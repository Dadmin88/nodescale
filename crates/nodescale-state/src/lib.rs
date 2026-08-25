//! Nodescale-owned SQLite durable state and transactional audit foundation.

use chrono::{DateTime, Utc};
use nodescale_domain::{
    AuditActor, AuditEventId, Device, DeviceGenerations, DeviceId, Generation, Invitation,
    JoinSession, JoinSessionId, JoinSessionState, MembershipState, Network, NetworkId,
    ProviderCredentialId, ProviderCredentialReference, ProviderInstanceId, ProviderKind,
    Revocation, RevocationState,
};
use nodescale_provider::{
    CompatibilityStatus, HeadscaleMutationAuthorization, HeadscaleMutationAuthorizationContext,
    MutationPolicyMode, PreAuthAssociationStrength, ProviderError, ProviderMutationCapability,
    ProviderNode, ReadOnlyProvider, ServerInspection,
};
use rusqlite::{Connection, ErrorCode, OptionalExtension, Transaction, params};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use sha2::{Digest, Sha256};
use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet},
    path::Path,
};
use thiserror::Error;

mod n5;
pub use n5::*;
mod n6;
pub use n6::*;
mod n7;
pub use n7::*;
#[cfg(test)]
mod n5_identity_trust_tests;

pub const SUPPORTED_SCHEMA_VERSION: u32 = 11;
pub const DEVICE_PAGE_MAX: usize = 32;
const INITIAL_MIGRATION: &str = include_str!("../migrations/0001_initial.sql");
const DISCOVERY_MIGRATION: &str = include_str!("../migrations/0002_discovery_reconciliation.sql");
const MUTATION_AUTHORIZATION_MIGRATION: &str =
    include_str!("../migrations/0003_mutation_authorization.sql");
const INVITATION_LIFECYCLE_MIGRATION: &str =
    include_str!("../migrations/0004_invitation_lifecycle.sql");
const DEVICE_TRUST_MIGRATION: &str = include_str!("../migrations/0005_device_trust.sql");
const KERYX_IDENTITY_BINDING_MIGRATION: &str =
    include_str!("../migrations/0006_keryx_identity_binding.sql");
const FLEET_PROJECTION_MIGRATION: &str = include_str!("../migrations/0007_fleet_projection.sql");
const EXISTING_DEVICE_ADOPTION_STATE_MIGRATION: &str =
    include_str!("../migrations/0008_existing_device_adoption_state.sql");
const TYPED_N5_PROVENANCE_MIGRATION: &str =
    include_str!("../migrations/0009_typed_n5_provenance.sql");
const EXISTING_PROVIDER_ADOPTION_ACTIVATION_MIGRATION: &str =
    include_str!("../migrations/0010_existing_provider_adoption_activation.sql");
const EXACT_PROVIDER_REVALIDATION_MIGRATION: &str =
    include_str!("../migrations/0011_exact_provider_revalidation.sql");

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Failpoint {
    BeforeAuditInsert,
    BeforeN4ConfirmationAudit,
    BeforeAdoptionExpiryCommit,
}

#[derive(Debug, Error)]
pub enum StateError {
    #[error("SQLite state error: {0}")]
    Sqlite(#[from] rusqlite::Error),
    #[error("serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    #[error("state conflict: {0}")]
    Conflict(String),
    #[error("stale generation: expected {expected}, actual {actual}")]
    StaleGeneration { expected: u64, actual: u64 },
    #[error("unsupported schema version {found}; maximum supported is {supported}")]
    UnsupportedSchema { found: u32, supported: u32 },
    #[error("audit metadata is unsafe: {0}")]
    UnsafeAuditMetadata(String),
    #[error("injected transaction failure")]
    InjectedFailure,
    #[error("trusted activation remains gated in N0C")]
    ActivationGated,
    #[error("record not found: {0}")]
    NotFound(String),
    #[error("mutation authorization denied: {0}")]
    MutationAuthorizationDenied(&'static str),
}

/// TLS verification deliberately has no insecure option in N2A imports.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TlsVerificationPolicy {
    Verify,
}

/// Persistable Headscale import configuration. The API key is deliberately not
/// accepted here; only an opaque secret reference may be stored.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct HeadscaleImportConfig {
    pub server_url: String,
    pub provider_instance_id: ProviderInstanceId,
    pub opaque_secret_reference: String,
    pub compatibility_pin: String,
    #[serde(default)]
    pub custom_root_ca_sha256: Option<String>,
    pub tls_verification: TlsVerificationPolicy,
    pub read_only: bool,
    pub mutation_allowed: bool,
}
impl HeadscaleImportConfig {
    pub fn new(
        server_url: impl Into<String>,
        provider_instance_id: ProviderInstanceId,
        opaque_secret_reference: impl Into<String>,
        compatibility_pin: impl Into<String>,
        tls_verification: TlsVerificationPolicy,
    ) -> Result<Self, StateError> {
        let server_url = server_url.into();
        let opaque_secret_reference = opaque_secret_reference.into();
        let compatibility_pin = compatibility_pin.into();
        let host = server_url.strip_prefix("https://").unwrap_or_default();
        if host.is_empty()
            || host.contains(['/', '@', '?', '#'])
            || server_url.chars().any(char::is_whitespace)
        {
            return Err(StateError::Conflict(
                "Headscale server URL must be a clean HTTPS origin".into(),
            ));
        }
        if !opaque_secret_reference.starts_with("secret://")
            || opaque_secret_reference.len() > 255
            || opaque_secret_reference.chars().any(char::is_whitespace)
        {
            return Err(StateError::Conflict(
                "credential must be an opaque secret:// reference, not plaintext".into(),
            ));
        }
        if compatibility_pin.is_empty()
            || compatibility_pin.len() > 64
            || compatibility_pin.chars().any(char::is_whitespace)
        {
            return Err(StateError::Conflict(
                "Headscale compatibility pin is invalid".into(),
            ));
        }
        Ok(Self {
            server_url,
            provider_instance_id,
            opaque_secret_reference,
            compatibility_pin,
            custom_root_ca_sha256: None,
            tls_verification,
            read_only: true,
            mutation_allowed: false,
        })
    }

    pub fn with_custom_root_ca_sha256(
        mut self,
        fingerprint: impl Into<String>,
    ) -> Result<Self, StateError> {
        let fingerprint = fingerprint.into();
        if fingerprint.len() != 71
            || !fingerprint.starts_with("sha256:")
            || !fingerprint[7..]
                .chars()
                .all(|character| character.is_ascii_hexdigit() && !character.is_ascii_uppercase())
        {
            return Err(StateError::Conflict(
                "custom root CA fingerprint must be canonical sha256".into(),
            ));
        }
        self.custom_root_ca_sha256 = Some(fingerprint);
        Ok(self)
    }

    fn validate_for_persistence(&self) -> Result<(), StateError> {
        Self::new(
            &self.server_url,
            self.provider_instance_id,
            &self.opaque_secret_reference,
            &self.compatibility_pin,
            self.tls_verification,
        )?;
        Ok(())
    }
}

/// Persistable Tailscale SaaS import configuration. The token is deliberately
/// excluded; only an opaque secret reference is durable.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct TailscaleImportConfig {
    pub tailnet: String,
    pub provider_instance_id: ProviderInstanceId,
    pub opaque_secret_reference: String,
    pub compatibility_pin: String,
    pub read_only: bool,
    pub mutation_allowed: bool,
}

impl TailscaleImportConfig {
    pub fn new(
        tailnet: impl Into<String>,
        provider_instance_id: ProviderInstanceId,
        opaque_secret_reference: impl Into<String>,
    ) -> Result<Self, StateError> {
        let tailnet = tailnet.into();
        let opaque_secret_reference = opaque_secret_reference.into();
        if tailnet.is_empty()
            || tailnet.len() > 256
            || tailnet.trim() != tailnet
            || !tailnet
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || b".-_@".contains(&byte))
        {
            return Err(StateError::Conflict("Tailscale tailnet is invalid".into()));
        }
        if !opaque_secret_reference.starts_with("secret://")
            || opaque_secret_reference.len() > 255
            || opaque_secret_reference.chars().any(char::is_whitespace)
        {
            return Err(StateError::Conflict(
                "credential must be an opaque secret:// reference, not plaintext".into(),
            ));
        }
        Ok(Self {
            tailnet,
            provider_instance_id,
            opaque_secret_reference,
            compatibility_pin: "api-v2".into(),
            read_only: true,
            mutation_allowed: false,
        })
    }

    fn scoped_api_url(&self) -> String {
        format!("https://api.tailscale.com/api/v2/tailnet/{}", self.tailnet)
    }
}

struct ReconciliationImportConfig {
    provider_instance_id: ProviderInstanceId,
    provider_name: &'static str,
    compatibility_pin: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ObservationClassification {
    ExpectedJoining,
    DiscoveredUnmanaged,
    Active,
    ProviderMissing,
    ProviderExpired,
    ProviderRemoved,
    IdentityConflict,
    Quarantined,
    Revoked,
}

/// Adoption is staging only. Even `PendingDeviceCredentialProof` cannot create
/// a trusted device, Keryx binding, Fleet projection, grant, or execution right.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AdoptionState {
    Unmanaged,
    PendingDeviceCredentialProof,
    Adopted,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ProviderObservation {
    pub network_id: NetworkId,
    pub device_id: Option<DeviceId>,
    pub provider_instance_id: ProviderInstanceId,
    pub canonical_provider_node_id: String,
    pub stable_machine_key_fingerprint: String,
    pub node: ProviderNode,
    pub classification: ObservationClassification,
    pub adoption_state: AdoptionState,
    pub semantic_fingerprint: String,
    pub semantic_generation: u64,
    pub first_observed_at: DateTime<Utc>,
    pub last_observed_at: DateTime<Utc>,
    pub snapshot_at: DateTime<Utc>,
}

/// Maximum number of durable observations returned by one read page.
///
/// This is deliberately fixed at the state boundary so every caller, including
/// local transports, has the same bounded current-state read contract.
pub const PROVIDER_OBSERVATION_PAGE_MAX: usize = 100;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ProviderReconciliationState {
    NeverReconciled,
    Healthy,
    Unreachable,
    AuthenticationFailed,
    Incompatible,
    Malformed,
    IdentityConflict,
    StateFailure,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ReconciliationReport {
    pub network_id: NetworkId,
    pub provider_state: ProviderReconciliationState,
    pub provider_compatibility: CompatibilityStatus,
    pub provider_version: String,
    pub last_attempted_reconciliation: Option<DateTime<Utc>>,
    pub last_successful_reconciliation: Option<DateTime<Utc>>,
    pub observed_count: u64,
    pub discovered_unmanaged_count: u64,
    pub provider_missing_count: u64,
    pub provider_expired_count: u64,
    pub identity_conflict_count: u64,
    pub quarantined_count: u64,
    pub active_trusted_count: u64,
    pub warnings: Vec<String>,
    pub provider_mutation_enabled: bool,
}

#[derive(Debug, Error)]
pub enum ReconciliationFailure {
    #[error("provider unreachable")]
    Unreachable,
    #[error("provider authentication failed")]
    AuthenticationFailed,
    #[error("provider is incompatible")]
    Incompatible,
    #[error("provider response is malformed")]
    Malformed,
    #[error("provider identity conflict")]
    IdentityConflict,
    #[error("state failure: {0}")]
    State(#[from] StateError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SanitizedMetadata(Value);
impl SanitizedMetadata {
    pub fn new(value: Value) -> Result<Self, StateError> {
        validate_metadata(&value)?;
        Ok(Self(value))
    }
    #[must_use]
    pub fn empty() -> Self {
        Self(Value::Object(Map::new()))
    }
    fn json(&self) -> Result<String, StateError> {
        Ok(serde_json::to_string(&self.0)?)
    }

    fn n4_digest_json(&self) -> Result<String, StateError> {
        if self.0.as_object().is_some_and(Map::is_empty) {
            return Ok("{}".into());
        }
        let canonical = serde_json::to_vec(&self.0)?;
        Ok(format!(
            "{{\"sha256\":\"{:x}\"}}",
            Sha256::digest(canonical)
        ))
    }
}
impl Default for SanitizedMetadata {
    fn default() -> Self {
        Self::empty()
    }
}

/// Exact N4 provider routing context, deliberately free of plaintext secrets.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct N4InvitationContext {
    pub provider_instance_id: ProviderInstanceId,
    pub provider_principal_id: String,
}
impl N4InvitationContext {
    pub fn new(
        provider_instance_id: ProviderInstanceId,
        provider_principal_id: impl Into<String>,
    ) -> Result<Self, StateError> {
        let provider_principal_id = provider_principal_id.into();
        if !safe_identifier(&provider_principal_id) {
            return Err(StateError::Conflict("invalid N4 provider principal".into()));
        }
        Ok(Self {
            provider_instance_id,
            provider_principal_id,
        })
    }
}

/// Redacted candidate used solely by the service's private Argon2 verification boundary.
#[derive(Eq, PartialEq)]
pub struct N4InvitationCandidate {
    pub invitation_id: nodescale_domain::InvitationId,
    pub network_id: NetworkId,
    pub revision: u64,
    pub state: nodescale_domain::InvitationState,
    pub expires_at: DateTime<Utc>,
    pub context: N4InvitationContext,
    verifier: nodescale_domain::SecretVerifier,
}
impl N4InvitationCandidate {
    pub fn verify(&self, token: &nodescale_domain::InvitationToken) -> Result<bool, StateError> {
        if token.invitation_id() != self.invitation_id {
            return Ok(false);
        }
        self.verifier.verify(token).map_err(|_| {
            StateError::Conflict("N4 invitation verifier could not be evaluated".into())
        })
    }
}
impl std::fmt::Debug for N4InvitationCandidate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("N4InvitationCandidate")
            .field("invitation_id", &self.invitation_id)
            .field("network_id", &self.network_id)
            .field("revision", &self.revision)
            .field("state", &self.state)
            .field("expires_at", &self.expires_at)
            .field("context", &self.context)
            .field("verifier", &"[REDACTED]")
            .finish()
    }
}

/// Sanitized lifecycle/reconciliation state suitable for public status views.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum N4CleanupState {
    Active,
    Pending,
    Confirmed,
    Retryable,
    Ambiguous,
    Blocked,
    None,
}

/// Public/list-safe N4 view: neither verifier nor provider-native credential reference is present.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct N4InvitationView {
    pub invitation_id: nodescale_domain::InvitationId,
    pub network_id: NetworkId,
    pub state: nodescale_domain::InvitationState,
    pub revision: u64,
    pub roles: nodescale_domain::Roles,
    pub join_constraints: nodescale_domain::JoinConstraints,
    pub created_at: DateTime<Utc>,
    pub expires_at: DateTime<Utc>,
    pub max_uses: u32,
    pub used_count: u32,
    pub consumed_at: Option<DateTime<Utc>>,
    pub revoked_at: Option<DateTime<Utc>>,
    pub expired_at: Option<DateTime<Utc>>,
    pub cleanup_state: N4CleanupState,
    pub context: N4InvitationContext,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct N4PresentedMetadata {
    pub platform: Option<String>,
    pub hostname_hint: Option<String>,
    pub correlation: SanitizedMetadata,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct N4RedemptionReservation {
    pub join_session_id: JoinSessionId,
    pub invitation_id: nodescale_domain::InvitationId,
    pub network_id: NetworkId,
    pub expires_at: DateTime<Utc>,
    pub context: N4InvitationContext,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct N4CredentialDispatch {
    pub join_session_id: JoinSessionId,
    pub invitation_id: nodescale_domain::InvitationId,
    pub network_id: NetworkId,
    pub context: N4InvitationContext,
    pub authorization_generation: Generation,
    pub configuration_generation: Generation,
    pub configuration_fingerprint: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct N4CredentialConfirmation {
    pub credential_id: ProviderCredentialId,
    pub provider_reference: ProviderCredentialReference,
    pub provider_principal_id: String,
    pub ephemeral: bool,
    pub approved_tags: Vec<String>,
    pub expires_at: DateTime<Utc>,
    pub confirmed_at: DateTime<Utc>,
    pub safe_correlation: SanitizedMetadata,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum N4DispatchFailure {
    PreDispatch,
    DefiniteNoApply,
    Ambiguous,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum N4InvalidationOutcome {
    Confirmed,
    AlreadySatisfied,
    Retryable,
    Ambiguous,
    AuthenticationFailed,
    CompatibilityBlocked,
    Blocked,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum N4CleanupIntent {
    Revoked,
    Expired,
}

/// Exact durable provider cleanup routing. Its `Debug` redacts the native reference.
#[derive(Clone, Eq, PartialEq)]
pub struct N4CleanupTarget {
    pub invitation_id: nodescale_domain::InvitationId,
    pub join_session_id: Option<JoinSessionId>,
    pub credential_id: Option<ProviderCredentialId>,
    pub provider_reference: Option<ProviderCredentialReference>,
    pub network_id: NetworkId,
    pub provider_instance_id: ProviderInstanceId,
    pub intent: N4CleanupIntent,
    pub cleanup_uncertain: bool,
}
impl std::fmt::Debug for N4CleanupTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("N4CleanupTarget")
            .field("invitation_id", &self.invitation_id)
            .field("join_session_id", &self.join_session_id)
            .field("credential_id", &self.credential_id)
            .field(
                "provider_reference",
                &self.provider_reference.as_ref().map(|_| "[REDACTED]"),
            )
            .field("network_id", &self.network_id)
            .field("provider_instance_id", &self.provider_instance_id)
            .field("intent", &self.intent)
            .field("cleanup_uncertain", &self.cleanup_uncertain)
            .finish()
    }
}

/// Imports remain permanently read-only and never imply authorization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProviderMutationConfiguration {
    provider_instance_id: ProviderInstanceId,
    authorization_generation: Generation,
    configuration_generation: Generation,
    configuration_fingerprint: String,
    adapter: String,
    expected_version: String,
    enabled: bool,
    revoked: bool,
    not_before: DateTime<Utc>,
    expires_at: DateTime<Utc>,
    policy_mode: MutationPolicyMode,
    capabilities: BTreeSet<ProviderMutationCapability>,
}
impl ProviderMutationConfiguration {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        provider_instance_id: ProviderInstanceId,
        authorization_generation: Generation,
        configuration_generation: Generation,
        configuration_fingerprint: impl Into<String>,
        adapter: impl Into<String>,
        expected_version: impl Into<String>,
        enabled: bool,
        revoked: bool,
        not_before: DateTime<Utc>,
        expires_at: DateTime<Utc>,
        policy_mode: MutationPolicyMode,
        capabilities: impl IntoIterator<Item = ProviderMutationCapability>,
    ) -> Result<Self, StateError> {
        let configuration_fingerprint = configuration_fingerprint.into();
        let adapter = adapter.into();
        let expected_version = expected_version.into();
        let capabilities = capabilities.into_iter().collect::<BTreeSet<_>>();
        if !valid_sha256_fingerprint(&configuration_fingerprint)
            || adapter != "headscale"
            || expected_version != "v0.29.3"
            || not_before >= expires_at
            || not_before.timestamp_millis() < 0
            || expires_at.timestamp_millis() < 0
            || capabilities.is_empty()
            || (capabilities.contains(&ProviderMutationCapability::ManagePolicy)
                && policy_mode != MutationPolicyMode::Database)
        {
            return Err(StateError::Conflict(
                "invalid provider mutation configuration".into(),
            ));
        }
        Ok(Self {
            provider_instance_id,
            authorization_generation,
            configuration_generation,
            configuration_fingerprint,
            adapter,
            expected_version,
            enabled,
            revoked,
            not_before,
            expires_at,
            policy_mode,
            capabilities,
        })
    }
}

/// Secret-free durable evidence that a provider credential creation was
/// confirmed. The plaintext join credential is intentionally absent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConfirmedProviderCredentialReference {
    pub credential_id: ProviderCredentialId,
    pub network_id: NetworkId,
    pub provider_instance_id: ProviderInstanceId,
    pub provider_reference: ProviderCredentialReference,
    pub authorization_generation: Generation,
    pub configuration_generation: Generation,
    pub configuration_fingerprint: String,
    pub confirmed_at: DateTime<Utc>,
    pub expires_at: DateTime<Utc>,
    pub max_uses: u32,
}
impl ConfirmedProviderCredentialReference {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        credential_id: ProviderCredentialId,
        network_id: NetworkId,
        provider_instance_id: ProviderInstanceId,
        provider_reference: ProviderCredentialReference,
        authorization_generation: Generation,
        configuration_generation: Generation,
        configuration_fingerprint: impl Into<String>,
        confirmed_at: DateTime<Utc>,
        expires_at: DateTime<Utc>,
        max_uses: u32,
    ) -> Result<Self, StateError> {
        let configuration_fingerprint = configuration_fingerprint.into();
        if !valid_sha256_fingerprint(&configuration_fingerprint)
            || confirmed_at.timestamp_millis() < 0
            || expires_at <= confirmed_at
            || max_uses != 1
        {
            return Err(StateError::Conflict(
                "invalid confirmed provider credential reference".into(),
            ));
        }
        Ok(Self {
            credential_id,
            network_id,
            provider_instance_id,
            provider_reference,
            authorization_generation,
            configuration_generation,
            configuration_fingerprint,
            confirmed_at,
            expires_at,
            max_uses,
        })
    }
}

/// State-owned single-use real-provider authorization. Its fields are private;
/// it deliberately has no constructor, Clone/Copy, or serde implementations.
#[derive(Debug)]
pub struct MutationAuthorization {
    network_id: NetworkId,
    provider_instance_id: ProviderInstanceId,
    authorization_generation: Generation,
    configuration_generation: Generation,
    configuration_fingerprint: String,
    adapter: String,
    expected_version: String,
    not_before: DateTime<Utc>,
    expires_at: DateTime<Utc>,
    capability: ProviderMutationCapability,
    policy_mode: MutationPolicyMode,
}

/// Runtime facts the Headscale adapter proves before any network request.
pub struct MutationAuthorizationContext {
    network_id: NetworkId,
    provider_instance_id: ProviderInstanceId,
    authorization_generation: Generation,
    configuration_generation: Generation,
    configuration_fingerprint: String,
    adapter: &'static str,
    version: String,
    dirty: bool,
    capability: ProviderMutationCapability,
    policy_mode: MutationPolicyMode,
    now: DateTime<Utc>,
}
impl MutationAuthorizationContext {
    #[allow(clippy::too_many_arguments)]
    #[must_use]
    pub fn headscale(
        network_id: NetworkId,
        provider_instance_id: ProviderInstanceId,
        authorization_generation: Generation,
        configuration_generation: Generation,
        configuration_fingerprint: impl Into<String>,
        version: impl Into<String>,
        dirty: bool,
        capability: ProviderMutationCapability,
        policy_mode: MutationPolicyMode,
        now: DateTime<Utc>,
    ) -> Self {
        Self {
            network_id,
            provider_instance_id,
            authorization_generation,
            configuration_generation,
            configuration_fingerprint: configuration_fingerprint.into(),
            adapter: "headscale",
            version: version.into(),
            dirty,
            capability,
            policy_mode,
            now,
        }
    }
}
impl MutationAuthorization {
    /// Consumes the token before adapter transport, preventing reuse.
    pub fn validate(self, context: MutationAuthorizationContext) -> Result<(), StateError> {
        if self.network_id != context.network_id
            || self.provider_instance_id != context.provider_instance_id
            || self.authorization_generation != context.authorization_generation
            || self.configuration_generation != context.configuration_generation
            || self.configuration_fingerprint != context.configuration_fingerprint
            || self.adapter != context.adapter
            || self.expected_version != context.version
            || context.dirty
            || self.capability != context.capability
            || (self.capability == ProviderMutationCapability::ManagePolicy
                && (self.policy_mode != MutationPolicyMode::Database
                    || context.policy_mode != MutationPolicyMode::Database))
            || context.now < self.not_before
            || context.now >= self.expires_at
        {
            return Err(StateError::MutationAuthorizationDenied(
                "authorization facts do not match",
            ));
        }
        Ok(())
    }
}

impl HeadscaleMutationAuthorization for MutationAuthorization {
    fn validate_for_headscale(
        self,
        context: HeadscaleMutationAuthorizationContext,
    ) -> Result<(), ProviderError> {
        self.validate(MutationAuthorizationContext::headscale(
            context.network_id,
            context.provider_instance_id,
            context.authorization_generation,
            context.configuration_generation,
            &context.configuration_fingerprint,
            &context.version,
            context.dirty,
            context.capability,
            context.policy_mode,
            context.now,
        ))
        .map_err(|error| ProviderError::Rejected(error.to_string()))
    }
}

pub struct StateStore {
    connection: RefCell<Connection>,
    fail_before_audit: Cell<bool>,
    fail_before_n4_confirmation_audit: Cell<bool>,
    fail_before_adoption_expiry_commit: Cell<bool>,
}

fn migration_query_digest(
    connection: &Connection,
    query: &str,
) -> Result<(u64, String), StateError> {
    let mut statement = connection.prepare(query)?;
    let column_count = statement.column_count();
    let mut rows = statement.query([])?;
    let mut row_count = 0_u64;
    let mut hasher = Sha256::new();
    while let Some(row) = rows.next()? {
        row_count += 1;
        for index in 0..column_count {
            use rusqlite::types::ValueRef;
            match row.get_ref(index)? {
                ValueRef::Null => hasher.update([0]),
                ValueRef::Integer(value) => {
                    hasher.update([1]);
                    hasher.update(value.to_be_bytes());
                }
                ValueRef::Real(value) => {
                    hasher.update([2]);
                    hasher.update(value.to_bits().to_be_bytes());
                }
                ValueRef::Text(value) => {
                    hasher.update([3]);
                    hasher.update((value.len() as u64).to_be_bytes());
                    hasher.update(value);
                }
                ValueRef::Blob(value) => {
                    hasher.update([4]);
                    hasher.update((value.len() as u64).to_be_bytes());
                    hasher.update(value);
                }
            }
        }
    }
    Ok((row_count, format!("{:x}", hasher.finalize())))
}

fn stage_columns(connection: &Connection, stage: &str) -> Result<Vec<String>, StateError> {
    let mut statement = connection.prepare(&format!("PRAGMA temp.table_info(\"{stage}\")"))?;
    let rows = statement.query_map([], |row| row.get::<_, String>(1))?;
    rows.collect::<Result<Vec<_>, _>>()
        .map_err(StateError::from)
}

fn verify_v9_migration_parity(connection: &Connection) -> Result<(), StateError> {
    for table in [
        "n5_device_identities",
        "n5_provider_bindings",
        "n6_binding_decisions",
        "n6_binding_records",
        "n6_binding_challenges",
        "n6_binding_authorizations",
        "n6_challenge_reservations",
    ] {
        let stage = format!("stage_{table}");
        let columns = stage_columns(connection, &stage)?;
        if columns.is_empty() {
            return Err(StateError::Conflict(format!(
                "V9 staging table {stage} is missing"
            )));
        }
        let old_projection = columns
            .iter()
            .map(|column| format!("s.\"{column}\""))
            .collect::<Vec<_>>()
            .join(",");
        let (joins, new_projection) = match table {
            "n5_device_identities" => (
                " JOIN n5_n4_identity_origins p ON p.origin_id=n.n4_origin_id AND p.device_id=n.device_id AND p.network_id=n.network_id",
                columns
                    .iter()
                    .map(|column| {
                        if column == "origin_join_session_id" {
                            "p.join_session_id AS origin_join_session_id".into()
                        } else {
                            format!("n.\"{column}\"")
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            "n5_provider_bindings" => (
                " JOIN n5_n4_provider_binding_provenance p ON p.binding_id=n.n4_provenance_binding_id AND p.device_id=n.device_id AND p.network_id=n.network_id",
                columns
                    .iter()
                    .map(|column| match column.as_str() {
                        "join_session_id" => "p.join_session_id AS join_session_id".into(),
                        "credential_id" => "p.credential_id AS credential_id".into(),
                        "provider_credential_reference" => {
                            "p.provider_credential_reference AS provider_credential_reference"
                                .into()
                        }
                        _ => format!("n.\"{column}\""),
                    })
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            "n6_binding_records" => (
                " JOIN n5_n4_provider_binding_provenance p ON p.binding_id=n.n5_provider_binding_id AND p.device_id=n.device_id AND p.network_id=n.network_id",
                columns
                    .iter()
                    .map(|column| {
                        if column == "join_session_id" {
                            "p.join_session_id AS join_session_id".into()
                        } else {
                            format!("n.\"{column}\"")
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            _ => (
                " JOIN n6_binding_records r ON r.binding_id=n.binding_id AND r.network_id=n.network_id AND r.device_id=n.device_id AND r.generation=n.generation JOIN n5_n4_provider_binding_provenance p ON p.binding_id=r.n5_provider_binding_id AND p.device_id=r.device_id AND p.network_id=r.network_id",
                columns
                    .iter()
                    .map(|column| {
                        if column == "join_session_id" {
                            "p.join_session_id AS join_session_id".into()
                        } else {
                            format!("n.\"{column}\"")
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(","),
            ),
        };
        let order = (1..=columns.len())
            .map(|index| index.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let old_query = format!("SELECT {old_projection} FROM temp.\"{stage}\" s ORDER BY {order}");
        let new_query =
            format!("SELECT {new_projection} FROM \"{table}\" n{joins} ORDER BY {order}");
        let old_digest = migration_query_digest(connection, &old_query)?;
        let new_digest = migration_query_digest(connection, &new_query)?;
        if old_digest != new_digest {
            return Err(StateError::Conflict(format!(
                "V9 semantic parity failed for {table}"
            )));
        }
    }
    Ok(())
}

const DROP_V9_STAGING: &str = "
DROP TABLE temp.stage_n6_challenge_reservations;
DROP TABLE temp.stage_n6_binding_authorizations;
DROP TABLE temp.stage_n6_binding_challenges;
DROP TABLE temp.stage_n6_binding_records;
DROP TABLE temp.stage_n6_binding_decisions;
DROP TABLE temp.stage_n5_provider_bindings;
DROP TABLE temp.stage_n5_device_identities;
";

impl StateStore {
    pub fn open(path: impl AsRef<Path>) -> Result<Self, StateError> {
        let connection = Connection::open(path)?;
        Self::initialize(connection)
    }

    pub fn open_in_memory() -> Result<Self, StateError> {
        Self::initialize(Connection::open_in_memory()?)
    }

    fn initialize(connection: Connection) -> Result<Self, StateError> {
        connection.pragma_update(None, "foreign_keys", true)?;
        connection.busy_timeout(std::time::Duration::from_secs(5))?;
        connection.execute_batch("BEGIN IMMEDIATE;")?;

        let migration_result = (|| -> Result<(), StateError> {
            let found =
                connection.pragma_query_value(None, "user_version", |row| row.get::<_, u32>(0))?;
            if found > SUPPORTED_SCHEMA_VERSION {
                return Err(StateError::UnsupportedSchema {
                    found,
                    supported: SUPPORTED_SCHEMA_VERSION,
                });
            }

            let migrations = [
                INITIAL_MIGRATION,
                DISCOVERY_MIGRATION,
                MUTATION_AUTHORIZATION_MIGRATION,
                INVITATION_LIFECYCLE_MIGRATION,
                DEVICE_TRUST_MIGRATION,
                KERYX_IDENTITY_BINDING_MIGRATION,
                FLEET_PROJECTION_MIGRATION,
                EXISTING_DEVICE_ADOPTION_STATE_MIGRATION,
                TYPED_N5_PROVENANCE_MIGRATION,
                EXISTING_PROVIDER_ADOPTION_ACTIVATION_MIGRATION,
                EXACT_PROVIDER_REVALIDATION_MIGRATION,
            ];
            for migration in migrations.iter().skip(found as usize) {
                connection.execute_batch(migration)?;
            }
            if found < 9 {
                verify_v9_migration_parity(&connection)?;
                connection.execute_batch(DROP_V9_STAGING)?;
            }

            let foreign_key_failures: u64 = connection.query_row(
                "SELECT COUNT(*) FROM pragma_foreign_key_check",
                [],
                |row| row.get(0),
            )?;
            if foreign_key_failures != 0 {
                return Err(StateError::Conflict(format!(
                    "migration left {foreign_key_failures} foreign-key violation(s)"
                )));
            }
            let integrity: String =
                connection.pragma_query_value(None, "integrity_check", |row| row.get(0))?;
            if integrity != "ok" {
                return Err(StateError::Conflict(format!(
                    "migration integrity check failed: {integrity}"
                )));
            }
            let staging_residue: u64 = connection.query_row(
                "SELECT COUNT(*) FROM sqlite_temp_master WHERE name LIKE 'stage_n5_%' OR name LIKE 'stage_n6_%'",
                [],
                |row| row.get(0),
            )?;
            if staging_residue != 0 {
                return Err(StateError::Conflict(format!(
                    "migration left {staging_residue} temporary staging object(s)"
                )));
            }
            connection.pragma_update(None, "user_version", SUPPORTED_SCHEMA_VERSION)?;
            Ok(())
        })();

        match migration_result {
            Ok(()) => connection.execute_batch("COMMIT;")?,
            Err(error) => {
                let _ = connection.execute_batch("ROLLBACK;");
                return Err(error);
            }
        }

        Ok(Self {
            connection: RefCell::new(connection),
            fail_before_audit: Cell::new(false),
            fail_before_n4_confirmation_audit: Cell::new(false),
            fail_before_adoption_expiry_commit: Cell::new(false),
        })
    }

    pub fn schema_version(&self) -> Result<u32, StateError> {
        Ok(self
            .connection
            .borrow()
            .pragma_query_value(None, "user_version", |row| row.get(0))?)
    }

    pub fn audit_event_count(&self) -> Result<u64, StateError> {
        Ok(self
            .connection
            .borrow()
            .query_row("SELECT COUNT(*) FROM audit_events", [], |row| row.get(0))?)
    }

    pub fn set_failpoint(&self, failpoint: Failpoint, enabled: bool) {
        match failpoint {
            Failpoint::BeforeAuditInsert => self.fail_before_audit.set(enabled),
            Failpoint::BeforeN4ConfirmationAudit => {
                self.fail_before_n4_confirmation_audit.set(enabled);
            }
            Failpoint::BeforeAdoptionExpiryCommit => {
                self.fail_before_adoption_expiry_commit.set(enabled);
            }
        }
    }

    pub fn create_network(&self, network: &Network, actor: AuditActor) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            let record = serde_json::to_string(network)?;
            tx.execute("INSERT INTO networks (network_id,name,state,provider_kind,provider_instance_id,membership_generation,policy_generation,record_json,created_at,updated_at) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10)", params![network.network_id.to_string(), network.name, lower(network.state.as_str()), format!("{:?}", network.provider_kind).to_lowercase(), network.provider_instance_id.to_string(), to_i64(network.membership_generation)?, to_i64(network.policy_generation)?, record, network.created_at.to_rfc3339(), network.updated_at.to_rfc3339()]).map_err(map_constraint)?;
            tx.execute("INSERT INTO membership_generations (network_id,generation,updated_at) VALUES (?1,?2,?3)", params![network.network_id.to_string(), to_i64(network.membership_generation)?, network.updated_at.to_rfc3339()]).map_err(map_constraint)?;
            store.append_audit(tx, Some(network.network_id), None, actor, "network.created", "success", Some(network.membership_generation), &SanitizedMetadata::empty())
        })
    }

    pub fn create_device(&self, device: &Device, actor: AuditActor) -> Result<(), StateError> {
        if matches!(
            device.membership_state,
            MembershipState::Active | MembershipState::Suspended
        ) {
            return Err(StateError::ActivationGated);
        }
        self.transactional(|tx, store| {
            let (provider_instance, provider_node, provider_key) = device.provider_identity.as_ref().map_or((None,None,None), |identity| (Some(identity.provider_instance_id.to_string()), Some(identity.node_id.to_string()), Some(identity.stable_key_fingerprint.clone())));
            tx.execute("INSERT INTO devices (device_id,network_id,display_name,membership_state,provider_instance_id,provider_node_id,provider_key_fingerprint,credential_generation,keryx_binding_generation,fleet_projection_generation,fleet_projection_status,record_json,created_at,updated_at,revoked_at) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10,?11,?12,?13,?14,?15)", params![device.device_id.to_string(), device.network_id.to_string(), device.display_name, lower(device.membership_state.as_str()), provider_instance, provider_node, provider_key, to_i64(device.generations.credential)?, to_i64(device.generations.keryx_binding)?, to_i64(device.generations.fleet_projection)?, lower(device.fleet_projection_status.as_str()), serde_json::to_string(device)?, device.created_at.to_rfc3339(), device.updated_at.to_rfc3339(), device.revoked_at.map(|value| value.to_rfc3339())]).map_err(map_constraint)?;
            tx.execute("INSERT INTO device_generations (device_id,credential_generation,keryx_binding_generation,fleet_projection_generation,updated_at) VALUES (?1,?2,?3,?4,?5)", params![device.device_id.to_string(), to_i64(device.generations.credential)?, to_i64(device.generations.keryx_binding)?, to_i64(device.generations.fleet_projection)?, device.updated_at.to_rfc3339()]).map_err(map_constraint)?;
            store.append_audit(tx, Some(device.network_id), Some(device.device_id), actor, "device.created", "success", Some(device.generations.credential), &SanitizedMetadata::empty())
        })
    }

    /// Issue a single-use N4 invitation only against an exact currently enabled
    /// mutation configuration with both create and invalidation capability.
    pub fn issue_n4_invitation(
        &self,
        invitation: &Invitation,
        context: N4InvitationContext,
        now: DateTime<Utc>,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        if invitation.validate_n4_issuance().is_err()
            || invitation.network_id != self.network(invitation.network_id)?.network_id
            || now < invitation.created_at
            || now >= invitation.expires_at
        {
            return Err(StateError::Conflict("invalid N4 invitation input".into()));
        }
        self.transactional(|tx, store| {
            let authorized: bool = tx.query_row(
                "SELECT EXISTS(SELECT 1 FROM provider_mutation_configurations c JOIN provider_imports i ON i.network_id=c.network_id AND i.provider_instance_id=c.provider_instance_id WHERE c.network_id=?1 AND c.provider_instance_id=?2 AND c.enabled=1 AND c.revoked=0 AND ?3>=c.not_before_ms AND ?3<c.expires_at_ms AND EXISTS (SELECT 1 FROM provider_mutation_capabilities p WHERE p.network_id=c.network_id AND p.provider_instance_id=c.provider_instance_id AND p.capability='CreateJoinCredential') AND EXISTS (SELECT 1 FROM provider_mutation_capabilities p WHERE p.network_id=c.network_id AND p.provider_instance_id=c.provider_instance_id AND p.capability='InvalidateJoinCredential'))",
                params![invitation.network_id.to_string(), context.provider_instance_id.to_string(), now.timestamp_millis()],
                |row| row.get(0),
            )?;
            if !authorized { return Err(StateError::MutationAuthorizationDenied("N4 requires exact enabled create/invalidate configuration")); }
            tx.execute("INSERT INTO invitations (invitation_id,network_id,state,secret_verifier,provider_credential_reference,max_uses,used_count,record_json,created_at,expires_at) VALUES (?1,?2,?3,?4,NULL,1,0,?5,?6,?7)", params![invitation.invitation_id.to_string(), invitation.network_id.to_string(), lower(invitation.state.as_str()), invitation.secret_verifier.as_str(), serde_json::to_string(invitation)?, invitation.created_at.to_rfc3339(), invitation.expires_at.to_rfc3339()]).map_err(map_constraint)?;
            tx.execute("INSERT INTO n4_invitation_details (invitation_id,network_id,provider_instance_id,provider_principal_id,roles_json,constraints_json,created_by_source,created_by_id,revision,last_redemption_metadata_json) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,1,'{}')", params![invitation.invitation_id.to_string(), invitation.network_id.to_string(), context.provider_instance_id.to_string(), context.provider_principal_id, serde_json::to_string(&invitation.roles)?, serde_json::to_string(&invitation.join_constraints)?, actor.source, actor.actor_id])?;
            store.append_n4_audit(tx, invitation.invitation_id, None, &format!("invitation:{}:created", invitation.invitation_id), actor, "invitation_created", "success", &SanitizedMetadata::empty())?;
            Ok(())
        })
    }

    /// Return a N4-only candidate. Legacy invitations intentionally have no
    /// extension row and fail closed instead of becoming redeemable by upgrade.
    pub fn n4_invitation_candidate(
        &self,
        invitation_id: nodescale_domain::InvitationId,
    ) -> Result<N4InvitationCandidate, StateError> {
        let row = self.connection.borrow().query_row(
            "SELECT i.record_json,d.revision,d.provider_instance_id,d.provider_principal_id FROM invitations i JOIN n4_invitation_details d ON d.invitation_id=i.invitation_id WHERE i.invitation_id=?1",
            [invitation_id.to_string()],
            |row| Ok((row.get::<_, String>(0)?, row.get::<_, u64>(1)?, row.get::<_, String>(2)?, row.get::<_, String>(3)?)),
        ).optional()?.ok_or_else(|| StateError::NotFound(invitation_id.to_string()))?;
        let invitation: Invitation = serde_json::from_str(&row.0)?;
        Ok(N4InvitationCandidate {
            invitation_id,
            network_id: invitation.network_id,
            revision: row.1,
            state: invitation.state,
            expires_at: invitation.expires_at,
            context: N4InvitationContext::new(
                ProviderInstanceId::parse(&row.2)
                    .map_err(|error| StateError::Conflict(error.to_string()))?,
                row.3,
            )?,
            verifier: invitation.secret_verifier,
        })
    }

    pub fn n4_invitation_view(
        &self,
        invitation_id: nodescale_domain::InvitationId,
    ) -> Result<N4InvitationView, StateError> {
        self.n4_view_row(&self.connection.borrow(), invitation_id)
    }

    /// Deterministic N4-only listing; legacy invitation rows have no extension and are excluded.
    pub fn list_n4_invitations(
        &self,
        network_id: NetworkId,
    ) -> Result<Vec<N4InvitationView>, StateError> {
        let connection = self.connection.borrow();
        let mut statement = connection.prepare(
            "SELECT d.invitation_id FROM n4_invitation_details d JOIN invitations i ON i.invitation_id=d.invitation_id WHERE d.network_id=?1 ORDER BY i.created_at, d.invitation_id",
        )?;
        let ids = statement
            .query_map([network_id.to_string()], |row| row.get::<_, String>(0))?
            .collect::<Result<Vec<_>, _>>()?;
        ids.into_iter()
            .map(|id| {
                self.n4_view_row(
                    &connection,
                    nodescale_domain::InvitationId::parse(&id)
                        .map_err(|error| StateError::Conflict(error.to_string()))?,
                )
            })
            .collect()
    }

    fn n4_view_row(
        &self,
        connection: &Connection,
        invitation_id: nodescale_domain::InvitationId,
    ) -> Result<N4InvitationView, StateError> {
        let row = connection.query_row(
            "SELECT i.record_json,i.used_count,d.revision,d.provider_instance_id,d.provider_principal_id,d.consumed_at_ms,d.revoked_at_ms,d.expired_at_ms,COALESCE(m.invalidation_state,'none') FROM invitations i JOIN n4_invitation_details d ON d.invitation_id=i.invitation_id LEFT JOIN n4_join_session_dispatches x ON x.invitation_id=i.invitation_id LEFT JOIN n4_provider_credential_metadata m ON m.join_session_id=x.join_session_id WHERE i.invitation_id=?1",
            [invitation_id.to_string()],
            |r| Ok((r.get::<_, String>(0)?, r.get::<_, u32>(1)?, r.get::<_, u64>(2)?, r.get::<_, String>(3)?, r.get::<_, String>(4)?, r.get::<_, Option<i64>>(5)?, r.get::<_, Option<i64>>(6)?, r.get::<_, Option<i64>>(7)?, r.get::<_, String>(8)?)),
        ).optional()?.ok_or_else(|| StateError::NotFound(invitation_id.to_string()))?;
        let invitation: Invitation = serde_json::from_str(&row.0)?;
        let parse_time = |value: Option<i64>| {
            value
                .and_then(DateTime::from_timestamp_millis)
                .ok_or_else(|| StateError::Conflict("invalid persisted N4 timestamp".into()))
        };
        let cleanup_state = match row.8.as_str() {
            "active" => N4CleanupState::Active,
            "pending" => N4CleanupState::Pending,
            "confirmed" => N4CleanupState::Confirmed,
            "retryable" => N4CleanupState::Retryable,
            "ambiguous" => N4CleanupState::Ambiguous,
            "blocked" => N4CleanupState::Blocked,
            "none" => N4CleanupState::None,
            _ => return Err(StateError::Conflict("invalid N4 cleanup state".into())),
        };
        Ok(N4InvitationView {
            invitation_id,
            network_id: invitation.network_id,
            state: invitation.state,
            revision: row.2,
            roles: invitation.roles,
            join_constraints: invitation.join_constraints,
            created_at: invitation.created_at,
            expires_at: invitation.expires_at,
            max_uses: invitation.max_uses,
            used_count: row.1,
            consumed_at: match row.5 {
                Some(value) => Some(parse_time(Some(value))?),
                None => None,
            },
            revoked_at: match row.6 {
                Some(value) => Some(parse_time(Some(value))?),
                None => None,
            },
            expired_at: match row.7 {
                Some(value) => Some(parse_time(Some(value))?),
                None => None,
            },
            cleanup_state,
            context: N4InvitationContext::new(
                ProviderInstanceId::parse(&row.3)
                    .map_err(|error| StateError::Conflict(error.to_string()))?,
                row.4,
            )?,
        })
    }

    pub fn prepare_n4_revocation(
        &self,
        invitation_id: nodescale_domain::InvitationId,
        now: DateTime<Utc>,
        actor: AuditActor,
    ) -> Result<N4CleanupTarget, StateError> {
        self.prepare_n4_cleanup(invitation_id, now, actor, N4CleanupIntent::Revoked)
    }

    pub fn prepare_n4_expiry(
        &self,
        invitation_id: nodescale_domain::InvitationId,
        now: DateTime<Utc>,
        actor: AuditActor,
    ) -> Result<N4CleanupTarget, StateError> {
        self.prepare_n4_cleanup(invitation_id, now, actor, N4CleanupIntent::Expired)
    }

    pub fn expired_n4_invitation_ids(
        &self,
        now: DateTime<Utc>,
    ) -> Result<Vec<nodescale_domain::InvitationId>, StateError> {
        let connection = self.connection.borrow();
        let mut statement = connection.prepare("SELECT i.invitation_id FROM invitations i JOIN n4_invitation_details d ON d.invitation_id=i.invitation_id WHERE i.expires_at<=?1 AND i.state NOT IN ('expired','revoked') ORDER BY i.invitation_id")?;
        statement
            .query_map([now.to_rfc3339()], |row| row.get::<_, String>(0))?
            .map(|id| {
                nodescale_domain::InvitationId::parse(&id?)
                    .map_err(|error| StateError::Conflict(error.to_string()))
            })
            .collect()
    }

    fn prepare_n4_cleanup(
        &self,
        invitation_id: nodescale_domain::InvitationId,
        now: DateTime<Utc>,
        actor: AuditActor,
        intent: N4CleanupIntent,
    ) -> Result<N4CleanupTarget, StateError> {
        self.transactional(|tx, store| {
            let row = tx.query_row("SELECT i.record_json,d.provider_instance_id,x.join_session_id,x.credential_id,x.dispatch_state,r.provider_reference FROM invitations i JOIN n4_invitation_details d ON d.invitation_id=i.invitation_id LEFT JOIN n4_join_session_dispatches x ON x.invitation_id=i.invitation_id LEFT JOIN confirmed_provider_credential_references r ON r.credential_id=x.credential_id WHERE i.invitation_id=?1", [invitation_id.to_string()], |r| Ok((r.get::<_, String>(0)?,r.get::<_, String>(1)?,r.get::<_, Option<String>>(2)?,r.get::<_, Option<String>>(3)?,r.get::<_, Option<String>>(4)?,r.get::<_, Option<String>>(5)?))).optional()?.ok_or_else(|| StateError::NotFound(invitation_id.to_string()))?;
            let (record, instance, session_id, credential_id, dispatch_state, provider_reference) = row;
            let mut invitation: Invitation = serde_json::from_str(&record)?;
            if intent == N4CleanupIntent::Expired && now < invitation.expires_at {
                return Err(StateError::Conflict(
                    "N4 invitation has not reached its expiry deadline".into(),
                ));
            }
            let instance = ProviderInstanceId::parse(&instance).map_err(|e| StateError::Conflict(e.to_string()))?;
            let session_id = session_id.map(|value| JoinSessionId::parse(&value).map_err(|e| StateError::Conflict(e.to_string()))).transpose()?;
            let credential_id = credential_id.map(|value| ProviderCredentialId::parse(&value).map_err(|e| StateError::Conflict(e.to_string()))).transpose()?;
            let reference = provider_reference.map(ProviderCredentialReference::new).transpose().map_err(|e| StateError::Conflict(e.to_string()))?;
            let cleanup_uncertain = reference.is_none() && session_id.is_some();
            let target = N4CleanupTarget { invitation_id, join_session_id: session_id, credential_id, provider_reference: reference, network_id: invitation.network_id, provider_instance_id: instance, intent, cleanup_uncertain };
            let terminal = matches!(invitation.state, nodescale_domain::InvitationState::Revoked | nodescale_domain::InvitationState::Expired);
            if terminal || (matches!(dispatch_state.as_deref(), Some("revocation_pending"))
                && !(intent == N4CleanupIntent::Expired
                    && target.provider_reference.is_none()
                    && now >= invitation.expires_at)) {
                return Ok(target);
            }
            if target.provider_reference.is_none() && session_id.is_some() && matches!(dispatch_state.as_deref(), Some("dispatch_started") | Some("ambiguous")) && !(intent == N4CleanupIntent::Expired && now >= invitation.expires_at) {
                let pending_state = match intent { N4CleanupIntent::Revoked => nodescale_domain::InvitationState::Revoking, N4CleanupIntent::Expired => nodescale_domain::InvitationState::Expiring };
                invitation.state = invitation.state.transition(pending_state).map_err(|e| StateError::Conflict(e.to_string()))?;
                tx.execute("UPDATE invitations SET state=?2,record_json=?3 WHERE invitation_id=?1", params![invitation_id.to_string(), lower(invitation.state.as_str()), serde_json::to_string(&invitation)?])?;
                tx.execute("UPDATE n4_join_session_dispatches SET dispatch_state='revocation_pending' WHERE invitation_id=?1 AND dispatch_state IN ('dispatch_started','ambiguous')", [invitation_id.to_string()])?;
                let Some(pending_session_id) = session_id else { return Err(StateError::Conflict("N4 cleanup session is absent".into())); };
                let session_record: String = tx.query_row("SELECT record_json FROM join_sessions WHERE join_session_id=?1", [pending_session_id.to_string()], |r| r.get(0))?;
                let mut session: JoinSession = serde_json::from_str(&session_record)?;
                session.advance_n4(JoinSessionState::ProviderCredentialRevocationPending, now).map_err(|e| StateError::Conflict(e.to_string()))?;
                tx.execute("UPDATE join_sessions SET state=?2,record_json=?3,updated_at=?4 WHERE join_session_id=?1", params![session.join_session_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, now.to_rfc3339()])?;
                return Ok(target);
            }
            if target.provider_reference.is_some() && matches!(dispatch_state.as_deref(), Some("confirmed")) {
                let pending_state = match intent { N4CleanupIntent::Revoked => nodescale_domain::InvitationState::Revoking, N4CleanupIntent::Expired => nodescale_domain::InvitationState::Expiring };
                invitation.state = invitation.state.transition(pending_state).map_err(|e| StateError::Conflict(e.to_string()))?;
                tx.execute("UPDATE invitations SET state=?2,record_json=?3 WHERE invitation_id=?1", params![invitation_id.to_string(), lower(invitation.state.as_str()), serde_json::to_string(&invitation)?])?;
                let next = match intent { N4CleanupIntent::Revoked => "revocation_pending", N4CleanupIntent::Expired => "revocation_pending" };
                tx.execute("UPDATE n4_join_session_dispatches SET dispatch_state=?2 WHERE invitation_id=?1 AND dispatch_state='confirmed'", params![invitation_id.to_string(), next])?;
                tx.execute("UPDATE n4_provider_credential_metadata SET invalidation_state='pending' WHERE credential_id=?1", [credential_id.expect("confirmed has credential").to_string()])?;
                let session_record: String = tx.query_row("SELECT record_json FROM join_sessions WHERE join_session_id=?1", [session_id.expect("confirmed has session").to_string()], |r| r.get(0))?;
                let mut session: JoinSession = serde_json::from_str(&session_record)?;
                session.advance_n4(JoinSessionState::ProviderCredentialRevocationPending, now).map_err(|e| StateError::Conflict(e.to_string()))?;
                tx.execute("UPDATE join_sessions SET state=?2,record_json=?3,updated_at=?4 WHERE join_session_id=?1", params![session.join_session_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, now.to_rfc3339()])?;
                return Ok(target);
            }
            let intermediate = match intent { N4CleanupIntent::Revoked => nodescale_domain::InvitationState::Revoking, N4CleanupIntent::Expired => nodescale_domain::InvitationState::Expiring };
            let next = match intent { N4CleanupIntent::Revoked => nodescale_domain::InvitationState::Revoked, N4CleanupIntent::Expired => nodescale_domain::InvitationState::Expired };
            if intent == N4CleanupIntent::Expired
                && invitation.state == nodescale_domain::InvitationState::Revoking
            {
                // Expiry is the authoritative terminal reason once its deadline
                // is reached, even when an earlier no-reference revoke left a
                // local-only cleanup pending. The generic domain graph cannot
                // express the cross-intent pending-to-expired recovery edge.
                invitation.state = nodescale_domain::InvitationState::Expired;
            } else {
                if invitation.state != intermediate {
                    invitation.state = invitation
                        .state
                        .transition(intermediate)
                        .map_err(|e| StateError::Conflict(e.to_string()))?;
                }
                invitation.state = invitation
                    .state
                    .transition(next)
                    .map_err(|e| StateError::Conflict(e.to_string()))?;
            }
            tx.execute("UPDATE invitations SET state=?2,record_json=?3 WHERE invitation_id=?1", params![invitation_id.to_string(), lower(invitation.state.as_str()), serde_json::to_string(&invitation)?])?;
            if let Some(session_id) = session_id {
                let session_record: String = tx.query_row("SELECT record_json FROM join_sessions WHERE join_session_id=?1", [session_id.to_string()], |r| r.get(0))?;
                let mut session: JoinSession = serde_json::from_str(&session_record)?;
                let terminal_session = match intent { N4CleanupIntent::Revoked => JoinSessionState::Revoked, N4CleanupIntent::Expired => JoinSessionState::Expired };
                if session.state != terminal_session && session.state != JoinSessionState::Failed {
                    session.advance_n4(terminal_session, now).map_err(|e| StateError::Conflict(e.to_string()))?;
                    tx.execute("UPDATE join_sessions SET state=?2,record_json=?3,updated_at=?4 WHERE join_session_id=?1", params![session.join_session_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, now.to_rfc3339()])?;
                }
            }
            if dispatch_state.is_some() {
                let terminal_dispatch = match intent { N4CleanupIntent::Revoked => "revoked", N4CleanupIntent::Expired => "expired" };
                tx.execute("UPDATE n4_join_session_dispatches SET dispatch_state=?2,resolved_at_ms=COALESCE(resolved_at_ms,?3) WHERE invitation_id=?1 AND dispatch_state IN ('reserved','failed_pre_dispatch','failed_no_apply','revocation_pending')", params![invitation_id.to_string(), terminal_dispatch, now.timestamp_millis()])?;
            }
            tx.execute(match intent { N4CleanupIntent::Revoked => "UPDATE n4_invitation_details SET revoked_at_ms=?2,revision=revision+1 WHERE invitation_id=?1", N4CleanupIntent::Expired => "UPDATE n4_invitation_details SET expired_at_ms=?2,revision=revision+1 WHERE invitation_id=?1" }, params![invitation_id.to_string(), now.timestamp_millis()])?;
            store.append_n4_audit(tx, invitation_id, None, &format!("invitation:{invitation_id}:{intent:?}"), actor, match intent { N4CleanupIntent::Revoked => "invitation_revoked", N4CleanupIntent::Expired => "invitation_expired" }, "success", &SanitizedMetadata::empty())?;
            Ok(target)
        })
    }

    pub fn settle_n4_credential_invalidation(
        &self,
        target: N4CleanupTarget,
        outcome: N4InvalidationOutcome,
        now: DateTime<Utc>,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            let (session_id, credential_id, network, instance, reference, dispatch_state, invitation_record): (String, String, String, String, String, String, String) = tx.query_row(
                "SELECT d.join_session_id,d.credential_id,d.network_id,d.provider_instance_id,r.provider_reference,d.dispatch_state,i.record_json FROM n4_join_session_dispatches d JOIN confirmed_provider_credential_references r ON r.credential_id=d.credential_id JOIN invitations i ON i.invitation_id=d.invitation_id WHERE d.invitation_id=?1",
                [target.invitation_id.to_string()],
                |r| Ok((r.get(0)?,r.get(1)?,r.get(2)?,r.get(3)?,r.get(4)?,r.get(5)?,r.get(6)?)),
            ).optional()?.ok_or_else(|| StateError::Conflict("N4 invalidation target has no exact durable credential".into()))?;
            if target.join_session_id.map(|id| id.to_string()).as_deref() != Some(&session_id)
                || target.credential_id.map(|id| id.to_string()).as_deref() != Some(&credential_id)
                || target.provider_reference.as_ref().map(ProviderCredentialReference::as_str) != Some(reference.as_str())
                || target.network_id.to_string() != network || target.provider_instance_id.to_string() != instance {
                return Err(StateError::Conflict("N4 invalidation target does not exactly match durable provenance".into()));
            }
            match outcome {
                N4InvalidationOutcome::Confirmed | N4InvalidationOutcome::AlreadySatisfied => {
                    let terminal_dispatch = match target.intent { N4CleanupIntent::Revoked => "revoked", N4CleanupIntent::Expired => "expired" };
                    if matches!(dispatch_state.as_str(), "revoked" | "expired") {
                        if dispatch_state == terminal_dispatch {
                            return Ok(());
                        }
                        return Err(StateError::Conflict("N4 terminal invalidation intent conflicts with durable dispatch".into()));
                    }
                    if dispatch_state != "revocation_pending" { return Err(StateError::Conflict("N4 invalidation is not pending".into())); }
                    let metadata_changed = tx.execute("UPDATE n4_provider_credential_metadata SET invalidation_state='confirmed',invalidated_at_ms=?2 WHERE credential_id=?1 AND invalidation_state IN ('pending','retryable','ambiguous','blocked')", params![credential_id, now.timestamp_millis()])?;
                    if metadata_changed != 1 { return Err(StateError::Conflict("N4 invalidation metadata did not settle exactly once".into())); }
                    tx.execute("UPDATE n4_join_session_dispatches SET dispatch_state=?2,resolved_at_ms=COALESCE(resolved_at_ms,?3) WHERE invitation_id=?1 AND dispatch_state='revocation_pending'", params![target.invitation_id.to_string(), terminal_dispatch, now.timestamp_millis()])?;
                    let mut invitation: Invitation = serde_json::from_str(&invitation_record)?;
                    let invitation_terminal = match target.intent { N4CleanupIntent::Revoked => nodescale_domain::InvitationState::Revoked, N4CleanupIntent::Expired => nodescale_domain::InvitationState::Expired };
                    invitation.state = invitation.state.transition(invitation_terminal).map_err(|e| StateError::Conflict(e.to_string()))?;
                    tx.execute("UPDATE invitations SET state=?2,record_json=?3 WHERE invitation_id=?1", params![target.invitation_id.to_string(), lower(invitation.state.as_str()), serde_json::to_string(&invitation)?])?;
                    tx.execute(match target.intent { N4CleanupIntent::Revoked => "UPDATE n4_invitation_details SET revoked_at_ms=?2,revision=revision+1 WHERE invitation_id=?1", N4CleanupIntent::Expired => "UPDATE n4_invitation_details SET expired_at_ms=?2,revision=revision+1 WHERE invitation_id=?1" }, params![target.invitation_id.to_string(), now.timestamp_millis()])?;
                    let session_record: String = tx.query_row("SELECT record_json FROM join_sessions WHERE join_session_id=?1", [session_id], |r| r.get(0))?;
                    let mut session: JoinSession = serde_json::from_str(&session_record)?;
                    session.advance_n4(match target.intent { N4CleanupIntent::Revoked => JoinSessionState::Revoked, N4CleanupIntent::Expired => JoinSessionState::Expired }, now).map_err(|e| StateError::Conflict(e.to_string()))?;
                    tx.execute("UPDATE join_sessions SET state=?2,record_json=?3,updated_at=?4 WHERE join_session_id=?1", params![session.join_session_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, now.to_rfc3339()])?;
                    let action = format!("credential-invalidation:{}:{:?}", credential_id, target.intent);
                    store.append_n4_audit(tx, target.invitation_id, target.join_session_id, &action, actor.clone(), "provider_join_credential_invalidated", "success", &SanitizedMetadata::empty())?;
                    store.append_n4_audit(tx, target.invitation_id, target.join_session_id, &action, actor, match target.intent { N4CleanupIntent::Revoked => "invitation_revoked", N4CleanupIntent::Expired => "invitation_expired" }, "success", &SanitizedMetadata::empty())?;
                }
                N4InvalidationOutcome::Retryable | N4InvalidationOutcome::Ambiguous | N4InvalidationOutcome::AuthenticationFailed | N4InvalidationOutcome::CompatibilityBlocked | N4InvalidationOutcome::Blocked => {
                    let state = match outcome { N4InvalidationOutcome::Retryable => "retryable", N4InvalidationOutcome::Ambiguous => "ambiguous", N4InvalidationOutcome::AuthenticationFailed | N4InvalidationOutcome::CompatibilityBlocked | N4InvalidationOutcome::Blocked => "blocked", _ => unreachable!() };
                    tx.execute("UPDATE n4_provider_credential_metadata SET invalidation_state=?2 WHERE credential_id=?1 AND invalidation_state IN ('pending','retryable','ambiguous','blocked')", params![credential_id, state])?;
                }
            }
            Ok(())
        })
    }

    pub fn reserve_n4_redemption(
        &self,
        invitation_id: nodescale_domain::InvitationId,
        expected_revision: u64,
        join_session_id: JoinSessionId,
        now: DateTime<Utc>,
        presented: N4PresentedMetadata,
        actor: AuditActor,
    ) -> Result<N4RedemptionReservation, StateError> {
        self.transactional(|tx, store| {
            let (record, revision, instance, principal): (String, u64, String, String) = tx.query_row("SELECT i.record_json,d.revision,d.provider_instance_id,d.provider_principal_id FROM invitations i JOIN n4_invitation_details d ON d.invitation_id=i.invitation_id WHERE i.invitation_id=?1", [invitation_id.to_string()], |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?))).optional()?.ok_or_else(|| StateError::NotFound(invitation_id.to_string()))?;
            let mut invitation: Invitation = serde_json::from_str(&record)?;
            let context = N4InvitationContext::new(ProviderInstanceId::parse(&instance).map_err(|e| StateError::Conflict(e.to_string()))?, principal)?;
            if revision != expected_revision || invitation.state != nodescale_domain::InvitationState::Issued || invitation.used_count != 0 || invitation.max_uses != 1 || now >= invitation.expires_at || invitation.join_constraints.expected_platform().is_some_and(|v| presented.platform.as_deref() != Some(v)) || invitation.join_constraints.expected_hostname_hint().is_some_and(|v| presented.hostname_hint.as_deref() != Some(v)) { return Err(StateError::Conflict("N4 invitation is not reservable".into())); }
            let current: bool = tx.query_row("SELECT EXISTS(SELECT 1 FROM provider_mutation_configurations c WHERE c.network_id=?1 AND c.provider_instance_id=?2 AND c.enabled=1 AND c.revoked=0 AND ?3>=c.not_before_ms AND ?3<c.expires_at_ms AND EXISTS(SELECT 1 FROM provider_mutation_capabilities p WHERE p.network_id=c.network_id AND p.provider_instance_id=c.provider_instance_id AND p.capability='CreateJoinCredential') AND EXISTS(SELECT 1 FROM provider_mutation_capabilities p WHERE p.network_id=c.network_id AND p.provider_instance_id=c.provider_instance_id AND p.capability='InvalidateJoinCredential'))", params![invitation.network_id.to_string(), instance, now.timestamp_millis()], |r| r.get(0))?;
            if !current { return Err(StateError::MutationAuthorizationDenied("N4 provider configuration unavailable")); }
            invitation.state = nodescale_domain::InvitationState::Redeeming; invitation.used_count = 1;
            if tx.execute("UPDATE invitations SET state='redeeming',used_count=1,record_json=?2 WHERE invitation_id=?1 AND state='issued' AND used_count=0", params![invitation_id.to_string(), serde_json::to_string(&invitation)?])? != 1 { return Err(StateError::Conflict("N4 reservation lost".into())); }
            let mut session = JoinSession::new_n4(join_session_id, invitation_id, invitation.network_id, now, invitation.expires_at).map_err(|e| StateError::Conflict(e.to_string()))?; session.advance_n4(JoinSessionState::InvitationValidated, now).map_err(|e| StateError::Conflict(e.to_string()))?;
            tx.execute("INSERT INTO join_sessions (join_session_id,invitation_id,network_id,device_id,state,record_json,created_at,expires_at,updated_at) VALUES (?1,?2,?3,NULL,?4,?5,?6,?7,?6)", params![join_session_id.to_string(), invitation_id.to_string(), invitation.network_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, now.to_rfc3339(), invitation.expires_at.to_rfc3339()])?;
            tx.execute("INSERT INTO n4_join_session_dispatches (join_session_id,invitation_id,network_id,provider_instance_id,provider_principal_id,create_request_id,dispatch_state) VALUES (?1,?2,?3,?4,?5,?6,'reserved')", params![join_session_id.to_string(), invitation_id.to_string(), invitation.network_id.to_string(), context.provider_instance_id.to_string(), context.provider_principal_id, uuid::Uuid::new_v4().to_string()])?;
            tx.execute("UPDATE n4_invitation_details SET revision=revision+1,last_redemption_at_ms=?2,last_redemption_metadata_json=?3 WHERE invitation_id=?1 AND revision=?4", params![invitation_id.to_string(), now.timestamp_millis(), presented.correlation.n4_digest_json()?, i64::try_from(expected_revision).map_err(|_| StateError::Conflict("revision overflow".into()))?])?;
            let action_id = format!("redemption:{join_session_id}");
            store.append_n4_audit(tx, invitation_id, Some(join_session_id), &action_id, actor.clone(), "invitation_redemption_started", "success", &SanitizedMetadata::empty())?;
            store.append_n4_audit(tx, invitation_id, Some(join_session_id), &action_id, actor, "join_session_created", "success", &SanitizedMetadata::empty())?;
            Ok(N4RedemptionReservation { join_session_id, invitation_id, network_id: invitation.network_id, expires_at: invitation.expires_at, context })
        })
    }

    pub fn begin_n4_credential_dispatch(
        &self,
        join_session_id: JoinSessionId,
        now: DateTime<Utc>,
        _actor: AuditActor,
    ) -> Result<N4CredentialDispatch, StateError> {
        self.transactional(|tx, _| {
            let (record, invitation_id, network, instance, principal, state): (String,String,String,String,String,String) = tx.query_row("SELECT s.record_json,d.invitation_id,d.network_id,d.provider_instance_id,d.provider_principal_id,d.dispatch_state FROM n4_join_session_dispatches d JOIN join_sessions s ON s.join_session_id=d.join_session_id WHERE d.join_session_id=?1", [join_session_id.to_string()], |r| Ok((r.get(0)?,r.get(1)?,r.get(2)?,r.get(3)?,r.get(4)?,r.get(5)?))).optional()?.ok_or_else(|| StateError::NotFound(join_session_id.to_string()))?;
            if state != "reserved" { return Err(StateError::Conflict("N4 dispatch already fenced".into())); }
            let (auth, config, fingerprint): (u64,u64,String) = tx.query_row("SELECT authorization_generation,configuration_generation,configuration_fingerprint FROM provider_mutation_configurations c WHERE c.network_id=?1 AND c.provider_instance_id=?2 AND c.enabled=1 AND c.revoked=0 AND ?3>=c.not_before_ms AND ?3<c.expires_at_ms AND EXISTS(SELECT 1 FROM provider_mutation_capabilities p WHERE p.network_id=c.network_id AND p.provider_instance_id=c.provider_instance_id AND p.capability='CreateJoinCredential')", params![network, instance, now.timestamp_millis()], |r| Ok((r.get(0)?,r.get(1)?,r.get(2)?))).optional()?.ok_or(StateError::MutationAuthorizationDenied("N4 create authority unavailable"))?;
            let mut session: JoinSession = serde_json::from_str(&record)?; if !session.is_n4() || session.state != JoinSessionState::InvitationValidated || now >= session.expires_at { return Err(StateError::Conflict("N4 session not dispatchable".into())); }; session.advance_n4(JoinSessionState::ProviderCredentialIssuing, now).map_err(|e| StateError::Conflict(e.to_string()))?;
            tx.execute("UPDATE join_sessions SET state=?2,record_json=?3,updated_at=?4 WHERE join_session_id=?1", params![join_session_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, now.to_rfc3339()])?;
            tx.execute("UPDATE n4_join_session_dispatches SET dispatch_state='dispatch_started',authorization_generation=?2,configuration_generation=?3,configuration_fingerprint=?4,dispatched_at_ms=?5 WHERE join_session_id=?1 AND dispatch_state='reserved'", params![join_session_id.to_string(), i64::try_from(auth).map_err(|_| StateError::Conflict("generation overflow".into()))?, i64::try_from(config).map_err(|_| StateError::Conflict("generation overflow".into()))?, fingerprint, now.timestamp_millis()])?;
            Ok(N4CredentialDispatch { join_session_id, invitation_id: nodescale_domain::InvitationId::parse(&invitation_id).map_err(|e| StateError::Conflict(e.to_string()))?, network_id: NetworkId::parse(&network).map_err(|e| StateError::Conflict(e.to_string()))?, context: N4InvitationContext::new(ProviderInstanceId::parse(&instance).map_err(|e| StateError::Conflict(e.to_string()))?, principal)?, authorization_generation: generation(auth)?, configuration_generation: generation(config)?, configuration_fingerprint: fingerprint })
        })
    }

    pub fn begin_n4_credential_dispatch_with_authorization(
        &self,
        join_session_id: JoinSessionId,
        now: DateTime<Utc>,
        _actor: AuditActor,
    ) -> Result<(N4CredentialDispatch, MutationAuthorization), StateError> {
        self.transactional(|tx, _| {
            let (record, invitation_id, network, instance, principal, state): (String, String, String, String, String, String) = tx.query_row("SELECT s.record_json,d.invitation_id,d.network_id,d.provider_instance_id,d.provider_principal_id,d.dispatch_state FROM n4_join_session_dispatches d JOIN join_sessions s ON s.join_session_id=d.join_session_id WHERE d.join_session_id=?1", [join_session_id.to_string()], |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?, r.get(4)?, r.get(5)?))).optional()?.ok_or_else(|| StateError::NotFound(join_session_id.to_string()))?;
            if state != "reserved" { return Err(StateError::Conflict("N4 dispatch already fenced".into())); }
            let row: (u64, u64, String, String, String, i64, i64, i64, i64, String) = tx.query_row("SELECT c.authorization_generation,c.configuration_generation,c.configuration_fingerprint,c.adapter,c.expected_version,c.enabled,c.revoked,c.not_before_ms,c.expires_at_ms,c.policy_mode FROM provider_mutation_configurations c JOIN provider_imports i ON i.network_id=c.network_id AND i.provider_instance_id=c.provider_instance_id WHERE c.network_id=?1 AND c.provider_instance_id=?2 AND i.read_only=1 AND i.mutation_allowed=0 AND EXISTS(SELECT 1 FROM provider_mutation_capabilities p WHERE p.network_id=c.network_id AND p.provider_instance_id=c.provider_instance_id AND p.capability='CreateJoinCredential')", params![network, instance], |r| Ok((r.get(0)?,r.get(1)?,r.get(2)?,r.get(3)?,r.get(4)?,r.get(5)?,r.get(6)?,r.get(7)?,r.get(8)?,r.get(9)?))).optional()?.ok_or(StateError::MutationAuthorizationDenied("N4 create authority unavailable"))?;
            let (auth_generation, config_generation, fingerprint, adapter, expected_version, enabled, revoked, not_before_ms, expires_at_ms, policy_mode) = row;
            let not_before = DateTime::from_timestamp_millis(not_before_ms).ok_or(StateError::MutationAuthorizationDenied("invalid persisted not-before"))?;
            let authority_expires_at = DateTime::from_timestamp_millis(expires_at_ms).ok_or(StateError::MutationAuthorizationDenied("invalid persisted expiry"))?;
            if enabled != 1 || revoked != 0 || now < not_before || now >= authority_expires_at || !valid_sha256_fingerprint(&fingerprint) || adapter != "headscale" || expected_version != "v0.29.3" { return Err(StateError::MutationAuthorizationDenied("N4 create authority unavailable")); }
            let mut session: JoinSession = serde_json::from_str(&record)?;
            if !session.is_n4() || session.state != JoinSessionState::InvitationValidated || now >= session.expires_at { return Err(StateError::Conflict("N4 session not dispatchable".into())); }
            session.advance_n4(JoinSessionState::ProviderCredentialIssuing, now).map_err(|e| StateError::Conflict(e.to_string()))?;
            tx.execute("UPDATE join_sessions SET state=?2,record_json=?3,updated_at=?4 WHERE join_session_id=?1", params![join_session_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, now.to_rfc3339()])?;
            tx.execute("UPDATE n4_join_session_dispatches SET dispatch_state='dispatch_started',authorization_generation=?2,configuration_generation=?3,configuration_fingerprint=?4,dispatched_at_ms=?5 WHERE join_session_id=?1 AND dispatch_state='reserved'", params![join_session_id.to_string(), i64::try_from(auth_generation).map_err(|_| StateError::Conflict("generation overflow".into()))?, i64::try_from(config_generation).map_err(|_| StateError::Conflict("generation overflow".into()))?, fingerprint, now.timestamp_millis()])?;
            let network_id = NetworkId::parse(&network).map_err(|e| StateError::Conflict(e.to_string()))?;
            let provider_instance_id = ProviderInstanceId::parse(&instance).map_err(|e| StateError::Conflict(e.to_string()))?;
            let authorization = MutationAuthorization { network_id, provider_instance_id, authorization_generation: generation(auth_generation)?, configuration_generation: generation(config_generation)?, configuration_fingerprint: fingerprint.clone(), adapter, expected_version, not_before, expires_at: authority_expires_at, capability: ProviderMutationCapability::CreateJoinCredential, policy_mode: parse_policy_mode(&policy_mode)? };
            let dispatch = N4CredentialDispatch { join_session_id, invitation_id: nodescale_domain::InvitationId::parse(&invitation_id).map_err(|e| StateError::Conflict(e.to_string()))?, network_id, context: N4InvitationContext::new(provider_instance_id, principal)?, authorization_generation: generation(auth_generation)?, configuration_generation: generation(config_generation)?, configuration_fingerprint: fingerprint };
            Ok((dispatch, authorization))
        })
    }

    pub fn confirm_n4_credential(
        &self,
        join_session_id: JoinSessionId,
        confirmation: N4CredentialConfirmation,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        if !safe_identifier(&confirmation.provider_principal_id)
            || confirmation.ephemeral
            || confirmation.approved_tags.is_empty()
            || confirmation.approved_tags.len() > 4
            || confirmation
                .approved_tags
                .iter()
                .any(|value| !n4_approved_tag(value))
        {
            return Err(StateError::Conflict(
                "invalid N4 credential metadata".into(),
            ));
        }
        self.transactional(|tx, store| {
            let row: (String,String,String,String,String,String,u64,u64,String,String) = tx.query_row("SELECT s.record_json,i.record_json,d.invitation_id,d.network_id,d.provider_instance_id,d.provider_principal_id,d.authorization_generation,d.configuration_generation,d.configuration_fingerprint,d.dispatch_state FROM n4_join_session_dispatches d JOIN join_sessions s ON s.join_session_id=d.join_session_id JOIN invitations i ON i.invitation_id=d.invitation_id WHERE d.join_session_id=?1", [join_session_id.to_string()], |r| Ok((r.get(0)?,r.get(1)?,r.get(2)?,r.get(3)?,r.get(4)?,r.get(5)?,r.get(6)?,r.get(7)?,r.get(8)?,r.get(9)?))).optional()?.ok_or_else(|| StateError::NotFound(join_session_id.to_string()))?;
            let (session_record, invitation_record, invitation_id, network, instance, principal, auth, config, fingerprint, state) = row;
            let mut invitation: Invitation = serde_json::from_str(&invitation_record)?;
            if state != "dispatch_started" || principal != confirmation.provider_principal_id || invitation.state != nodescale_domain::InvitationState::Redeeming || invitation.used_count != 1 || invitation.max_uses != 1 || confirmation.confirmed_at >= invitation.expires_at || confirmation.expires_at > invitation.expires_at || confirmation.expires_at <= confirmation.confirmed_at { return Err(StateError::Conflict("N4 confirmation is not valid for the durable fence".into())); }
            tx.execute("INSERT INTO confirmed_provider_credential_references (credential_id,network_id,provider_instance_id,provider_reference,authorization_generation,configuration_generation,configuration_fingerprint,confirmed_at_ms,expires_at_ms,max_uses) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,1)", params![confirmation.credential_id.to_string(), network, instance, confirmation.provider_reference.as_str(), i64::try_from(auth).map_err(|_| StateError::Conflict("generation overflow".into()))?, i64::try_from(config).map_err(|_| StateError::Conflict("generation overflow".into()))?, fingerprint, confirmation.confirmed_at.timestamp_millis(), confirmation.expires_at.timestamp_millis()]).map_err(map_constraint)?;
            let changed = tx.execute("UPDATE n4_join_session_dispatches SET dispatch_state='confirmed',credential_id=?2,resolved_at_ms=?3 WHERE join_session_id=?1 AND dispatch_state='dispatch_started'", params![join_session_id.to_string(), confirmation.credential_id.to_string(), confirmation.confirmed_at.timestamp_millis()])?;
            if changed != 1 {
                return Err(StateError::Conflict("N4 confirmation dispatch fence changed".into()));
            }
            tx.execute("INSERT INTO n4_provider_credential_metadata (credential_id,join_session_id,network_id,provider_instance_id,provider_principal_id,single_use,reusable,ephemeral,approved_tags_json,expires_at_ms,confirmed_at_ms,invalidation_state,safe_correlation_json) VALUES (?1,?2,?3,?4,?5,1,0,?6,?7,?8,?9,'active',?10)", params![confirmation.credential_id.to_string(), join_session_id.to_string(), network, instance, confirmation.provider_principal_id, i64::from(confirmation.ephemeral), serde_json::to_string(&confirmation.approved_tags)?, confirmation.expires_at.timestamp_millis(), confirmation.confirmed_at.timestamp_millis(), confirmation.safe_correlation.n4_digest_json()?])?;
            invitation.state = nodescale_domain::InvitationState::Consumed; invitation.provider_credential_reference = Some(confirmation.credential_id);
            tx.execute("UPDATE invitations SET state='consumed',provider_credential_reference=?2,record_json=?3 WHERE invitation_id=?1", params![invitation_id, confirmation.credential_id.to_string(), serde_json::to_string(&invitation)?])?;
            tx.execute("UPDATE n4_invitation_details SET consumed_at_ms=?2,revision=revision+1 WHERE invitation_id=?1", params![invitation_id, confirmation.confirmed_at.timestamp_millis()])?;
            let mut session: JoinSession = serde_json::from_str(&session_record)?; session.advance_n4(JoinSessionState::ProviderCredentialIssued, confirmation.confirmed_at).map_err(|e| StateError::Conflict(e.to_string()))?;
            tx.execute("UPDATE join_sessions SET state=?2,record_json=?3,updated_at=?4 WHERE join_session_id=?1", params![join_session_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, confirmation.confirmed_at.to_rfc3339()])?;
            let action_id = format!("credential-confirm:{join_session_id}");
            store.append_n4_audit(tx, nodescale_domain::InvitationId::parse(&invitation_id).map_err(|e| StateError::Conflict(e.to_string()))?, Some(join_session_id), &action_id, actor.clone(), "invitation_redeemed", "success", &SanitizedMetadata::empty())?;
            store.append_n4_audit(tx, nodescale_domain::InvitationId::parse(&invitation_id).map_err(|e| StateError::Conflict(e.to_string()))?, Some(join_session_id), &action_id, actor, "provider_join_credential_issued", "success", &SanitizedMetadata::empty())?;
            Ok(())
        })
    }

    pub fn fail_n4_credential_dispatch(
        &self,
        join_session_id: JoinSessionId,
        failure: N4DispatchFailure,
        now: DateTime<Utc>,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            let (session_record, invitation_record, invitation_id, _network, dispatch_state): (String,String,String,String,String) = tx.query_row("SELECT s.record_json,i.record_json,d.invitation_id,d.network_id,d.dispatch_state FROM n4_join_session_dispatches d JOIN join_sessions s ON s.join_session_id=d.join_session_id JOIN invitations i ON i.invitation_id=d.invitation_id WHERE d.join_session_id=?1", [join_session_id.to_string()], |r| Ok((r.get(0)?,r.get(1)?,r.get(2)?,r.get(3)?,r.get(4)?))).optional()?.ok_or_else(|| StateError::NotFound(join_session_id.to_string()))?;
            let expected = match failure { N4DispatchFailure::PreDispatch => "reserved", N4DispatchFailure::DefiniteNoApply | N4DispatchFailure::Ambiguous => "dispatch_started" }; if dispatch_state != expected { return Err(StateError::Conflict("N4 failure conflicts with dispatch fence".into())); }
            let mut invitation: Invitation = serde_json::from_str(&invitation_record)?; invitation.state = nodescale_domain::InvitationState::Failed;
            let mut session: JoinSession = serde_json::from_str(&session_record)?; session.advance_n4(match failure { N4DispatchFailure::PreDispatch | N4DispatchFailure::DefiniteNoApply => JoinSessionState::Failed, N4DispatchFailure::Ambiguous => JoinSessionState::ProviderCredentialAmbiguous }, now).map_err(|e| StateError::Conflict(e.to_string()))?;
            tx.execute("UPDATE invitations SET state='failed',record_json=?2 WHERE invitation_id=?1", params![invitation_id, serde_json::to_string(&invitation)?])?;
            tx.execute("UPDATE join_sessions SET state=?2,record_json=?3,updated_at=?4 WHERE join_session_id=?1", params![join_session_id.to_string(), lower(session.state.as_str()), serde_json::to_string(&session)?, now.to_rfc3339()])?;
            tx.execute("UPDATE n4_join_session_dispatches SET dispatch_state=?2,resolved_at_ms=?3 WHERE join_session_id=?1", params![join_session_id.to_string(), match failure { N4DispatchFailure::PreDispatch => "failed_pre_dispatch", N4DispatchFailure::DefiniteNoApply => "failed_no_apply", N4DispatchFailure::Ambiguous => "ambiguous" }, now.timestamp_millis()])?;
            store.append_n4_audit(tx, nodescale_domain::InvitationId::parse(&invitation_id).map_err(|e| StateError::Conflict(e.to_string()))?, Some(join_session_id), &format!("credential-failure:{join_session_id}"), actor, "invitation_redemption_failed", "failed", &SanitizedMetadata::empty())?;
            Ok(())
        })
    }

    pub fn issue_invitation(
        &self,
        invitation: &Invitation,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            tx.execute("INSERT INTO invitations (invitation_id,network_id,state,secret_verifier,provider_credential_reference,max_uses,used_count,record_json,created_at,expires_at) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10)", params![invitation.invitation_id.to_string(), invitation.network_id.to_string(), lower(invitation.state.as_str()), invitation.secret_verifier.as_str(), invitation.provider_credential_reference.map(|id| id.to_string()), i64::from(invitation.max_uses), i64::from(invitation.used_count), serde_json::to_string(invitation)?, invitation.created_at.to_rfc3339(), invitation.expires_at.to_rfc3339()]).map_err(map_constraint)?;
            store.append_audit(tx, Some(invitation.network_id), None, actor, "invitation.issued", "success", None, &SanitizedMetadata::empty())
        })
    }

    pub fn create_join_session(
        &self,
        session: &JoinSession,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            tx.execute("INSERT INTO join_sessions (join_session_id,invitation_id,network_id,device_id,state,record_json,created_at,expires_at,updated_at) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9)", params![session.join_session_id.to_string(), session.invitation_id.to_string(), session.network_id.to_string(), session.device_id.map(|id| id.to_string()), lower(session.state.as_str()), serde_json::to_string(session)?, session.created_at.to_rfc3339(), session.expires_at.to_rfc3339(), session.updated_at.to_rfc3339()]).map_err(map_constraint)?;
            store.append_audit(tx, Some(session.network_id), session.device_id, actor, "join_session.created", "success", None, &SanitizedMetadata::empty())
        })
    }

    pub fn join_session(&self, join_session_id: JoinSessionId) -> Result<JoinSession, StateError> {
        let record = self
            .connection
            .borrow()
            .query_row(
                "SELECT record_json FROM join_sessions WHERE join_session_id=?1",
                [join_session_id.to_string()],
                |row| row.get::<_, String>(0),
            )
            .optional()?
            .ok_or_else(|| StateError::NotFound(join_session_id.to_string()))?;
        Ok(serde_json::from_str(&record)?)
    }

    pub fn transition_join_session(
        &self,
        join_session_id: JoinSessionId,
        expected: JoinSessionState,
        next: JoinSessionState,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            let n4_owned: bool = tx.query_row("SELECT EXISTS(SELECT 1 FROM n4_join_session_dispatches WHERE join_session_id=?1)", [join_session_id.to_string()], |row| row.get(0))?;
            if n4_owned { return Err(StateError::Conflict("N4 join sessions require fenced lifecycle APIs".into())); }
            let record = tx.query_row(
                "SELECT record_json FROM join_sessions WHERE join_session_id=?1",
                [join_session_id.to_string()],
                |row| row.get::<_, String>(0),
            ).optional()?.ok_or_else(|| StateError::NotFound(join_session_id.to_string()))?;
            let mut session: JoinSession = serde_json::from_str(&record)?;
            if session.state != expected {
                return Err(StateError::Conflict("join session state changed concurrently".into()));
            }
            session.transition(next, Utc::now()).map_err(|error| StateError::Conflict(error.to_string()))?;
            let changed = tx.execute(
                "UPDATE join_sessions SET state=?3,record_json=?4,updated_at=?5 WHERE join_session_id=?1 AND state=?2",
                params![join_session_id.to_string(), lower(expected.as_str()), lower(next.as_str()), serde_json::to_string(&session)?, session.updated_at.to_rfc3339()],
            )?;
            if changed == 0 { return Err(StateError::Conflict("join session state changed concurrently".into())); }
            store.append_audit(tx, Some(session.network_id), session.device_id, actor, "join_session.state_changed", "success", None, &SanitizedMetadata::empty())
        })
    }

    pub fn record_revocation(
        &self,
        revocation: &Revocation,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            let record = tx
                .query_row(
                    "SELECT record_json FROM devices WHERE device_id=?1 AND network_id=?2",
                    params![revocation.device_id.to_string(), revocation.network_id.to_string()],
                    |row| row.get::<_, String>(0),
                )
                .optional()?
                .ok_or_else(|| StateError::NotFound(revocation.device_id.to_string()))?;
            let mut device: Device = serde_json::from_str(&record)?;
            device.membership_state = device
                .membership_state
                .transition(nodescale_domain::MembershipState::Revoking)
                .map_err(|error| StateError::Conflict(error.to_string()))?;
            device.updated_at = revocation.updated_at;
            tx.execute("INSERT INTO revocations (revocation_id,network_id,device_id,state,record_json,requested_at,updated_at,application_trust_removed_at,provider_cleanup_completed_at) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9)", params![revocation.revocation_id.to_string(), revocation.network_id.to_string(), revocation.device_id.to_string(), lower(revocation.state.as_str()), serde_json::to_string(revocation)?, revocation.requested_at.to_rfc3339(), revocation.updated_at.to_rfc3339(), revocation.application_trust_removed_at.map(|value| value.to_rfc3339()), revocation.provider_cleanup_completed_at.map(|value| value.to_rfc3339())]).map_err(map_constraint)?;
            tx.execute("UPDATE devices SET membership_state='revoking', record_json=?2, updated_at=?3 WHERE device_id=?1", params![revocation.device_id.to_string(), serde_json::to_string(&device)?, revocation.updated_at.to_rfc3339()])?;
            store.append_audit(tx, Some(revocation.network_id), Some(revocation.device_id), actor, "revocation.requested", "success", None, &SanitizedMetadata::empty())
        })
    }

    pub fn network(&self, network_id: NetworkId) -> Result<Network, StateError> {
        let record = self
            .connection
            .borrow()
            .query_row(
                "SELECT record_json FROM networks WHERE network_id=?1",
                [network_id.to_string()],
                |row| row.get::<_, String>(0),
            )
            .optional()?
            .ok_or_else(|| StateError::NotFound(network_id.to_string()))?;
        Ok(serde_json::from_str(&record)?)
    }

    pub fn network_generation(&self, network_id: NetworkId) -> Result<Generation, StateError> {
        let value = self
            .connection
            .borrow()
            .query_row(
                "SELECT generation FROM membership_generations WHERE network_id=?1",
                [network_id.to_string()],
                |row| row.get::<_, u64>(0),
            )
            .optional()?
            .ok_or_else(|| StateError::NotFound(network_id.to_string()))?;
        Generation::new(value).map_err(|error| StateError::Conflict(error.to_string()))
    }

    /// Atomically replace the explicit owner-controlled authorization config
    /// and all of its capabilities. `None` expects absence; `Some` is CAS.
    pub fn replace_provider_mutation_configuration(
        &self,
        network_id: NetworkId,
        expected_authorization_generation: Option<Generation>,
        expected_configuration_generation: Option<Generation>,
        replacement: ProviderMutationConfiguration,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            let current = tx.query_row(
                "SELECT provider_instance_id,authorization_generation,configuration_generation FROM provider_mutation_configurations WHERE network_id=?1",
                [network_id.to_string()],
                |row| Ok((row.get::<_, String>(0)?, row.get::<_, u64>(1)?, row.get::<_, u64>(2)?)),
            ).optional()?;
            let current_exists = current.is_some();
            match current {
                None if expected_authorization_generation.is_none() && expected_configuration_generation.is_none() => {}
                None => {
                    let expected = expected_authorization_generation
                        .or(expected_configuration_generation)
                        .expect("a CAS expectation exists");
                    return Err(StateError::StaleGeneration { expected: expected.get(), actual: 0 });
                }
                Some((current_provider_instance, actual_authorization, actual_configuration)) => {
                    if current_provider_instance != replacement.provider_instance_id.to_string() {
                        return Err(StateError::Conflict(
                            "mutation provider identity cannot be replaced".into(),
                        ));
                    }
                    if expected_authorization_generation.map(Generation::get) != Some(actual_authorization) {
                        return Err(StateError::StaleGeneration {
                            expected: expected_authorization_generation.map_or(0, Generation::get),
                            actual: actual_authorization,
                        });
                    }
                    if expected_configuration_generation.map(Generation::get) != Some(actual_configuration) {
                        return Err(StateError::StaleGeneration {
                            expected: expected_configuration_generation.map_or(0, Generation::get),
                            actual: actual_configuration,
                        });
                    }
                    if replacement.authorization_generation.get() <= actual_authorization
                        || replacement.configuration_generation.get() <= actual_configuration
                    {
                        return Err(StateError::Conflict(
                            "replacement mutation generations must advance".into(),
                        ));
                    }
                }
            }
            let import_matches: bool = tx.query_row(
                "SELECT EXISTS(SELECT 1 FROM provider_imports WHERE network_id=?1 AND provider_instance_id=?2 AND read_only=1 AND mutation_allowed=0)",
                params![network_id.to_string(), replacement.provider_instance_id.to_string()], |row| row.get(0),
            )?;
            if !import_matches {
                return Err(StateError::MutationAuthorizationDenied("exact read-only import is required"));
            }
            let values = params![
                network_id.to_string(), replacement.provider_instance_id.to_string(),
                to_i64(replacement.authorization_generation)?, to_i64(replacement.configuration_generation)?,
                replacement.configuration_fingerprint, replacement.adapter, replacement.expected_version,
                i64::from(replacement.enabled), i64::from(replacement.revoked),
                replacement.not_before.timestamp_millis(), replacement.expires_at.timestamp_millis(),
                policy_mode_name(replacement.policy_mode),
            ];
            if current_exists {
                tx.execute("DELETE FROM provider_mutation_capabilities WHERE network_id=?1", [network_id.to_string()])?;
                tx.execute("UPDATE provider_mutation_configurations SET provider_instance_id=?2,authorization_generation=?3,configuration_generation=?4,configuration_fingerprint=?5,adapter=?6,expected_version=?7,enabled=?8,revoked=?9,not_before_ms=?10,expires_at_ms=?11,policy_mode=?12 WHERE network_id=?1", values)?;
            } else {
                tx.execute("INSERT INTO provider_mutation_configurations (network_id,provider_instance_id,authorization_generation,configuration_generation,configuration_fingerprint,adapter,expected_version,enabled,revoked,not_before_ms,expires_at_ms,policy_mode) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10,?11,?12)", values)?;
            }
            for capability in replacement.capabilities {
                tx.execute("INSERT INTO provider_mutation_capabilities (network_id,provider_instance_id,capability) VALUES (?1,?2,?3)", params![network_id.to_string(), replacement.provider_instance_id.to_string(), mutation_capability_name(capability)])?;
            }
            store.append_audit(tx, Some(network_id), None, actor, "provider_mutation_configured", "success", Some(replacement.authorization_generation), &SanitizedMetadata::empty())
        })
    }

    /// Mint from current persisted v3 configuration only. A single captured
    /// `now` drives the half-open validity check.
    pub fn issue_mutation_authorization(
        &self,
        network_id: NetworkId,
        provider_instance_id: ProviderInstanceId,
        capability: ProviderMutationCapability,
        now: DateTime<Utc>,
    ) -> Result<MutationAuthorization, StateError> {
        let connection = self.connection.borrow();
        let row = connection.query_row(
            "SELECT c.authorization_generation,c.configuration_generation,c.configuration_fingerprint,c.adapter,c.expected_version,c.enabled,c.revoked,c.not_before_ms,c.expires_at_ms,c.policy_mode FROM provider_mutation_configurations c JOIN provider_imports i ON i.network_id=c.network_id AND i.provider_instance_id=c.provider_instance_id WHERE c.network_id=?1 AND c.provider_instance_id=?2 AND i.read_only=1 AND i.mutation_allowed=0 AND EXISTS (SELECT 1 FROM provider_mutation_capabilities p WHERE p.network_id=c.network_id AND p.provider_instance_id=c.provider_instance_id AND p.capability=?3)",
            params![network_id.to_string(), provider_instance_id.to_string(), mutation_capability_name(capability)],
            |row| Ok((row.get::<_, u64>(0)?, row.get::<_, u64>(1)?, row.get::<_, String>(2)?, row.get::<_, String>(3)?, row.get::<_, String>(4)?, row.get::<_, i64>(5)?, row.get::<_, i64>(6)?, row.get::<_, i64>(7)?, row.get::<_, i64>(8)?, row.get::<_, String>(9)?)),
        ).optional()?.ok_or(StateError::MutationAuthorizationDenied("no current configured capability"))?;
        let (
            authorization_generation,
            configuration_generation,
            configuration_fingerprint,
            adapter,
            expected_version,
            enabled,
            revoked,
            not_before_ms,
            expires_at_ms,
            policy_mode,
        ) = row;
        let not_before = DateTime::from_timestamp_millis(not_before_ms).ok_or(
            StateError::MutationAuthorizationDenied("invalid persisted not-before"),
        )?;
        let expires_at = DateTime::from_timestamp_millis(expires_at_ms).ok_or(
            StateError::MutationAuthorizationDenied("invalid persisted expiry"),
        )?;
        if enabled != 1
            || revoked != 0
            || now < not_before
            || now >= expires_at
            || !valid_sha256_fingerprint(&configuration_fingerprint)
            || adapter != "headscale"
            || expected_version != "v0.29.3"
            || (capability == ProviderMutationCapability::ManagePolicy && policy_mode != "database")
        {
            return Err(StateError::MutationAuthorizationDenied(
                "configuration is not currently issuable",
            ));
        }
        Ok(MutationAuthorization {
            network_id,
            provider_instance_id,
            authorization_generation: generation(authorization_generation)?,
            configuration_generation: generation(configuration_generation)?,
            configuration_fingerprint,
            adapter,
            expected_version,
            not_before,
            expires_at,
            capability,
            policy_mode: parse_policy_mode(&policy_mode)?,
        })
    }

    /// Persist only a confirmed provider-native reference. No credential
    /// plaintext is accepted by this API or stored in this table.
    pub fn record_confirmed_provider_credential_reference(
        &self,
        reference: &ConfirmedProviderCredentialReference,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            let current: bool = tx.query_row(
                "SELECT EXISTS(SELECT 1 FROM provider_mutation_configurations c JOIN provider_mutation_capabilities p ON p.network_id=c.network_id AND p.provider_instance_id=c.provider_instance_id WHERE c.network_id=?1 AND c.provider_instance_id=?2 AND c.authorization_generation=?3 AND c.configuration_generation=?4 AND c.configuration_fingerprint=?5 AND c.enabled=1 AND c.revoked=0 AND p.capability='CreateJoinCredential' AND ?6>=c.not_before_ms AND ?6<c.expires_at_ms)",
                params![
                    reference.network_id.to_string(),
                    reference.provider_instance_id.to_string(),
                    to_i64(reference.authorization_generation)?,
                    to_i64(reference.configuration_generation)?,
                    reference.configuration_fingerprint,
                    reference.confirmed_at.timestamp_millis(),
                ],
                |row| row.get(0),
            )?;
            if !current {
                return Err(StateError::MutationAuthorizationDenied(
                    "confirmed credential reference is not bound to current authority",
                ));
            }
            tx.execute(
                "INSERT INTO confirmed_provider_credential_references (credential_id,network_id,provider_instance_id,provider_reference,authorization_generation,configuration_generation,configuration_fingerprint,confirmed_at_ms,expires_at_ms,max_uses) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10)",
                params![
                    reference.credential_id.to_string(),
                    reference.network_id.to_string(),
                    reference.provider_instance_id.to_string(),
                    reference.provider_reference.as_str(),
                    to_i64(reference.authorization_generation)?,
                    to_i64(reference.configuration_generation)?,
                    reference.configuration_fingerprint,
                    reference.confirmed_at.timestamp_millis(),
                    reference.expires_at.timestamp_millis(),
                    i64::from(reference.max_uses),
                ],
            )
            .map_err(map_constraint)?;
            store.append_audit(
                tx,
                Some(reference.network_id),
                None,
                actor,
                "provider_credential_reference.confirmed",
                "success",
                Some(reference.authorization_generation),
                &SanitizedMetadata::empty(),
            )
        })
    }

    pub fn confirmed_provider_credential_reference(
        &self,
        credential_id: ProviderCredentialId,
    ) -> Result<ConfirmedProviderCredentialReference, StateError> {
        let row = self.connection.borrow().query_row(
            "SELECT network_id,provider_instance_id,provider_reference,authorization_generation,configuration_generation,configuration_fingerprint,confirmed_at_ms,expires_at_ms,max_uses FROM confirmed_provider_credential_references WHERE credential_id=?1",
            [credential_id.to_string()],
            |row| Ok((
                row.get::<_, String>(0)?, row.get::<_, String>(1)?, row.get::<_, String>(2)?,
                row.get::<_, u64>(3)?, row.get::<_, u64>(4)?, row.get::<_, String>(5)?,
                row.get::<_, i64>(6)?, row.get::<_, i64>(7)?, row.get::<_, u32>(8)?,
            )),
        ).optional()?.ok_or_else(|| StateError::NotFound(credential_id.to_string()))?;
        ConfirmedProviderCredentialReference::new(
            credential_id,
            NetworkId::parse(&row.0).map_err(|error| StateError::Conflict(error.to_string()))?,
            ProviderInstanceId::parse(&row.1)
                .map_err(|error| StateError::Conflict(error.to_string()))?,
            ProviderCredentialReference::new(row.2)
                .map_err(|error| StateError::Conflict(error.to_string()))?,
            generation(row.3)?,
            generation(row.4)?,
            row.5,
            DateTime::from_timestamp_millis(row.6).ok_or(
                StateError::MutationAuthorizationDenied("invalid persisted confirmation time"),
            )?,
            DateTime::from_timestamp_millis(row.7).ok_or(
                StateError::MutationAuthorizationDenied("invalid persisted credential expiry"),
            )?,
            row.8,
        )
    }

    pub fn device(&self, device_id: DeviceId) -> Result<Device, StateError> {
        let record = self
            .connection
            .borrow()
            .query_row(
                "SELECT record_json FROM devices WHERE device_id=?1",
                [device_id.to_string()],
                |row| row.get::<_, String>(0),
            )
            .optional()?
            .ok_or_else(|| StateError::NotFound(device_id.to_string()))?;
        Ok(serde_json::from_str(&record)?)
    }

    /// Bounded stable page used by the authenticated operator contract.
    pub fn operator_device_page(
        &self,
        network_id: NetworkId,
        after: Option<DeviceId>,
        limit: usize,
    ) -> Result<Vec<Device>, StateError> {
        if !(1..=DEVICE_PAGE_MAX).contains(&limit) {
            return Err(StateError::Conflict(
                "operator device page limit is out of bounds".into(),
            ));
        }
        let after = after.map(|device_id| device_id.to_string());
        let connection = self.connection.borrow();
        let mut statement = connection.prepare(
            "SELECT record_json FROM devices \
             WHERE network_id=?1 AND (?2 IS NULL OR device_id>?2) \
             ORDER BY device_id ASC LIMIT ?3",
        )?;
        let rows = statement.query_map(
            params![network_id.to_string(), after, limit as u64],
            |row| row.get::<_, String>(0),
        )?;
        let mut devices = Vec::with_capacity(limit);
        for row in rows {
            devices.push(serde_json::from_str(&row?)?);
        }
        Ok(devices)
    }

    pub fn device_generations(&self, device_id: DeviceId) -> Result<DeviceGenerations, StateError> {
        let values = self.connection.borrow().query_row("SELECT credential_generation,keryx_binding_generation,fleet_projection_generation FROM device_generations WHERE device_id=?1", [device_id.to_string()], |row| Ok((row.get::<_,u64>(0)?, row.get::<_,u64>(1)?, row.get::<_,u64>(2)?))).optional()?.ok_or_else(|| StateError::NotFound(device_id.to_string()))?;
        Ok(DeviceGenerations {
            credential: generation(values.0)?,
            keryx_binding: generation(values.1)?,
            fleet_projection: generation(values.2)?,
        })
    }

    pub fn revocation_state(&self, device_id: DeviceId) -> Result<RevocationState, StateError> {
        let value = self
            .connection
            .borrow()
            .query_row(
                "SELECT state FROM revocations WHERE device_id=?1",
                [device_id.to_string()],
                |row| row.get::<_, String>(0),
            )
            .optional()?
            .ok_or_else(|| StateError::NotFound(device_id.to_string()))?;
        match value.as_str() {
            "requested" => Ok(RevocationState::Requested),
            "applicationtrustremovalpending" => Ok(RevocationState::ApplicationTrustRemovalPending),
            "credentialrevocationpending" => Ok(RevocationState::CredentialRevocationPending),
            "keryxbindingdisablepending" => Ok(RevocationState::KeryxBindingDisablePending),
            "providercleanuppending" => Ok(RevocationState::ProviderCleanupPending),
            "revoked" => Ok(RevocationState::Revoked),
            _ => Err(StateError::Conflict("unknown revocation state".into())),
        }
    }

    pub fn advance_membership_generation(
        &self,
        network_id: NetworkId,
        expected: Generation,
        next: Generation,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        validate_next(expected, next)?;
        self.transactional(|tx, store| {
            let record = tx
                .query_row(
                    "SELECT record_json FROM networks WHERE network_id=?1",
                    [network_id.to_string()],
                    |row| row.get::<_, String>(0),
                )
                .optional()?
                .ok_or_else(|| StateError::NotFound(network_id.to_string()))?;
            let mut network: Network = serde_json::from_str(&record)?;
            if network.membership_generation != expected {
                return Err(StateError::StaleGeneration {
                    expected: expected.get(),
                    actual: network.membership_generation.get(),
                });
            }
            let now = Utc::now();
            network.membership_generation = next;
            network.updated_at = now;
            let changed = tx.execute("UPDATE membership_generations SET generation=?3,updated_at=?4 WHERE network_id=?1 AND generation=?2", params![network_id.to_string(), to_i64(expected)?, to_i64(next)?, now.to_rfc3339()])?;
            if changed == 0 { return Err(stale_network_generation(tx, network_id, expected)?); }
            tx.execute("UPDATE networks SET membership_generation=?2,record_json=?3,updated_at=?4 WHERE network_id=?1", params![network_id.to_string(), to_i64(next)?, serde_json::to_string(&network)?, now.to_rfc3339()])?;
            store.append_audit(tx, Some(network_id), None, actor, "membership.generation.advanced", "success", Some(next), &SanitizedMetadata::empty())
        })
    }

    pub fn advance_device_credential_generation(
        &self,
        device_id: DeviceId,
        expected: Generation,
        next: Generation,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        validate_next(expected, next)?;
        self.transactional(|tx, store| {
            let record = tx
                .query_row(
                    "SELECT record_json FROM devices WHERE device_id=?1",
                    [device_id.to_string()],
                    |row| row.get::<_, String>(0),
                )
                .optional()?
                .ok_or_else(|| StateError::NotFound(device_id.to_string()))?;
            let mut device: Device = serde_json::from_str(&record)?;
            if device.generations.credential != expected {
                return Err(StateError::StaleGeneration {
                    expected: expected.get(),
                    actual: device.generations.credential.get(),
                });
            }
            let network_id = device.network_id;
            let now = Utc::now();
            device.generations.credential = next;
            device.updated_at = now;
            let changed = tx.execute("UPDATE device_generations SET credential_generation=?3,updated_at=?4 WHERE device_id=?1 AND credential_generation=?2", params![device_id.to_string(), to_i64(expected)?, to_i64(next)?, now.to_rfc3339()])?;
            if changed == 0 {
                let actual = tx.query_row("SELECT credential_generation FROM device_generations WHERE device_id=?1", [device_id.to_string()], |row| row.get::<_,u64>(0)).optional()?.ok_or_else(|| StateError::NotFound(device_id.to_string()))?;
                return Err(StateError::StaleGeneration { expected: expected.get(), actual });
            }
            tx.execute("UPDATE devices SET credential_generation=?2,record_json=?3,updated_at=?4 WHERE device_id=?1", params![device_id.to_string(), to_i64(next)?, serde_json::to_string(&device)?, now.to_rfc3339()])?;
            store.append_audit(tx, Some(network_id), Some(device_id), actor, "device.credential_generation.advanced", "success", Some(next), &SanitizedMetadata::empty())
        })
    }

    /// Import one configured Headscale provider only after a compatible,
    /// identity-matching, permanently read-only inspection succeeds.
    pub async fn import_headscale_network(
        &self,
        network: &Network,
        config: &HeadscaleImportConfig,
        provider: &dyn ReadOnlyProvider,
        snapshot_at: DateTime<Utc>,
        actor: AuditActor,
    ) -> Result<(), ReconciliationFailure> {
        config.validate_for_persistence()?;
        if network.provider_kind != ProviderKind::Headscale
            || network.provider_instance_id != config.provider_instance_id
            || provider.instance_id() != config.provider_instance_id
            || !config.read_only
            || config.mutation_allowed
        {
            return Err(ReconciliationFailure::Incompatible);
        }
        let inspection = provider
            .inspect_server()
            .await
            .map_err(map_provider_failure)?;
        validate_inspection(&inspection, config)?;
        let nodes = provider.list_nodes().await.map_err(map_provider_failure)?;
        let nodes = validate_snapshot(nodes, config.provider_instance_id)?;
        self.transactional(|tx, store| {
            let record = serde_json::to_string(network)?;
            tx.execute("INSERT INTO networks (network_id,name,state,provider_kind,provider_instance_id,membership_generation,policy_generation,record_json,created_at,updated_at) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10)", params![network.network_id.to_string(), network.name, lower(network.state.as_str()), "headscale", network.provider_instance_id.to_string(), to_i64(network.membership_generation)?, to_i64(network.policy_generation)?, record, network.created_at.to_rfc3339(), network.updated_at.to_rfc3339()]).map_err(map_constraint)?;
            tx.execute("INSERT INTO membership_generations (network_id,generation,updated_at) VALUES (?1,?2,?3)", params![network.network_id.to_string(), to_i64(network.membership_generation)?, network.updated_at.to_rfc3339()]).map_err(map_constraint)?;
            tx.execute("INSERT INTO provider_imports (network_id,provider_instance_id,server_url,opaque_secret_reference,compatibility_pin,custom_root_ca_sha256,tls_verification,read_only,mutation_allowed,compatibility,provider_version,last_success_at,last_attempt_at) VALUES (?1,?2,?3,?4,?5,?6,'verify',1,0,?7,?8,?9,?9)", params![network.network_id.to_string(), config.provider_instance_id.to_string(), config.server_url, config.opaque_secret_reference, config.compatibility_pin, config.custom_root_ca_sha256, compatibility_name(inspection.compatibility), inspection.provider_version, snapshot_at.to_rfc3339()]).map_err(map_constraint)?;
            store.append_audit(tx, Some(network.network_id), None, actor.clone(), "network_imported", "success", Some(network.membership_generation), &SanitizedMetadata::empty())?;
            store.append_audit(tx, Some(network.network_id), None, actor.clone(), "provider_reconciliation_started", "success", None, &SanitizedMetadata::empty())?;
            for node in &nodes {
                let classification = if node.expired {
                    ObservationClassification::ProviderExpired
                } else {
                    ObservationClassification::DiscoveredUnmanaged
                };
                insert_new_observation(
                    tx,
                    network.network_id,
                    config.provider_instance_id,
                    node,
                    classification,
                    snapshot_at,
                )?;
                store.append_audit(
                    tx,
                    Some(network.network_id),
                    None,
                    actor.clone(),
                    if node.expired { "provider_node_expired" } else { "provider_node_discovered" },
                    "success",
                    None,
                    &SanitizedMetadata::empty(),
                )?;
            }
            store.append_audit(tx, Some(network.network_id), None, actor, "provider_reconciliation_completed", "success", None, &SanitizedMetadata::empty())
        })?;
        Ok(())
    }

    /// Import one configured Tailscale SaaS provider as read-only observations.
    /// Provider membership never creates a Nodescale device or Fleet authority.
    pub async fn import_tailscale_network(
        &self,
        network: &Network,
        config: &TailscaleImportConfig,
        provider: &dyn ReadOnlyProvider,
        snapshot_at: DateTime<Utc>,
        actor: AuditActor,
    ) -> Result<(), ReconciliationFailure> {
        if network.provider_kind != ProviderKind::Tailscale
            || network.provider_instance_id != config.provider_instance_id
            || provider.instance_id() != config.provider_instance_id
            || !config.read_only
            || config.mutation_allowed
        {
            return Err(ReconciliationFailure::Incompatible);
        }
        let inspection = provider
            .inspect_server()
            .await
            .map_err(map_provider_failure)?;
        validate_read_only_inspection(
            &inspection,
            config.provider_instance_id,
            "tailscale",
            &config.compatibility_pin,
        )?;
        let nodes = provider.list_nodes().await.map_err(map_provider_failure)?;
        let nodes = validate_snapshot(nodes, config.provider_instance_id)?;
        self.transactional(|tx, store| {
            let record = serde_json::to_string(network)?;
            tx.execute("INSERT INTO networks (network_id,name,state,provider_kind,provider_instance_id,membership_generation,policy_generation,record_json,created_at,updated_at) VALUES (?1,?2,?3,'tailscale',?4,?5,?6,?7,?8,?9)", params![network.network_id.to_string(), network.name, lower(network.state.as_str()), network.provider_instance_id.to_string(), to_i64(network.membership_generation)?, to_i64(network.policy_generation)?, record, network.created_at.to_rfc3339(), network.updated_at.to_rfc3339()]).map_err(map_constraint)?;
            tx.execute("INSERT INTO membership_generations (network_id,generation,updated_at) VALUES (?1,?2,?3)", params![network.network_id.to_string(), to_i64(network.membership_generation)?, network.updated_at.to_rfc3339()]).map_err(map_constraint)?;
            tx.execute("INSERT INTO provider_imports (network_id,provider_instance_id,server_url,opaque_secret_reference,compatibility_pin,custom_root_ca_sha256,tls_verification,read_only,mutation_allowed,compatibility,provider_version,last_success_at,last_attempt_at) VALUES (?1,?2,?3,?4,?5,NULL,'verify',1,0,?6,?7,?8,?8)", params![network.network_id.to_string(), config.provider_instance_id.to_string(), config.scoped_api_url(), config.opaque_secret_reference, config.compatibility_pin, compatibility_name(inspection.compatibility), inspection.provider_version, snapshot_at.to_rfc3339()]).map_err(map_constraint)?;
            store.append_audit(tx, Some(network.network_id), None, actor.clone(), "network_imported", "success", Some(network.membership_generation), &SanitizedMetadata::empty())?;
            store.append_audit(tx, Some(network.network_id), None, actor.clone(), "provider_reconciliation_started", "success", None, &SanitizedMetadata::empty())?;
            for node in &nodes {
                let classification = if node.expired {
                    ObservationClassification::ProviderExpired
                } else {
                    ObservationClassification::DiscoveredUnmanaged
                };
                insert_new_observation(
                    tx,
                    network.network_id,
                    config.provider_instance_id,
                    node,
                    classification,
                    snapshot_at,
                )?;
                store.append_audit(
                    tx,
                    Some(network.network_id),
                    None,
                    actor.clone(),
                    if node.expired { "provider_node_expired" } else { "provider_node_discovered" },
                    "success",
                    None,
                    &SanitizedMetadata::empty(),
                )?;
            }
            store.append_audit(tx, Some(network.network_id), None, actor, "provider_reconciliation_completed", "success", None, &SanitizedMetadata::empty())
        })?;
        Ok(())
    }

    /// Apply a complete successful snapshot. No device is created or activated;
    /// provider observations remain untrusted evidence.
    pub async fn reconcile_read_only(
        &self,
        network_id: NetworkId,
        provider: &dyn ReadOnlyProvider,
        snapshot_at: DateTime<Utc>,
        actor: AuditActor,
    ) -> Result<ReconciliationReport, ReconciliationFailure> {
        let config = self.reconciliation_import_config(network_id)?;
        let configured_instance = config.provider_instance_id;
        if provider.instance_id() != configured_instance {
            self.record_provider_failure(
                network_id,
                snapshot_at,
                "identity_conflict",
                "provider instance mismatch",
                actor.clone(),
            )?;
            return Err(ReconciliationFailure::IdentityConflict);
        }
        let inspection = match provider.inspect_server().await {
            Ok(value) => value,
            Err(error) => {
                let failure = map_provider_failure(error);
                self.record_failure_for(network_id, snapshot_at, &failure, actor.clone())?;
                return Err(failure);
            }
        };
        if let Err(failure) = validate_read_only_inspection(
            &inspection,
            config.provider_instance_id,
            config.provider_name,
            &config.compatibility_pin,
        ) {
            self.record_failure_for(network_id, snapshot_at, &failure, actor.clone())?;
            return Err(failure);
        }
        let nodes = match provider.list_nodes().await {
            Ok(nodes) => nodes,
            Err(error) => {
                let failure = map_provider_failure(error);
                self.record_failure_for(network_id, snapshot_at, &failure, actor.clone())?;
                return Err(failure);
            }
        };
        let nodes = match validate_snapshot(nodes, configured_instance) {
            Ok(nodes) => nodes,
            Err(failure) => {
                self.record_failure_for(network_id, snapshot_at, &failure, actor.clone())?;
                return Err(failure);
            }
        };
        self.transactional(|tx, store| {
            let existing = load_observations(tx, network_id)?;
            let incoming_ids = nodes.iter().map(|node| node.identity.node_id.to_string()).collect::<BTreeSet<_>>();
            let mut semantic_change = false;
            let mut changes = Vec::new();
            for node in &nodes {
                let key = node.identity.node_id.to_string();
                let previous = existing.get(&key);
                let (stored_node, classification, fingerprint, changed, event_kind) = match previous {
                    Some(old)
                        if old.stable_machine_key_fingerprint
                            != node.identity.stable_key_fingerprint
                            || old.node.identity_evidence.machine_key
                                != node.identity_evidence.machine_key => (
                        old.node.clone(), ObservationClassification::IdentityConflict, old.semantic_fingerprint.clone(),
                        old.classification != ObservationClassification::IdentityConflict, "provider_identity_conflict",
                    ),
                    Some(old) => {
                        let classification = next_classification(old.classification, node);
                        let fingerprint = semantic_fingerprint(node)?;
                        let changed = old.semantic_fingerprint != fingerprint || old.classification != classification;
                        (node.clone(), classification, fingerprint, changed, if classification == ObservationClassification::ProviderExpired { "provider_node_expired" } else { "provider_node_changed" })
                    }
                    None => {
                        let classification = if node.expired { ObservationClassification::ProviderExpired } else { ObservationClassification::DiscoveredUnmanaged };
                        (node.clone(), classification, semantic_fingerprint(node)?, true, "provider_node_discovered")
                    }
                };
                if changed { semantic_change = true; changes.push((key.clone(), event_kind)); }
                let serialized = serde_json::to_string(&stored_node)?;
                let first = previous.map(|old| old.first_observed_at).unwrap_or(snapshot_at);
                let device_id = previous.and_then(|old| old.device_id);
                tx.execute("INSERT INTO provider_observations (observation_id,network_id,device_id,provider_instance_id,provider_node_id,stable_key_fingerprint,classification,adoption_state,semantic_fingerprint,normalized_json,first_observed_at,last_observed_at,snapshot_at) VALUES (?1,?2,?3,?4,?5,?6,?7,'unmanaged',?8,?9,?10,?11,?12) ON CONFLICT(provider_instance_id,provider_node_id) DO UPDATE SET device_id=excluded.device_id,classification=excluded.classification,semantic_fingerprint=excluded.semantic_fingerprint,semantic_generation=CASE WHEN provider_observations.classification<>excluded.classification OR provider_observations.semantic_fingerprint<>excluded.semantic_fingerprint THEN provider_observations.semantic_generation+1 ELSE provider_observations.semantic_generation END,normalized_json=excluded.normalized_json,last_observed_at=excluded.last_observed_at,snapshot_at=excluded.snapshot_at", params![uuid::Uuid::new_v4().to_string(), network_id.to_string(), device_id.map(|id| id.to_string()), configured_instance.to_string(), key, previous.map(|old| old.stable_machine_key_fingerprint.clone()).unwrap_or_else(|| node.identity.stable_key_fingerprint.clone()), classification_name(classification), fingerprint, serialized, first.to_rfc3339(), snapshot_at.to_rfc3339(), snapshot_at.to_rfc3339()])?;
                if changed
                    && previous.is_some_and(|old| {
                        old.adoption_state == AdoptionState::PendingDeviceCredentialProof
                    })
                {
                    let reason = match classification {
                        ObservationClassification::ProviderExpired => "provider_expired",
                        ObservationClassification::IdentityConflict => "identity_conflict",
                        _ => "observation_changed",
                    };
                    terminalize_pending_adoption_for_observation(
                        tx,
                        network_id,
                        previous.expect("checked above").canonical_provider_node_id.as_str(),
                        previous.expect("checked above").semantic_generation + 1,
                        reason,
                        snapshot_at,
                        &actor,
                    )?;
                }
            }
            for (key, old) in &existing {
                if !incoming_ids.contains(key) && old.classification != ObservationClassification::ProviderMissing {
                    semantic_change = true;
                    changes.push((key.clone(), "provider_node_missing"));
                    tx.execute("UPDATE provider_observations SET classification='provider_missing',semantic_generation=semantic_generation+1,snapshot_at=?3 WHERE provider_instance_id=?1 AND provider_node_id=?2", params![configured_instance.to_string(), key, snapshot_at.to_rfc3339()])?;
                    if old.adoption_state == AdoptionState::PendingDeviceCredentialProof {
                        terminalize_pending_adoption_for_observation(
                            tx,
                            network_id,
                            key,
                            old.semantic_generation + 1,
                            "provider_missing",
                            snapshot_at,
                            &actor,
                        )?;
                    }
                }
            }
            if semantic_change {
                store.append_audit(tx, Some(network_id), None, actor.clone(), "provider_reconciliation_started", "success", None, &SanitizedMetadata::empty())?;
                for (_, kind) in &changes {
                    store.append_audit(tx, Some(network_id), None, actor.clone(), kind, "success", None, &SanitizedMetadata::empty())?;
                }
                store.append_audit(tx, Some(network_id), None, actor, "provider_reconciliation_completed", "success", None, &SanitizedMetadata::empty())?;
            }
            tx.execute("UPDATE provider_imports SET compatibility=?2,provider_version=?3,last_success_at=?4,last_attempt_at=?4,last_failure_kind=NULL,last_failure_detail=NULL WHERE network_id=?1", params![network_id.to_string(), compatibility_name(inspection.compatibility), inspection.provider_version, snapshot_at.to_rfc3339()])?;
            Ok(())
        })?;
        self.reconciliation_report(network_id)
            .map_err(ReconciliationFailure::State)
    }

    /// Return persisted, sanitized doctor state, including outages without
    /// discarding the last successful inventory snapshot.
    pub fn reconciliation_report(
        &self,
        network_id: NetworkId,
    ) -> Result<ReconciliationReport, StateError> {
        let connection = self.connection.borrow();
        let mut counts = BTreeMap::<String, u64>::new();
        let mut statement = connection.prepare(
            "SELECT classification,COUNT(*) FROM provider_observations WHERE network_id=?1 GROUP BY classification",
        )?;
        let rows = statement.query_map([network_id.to_string()], |row| {
            Ok((row.get::<_, String>(0)?, row.get::<_, u64>(1)?))
        })?;
        for row in rows {
            let (classification, count) = row?;
            counts.insert(classification, count);
        }
        let (compatibility, provider_version, last_success, last_attempt, failure_kind, failure_detail) = connection
            .query_row(
                "SELECT compatibility,provider_version,last_success_at,last_attempt_at,last_failure_kind,last_failure_detail FROM provider_imports WHERE network_id=?1",
                [network_id.to_string()],
                |row| Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, Option<String>>(2)?,
                    row.get::<_, Option<String>>(3)?,
                    row.get::<_, Option<String>>(4)?,
                    row.get::<_, Option<String>>(5)?,
                )),
            )
            .optional()?
            .ok_or_else(|| StateError::NotFound(network_id.to_string()))?;
        let parse_time = |value: Option<String>| -> Result<Option<DateTime<Utc>>, StateError> {
            value
                .map(|value| value.parse::<DateTime<Utc>>())
                .transpose()
                .map_err(|_| StateError::Conflict("invalid persisted reconciliation time".into()))
        };
        let provider_state = match failure_kind.as_deref() {
            None if last_success.is_some() => ProviderReconciliationState::Healthy,
            None => ProviderReconciliationState::NeverReconciled,
            Some("unreachable") => ProviderReconciliationState::Unreachable,
            Some("authentication") => ProviderReconciliationState::AuthenticationFailed,
            Some("incompatible") => ProviderReconciliationState::Incompatible,
            Some("malformed") => ProviderReconciliationState::Malformed,
            Some("identity_conflict") => ProviderReconciliationState::IdentityConflict,
            Some("state") => ProviderReconciliationState::StateFailure,
            Some(_) => ProviderReconciliationState::StateFailure,
        };
        Ok(ReconciliationReport {
            network_id,
            provider_state,
            provider_compatibility: parse_compatibility(&compatibility)?,
            provider_version,
            last_attempted_reconciliation: parse_time(last_attempt)?,
            last_successful_reconciliation: parse_time(last_success)?,
            observed_count: counts.values().copied().sum(),
            discovered_unmanaged_count: *counts.get("discovered_unmanaged").unwrap_or(&0),
            provider_missing_count: *counts.get("provider_missing").unwrap_or(&0),
            provider_expired_count: *counts.get("provider_expired").unwrap_or(&0),
            identity_conflict_count: *counts.get("identity_conflict").unwrap_or(&0),
            quarantined_count: *counts.get("quarantined").unwrap_or(&0),
            active_trusted_count: *counts.get("active").unwrap_or(&0),
            warnings: failure_detail.into_iter().collect(),
            provider_mutation_enabled: false,
        })
    }

    pub fn provider_observations(
        &self,
        network_id: NetworkId,
    ) -> Result<Vec<ProviderObservation>, StateError> {
        load_observations(&self.connection.borrow(), network_id)
            .map(|entries| entries.into_values().collect())
    }

    /// Return one deterministic, provider-node-ID ordered page of the durable
    /// current observation inventory. This is a read-only best-effort view: it
    /// neither reconciles a provider nor records an audit event.
    pub fn provider_observation_page(
        &self,
        network_id: NetworkId,
        after_provider_node_id: Option<&str>,
        limit: usize,
    ) -> Result<Vec<ProviderObservation>, StateError> {
        let limit = limit.min(PROVIDER_OBSERVATION_PAGE_MAX);
        if limit == 0 {
            return Ok(Vec::new());
        }
        let network = self.network(network_id)?;
        let observations = load_observation_page(
            &self.connection.borrow(),
            network_id,
            after_provider_node_id,
            limit,
        )?;
        let mut page = Vec::with_capacity(observations.len());
        for observation in observations {
            if observation.provider_instance_id != network.provider_instance_id
                || observation.node.identity.provider_instance_id
                    != observation.provider_instance_id
                || observation.node.identity.node_id.to_string()
                    != observation.canonical_provider_node_id
                || !valid_sha256_fingerprint(&observation.stable_machine_key_fingerprint)
                || observation.node.identity.stable_key_fingerprint
                    != observation.stable_machine_key_fingerprint
                || semantic_fingerprint(&observation.node)? != observation.semantic_fingerprint
            {
                return Err(StateError::Conflict(
                    "provider observation identity is inconsistent".into(),
                ));
            }
            page.push(observation);
        }
        Ok(page)
    }

    pub fn device_count(&self, network_id: NetworkId) -> Result<u64, StateError> {
        self.count("devices", network_id)
    }
    pub fn keryx_binding_count(&self, network_id: NetworkId) -> Result<u64, StateError> {
        self.count("keryx_bindings", network_id)
    }
    /// N2A has no Fleet projection table or behavior; this truthful count is zero.
    pub fn fleet_projection_count(&self, _network_id: NetworkId) -> Result<u64, StateError> {
        Ok(0)
    }

    pub fn database_text_dump_for_test(&self) -> Result<String, StateError> {
        let connection = self.connection.borrow();
        let mut output = String::new();
        for query in [
            "SELECT record_json || secret_verifier FROM invitations",
            "SELECT record_json || display_name || COALESCE(provider_key_fingerprint,'') FROM devices",
            "SELECT metadata_json || event_kind || actor_source || COALESCE(actor_id,'') FROM audit_events",
            "SELECT server_url || opaque_secret_reference || compatibility_pin || COALESCE(last_failure_detail,'') FROM provider_imports",
            "SELECT stable_key_fingerprint || semantic_fingerprint || normalized_json FROM provider_observations",
            "SELECT provider_principal_id || roles_json || constraints_json || last_redemption_metadata_json FROM n4_invitation_details",
            "SELECT provider_principal_id || create_request_id || COALESCE(configuration_fingerprint,'') FROM n4_join_session_dispatches",
            "SELECT provider_principal_id || approved_tags_json || safe_correlation_json FROM n4_provider_credential_metadata",
        ] {
            let mut statement = connection.prepare(query)?;
            let rows = statement.query_map([], |row| row.get::<_, String>(0))?;
            for row in rows {
                output.push_str(&row?);
            }
        }
        Ok(output)
    }

    fn reconciliation_import_config(
        &self,
        network_id: NetworkId,
    ) -> Result<ReconciliationImportConfig, StateError> {
        let row = self
            .connection
            .borrow()
            .query_row(
                "SELECT pi.provider_instance_id,n.provider_kind,pi.compatibility_pin,
                        pi.read_only,pi.mutation_allowed
                 FROM provider_imports pi
                 JOIN networks n ON n.network_id=pi.network_id
                 WHERE pi.network_id=?1",
                [network_id.to_string()],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, bool>(3)?,
                        row.get::<_, bool>(4)?,
                    ))
                },
            )
            .optional()?
            .ok_or_else(|| StateError::NotFound(network_id.to_string()))?;
        let provider_instance_id = ProviderInstanceId::parse(&row.0)
            .map_err(|error| StateError::Conflict(error.to_string()))?;
        if !row.3 || row.4 {
            return Err(StateError::Conflict(
                "persisted provider import is not read-only".into(),
            ));
        }
        let provider_name = match row.1.as_str() {
            "headscale" => "headscale",
            "tailscale" => "tailscale",
            _ => {
                return Err(StateError::Conflict(
                    "unsupported persisted provider kind".into(),
                ));
            }
        };
        Ok(ReconciliationImportConfig {
            provider_instance_id,
            provider_name,
            compatibility_pin: row.2,
        })
    }

    fn import_config(
        &self,
        network_id: NetworkId,
    ) -> Result<(ProviderInstanceId, HeadscaleImportConfig), StateError> {
        let row = self.connection.borrow().query_row("SELECT provider_instance_id,server_url,opaque_secret_reference,compatibility_pin,custom_root_ca_sha256 FROM provider_imports WHERE network_id=?1", [network_id.to_string()], |row| Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?, row.get::<_, String>(2)?, row.get::<_, String>(3)?, row.get::<_, Option<String>>(4)?))).optional()?.ok_or_else(|| StateError::NotFound(network_id.to_string()))?;
        let instance = ProviderInstanceId::parse(&row.0)
            .map_err(|error| StateError::Conflict(error.to_string()))?;
        let mut config = HeadscaleImportConfig::new(
            row.1,
            instance,
            row.2,
            row.3,
            TlsVerificationPolicy::Verify,
        )?;
        if let Some(fingerprint) = row.4 {
            config = config.with_custom_root_ca_sha256(fingerprint)?;
        }
        Ok((instance, config))
    }

    fn record_failure_for(
        &self,
        network_id: NetworkId,
        at: DateTime<Utc>,
        failure: &ReconciliationFailure,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        let (kind, detail) = match failure {
            ReconciliationFailure::Unreachable => ("unreachable", "provider unreachable"),
            ReconciliationFailure::AuthenticationFailed => {
                ("authentication", "provider authentication failed")
            }
            ReconciliationFailure::Incompatible => {
                ("incompatible", "provider compatibility rejected")
            }
            ReconciliationFailure::Malformed => ("malformed", "provider response malformed"),
            ReconciliationFailure::IdentityConflict => {
                ("identity_conflict", "provider identity conflict")
            }
            ReconciliationFailure::State(_) => ("state", "local state failure"),
        };
        self.record_provider_failure(network_id, at, kind, detail, actor)
    }

    fn record_provider_failure(
        &self,
        network_id: NetworkId,
        at: DateTime<Utc>,
        kind: &str,
        detail: &str,
        actor: AuditActor,
    ) -> Result<(), StateError> {
        self.transactional(|tx, store| {
            let previous = tx
                .query_row(
                    "SELECT last_failure_kind FROM provider_imports WHERE network_id=?1",
                    [network_id.to_string()],
                    |row| row.get::<_, Option<String>>(0),
                )
                .optional()?
                .ok_or_else(|| StateError::NotFound(network_id.to_string()))?;
            tx.execute("UPDATE provider_imports SET last_attempt_at=?2,last_failure_kind=?3,last_failure_detail=?4 WHERE network_id=?1", params![network_id.to_string(), at.to_rfc3339(), kind, detail])?;
            if previous.as_deref() != Some(kind) {
                store.append_audit(
                    tx,
                    Some(network_id),
                    None,
                    actor,
                    "provider_reconciliation_failed",
                    kind,
                    None,
                    &SanitizedMetadata::empty(),
                )?;
            }
            Ok(())
        })
    }

    fn count(&self, table: &str, network_id: NetworkId) -> Result<u64, StateError> {
        let query = match table {
            "devices" => "SELECT COUNT(*) FROM devices WHERE network_id=?1",
            "keryx_bindings" => "SELECT COUNT(*) FROM keryx_bindings WHERE network_id=?1",
            _ => return Err(StateError::Conflict("unknown count table".into())),
        };
        Ok(self
            .connection
            .borrow()
            .query_row(query, [network_id.to_string()], |row| row.get(0))?)
    }

    fn transactional<T>(
        &self,
        operation: impl FnOnce(&Transaction<'_>, &Self) -> Result<T, StateError>,
    ) -> Result<T, StateError> {
        let mut connection = self.connection.borrow_mut();
        let tx = connection.transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
        match operation(&tx, self) {
            Ok(value) => {
                tx.commit()?;
                Ok(value)
            }
            Err(error) => Err(error),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn append_n4_audit(
        &self,
        tx: &Transaction<'_>,
        invitation_id: nodescale_domain::InvitationId,
        join_session_id: Option<JoinSessionId>,
        action_id: &str,
        actor: AuditActor,
        kind: &str,
        outcome: &str,
        metadata: &SanitizedMetadata,
    ) -> Result<bool, StateError> {
        if self.fail_before_audit.get()
            || (self.fail_before_n4_confirmation_audit.get() && kind == "invitation_redeemed")
        {
            return Err(StateError::InjectedFailure);
        }
        let exists: bool = tx.query_row(
            "SELECT EXISTS(SELECT 1 FROM n4_audit_correlations WHERE action_id=?1 AND event_kind=?2)",
            params![action_id, kind],
            |row| row.get(0),
        )?;
        if exists {
            return Ok(false);
        }
        let network_id: String = tx.query_row(
            "SELECT network_id FROM n4_invitation_details WHERE invitation_id=?1",
            [invitation_id.to_string()],
            |row| row.get(0),
        )?;
        let event_id = AuditEventId::new();
        tx.execute("INSERT INTO audit_events (event_id,timestamp,network_id,device_id,actor_source,actor_id,event_kind,outcome,generation,metadata_json) VALUES (?1,?2,?3,NULL,?4,?5,?6,?7,NULL,?8)", params![event_id.to_string(), Utc::now().to_rfc3339(), network_id, actor.source, actor.actor_id, kind, outcome, metadata.json()?])?;
        tx.execute("INSERT INTO n4_audit_correlations (event_id,invitation_id,join_session_id,action_id,event_kind) VALUES (?1,?2,?3,?4,?5)", params![event_id.to_string(), invitation_id.to_string(), join_session_id.map(|id| id.to_string()), action_id, kind])?;
        Ok(true)
    }

    #[allow(clippy::too_many_arguments)]
    fn append_audit(
        &self,
        tx: &Transaction<'_>,
        network_id: Option<NetworkId>,
        device_id: Option<DeviceId>,
        actor: AuditActor,
        kind: &str,
        outcome: &str,
        generation: Option<Generation>,
        metadata: &SanitizedMetadata,
    ) -> Result<(), StateError> {
        if self.fail_before_audit.get() {
            return Err(StateError::InjectedFailure);
        }
        tx.execute("INSERT INTO audit_events (event_id,timestamp,network_id,device_id,actor_source,actor_id,event_kind,outcome,generation,metadata_json) VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10)", params![AuditEventId::new().to_string(), Utc::now().to_rfc3339(), network_id.map(|id| id.to_string()), device_id.map(|id| id.to_string()), actor.source, actor.actor_id, kind, outcome, generation.map(to_i64).transpose()?, metadata.json()?])?;
        Ok(())
    }
}

fn terminalize_pending_adoption_for_observation(
    tx: &Transaction<'_>,
    network_id: NetworkId,
    provider_node_id: &str,
    observation_generation: u64,
    reason: &str,
    now: DateTime<Utc>,
    actor: &AuditActor,
) -> Result<(), StateError> {
    type PendingAction = (String, String, u64, String, String, u64);
    let pending = tx
        .query_row(
            "SELECT action_id,authority_id,authority_generation,provider_instance_id,provider_node_id,proof_generation FROM n5_adoption_actions WHERE network_id=?1 AND provider_node_id=?2 AND action_state='proof_pending'",
            params![network_id.to_string(), provider_node_id],
            |row| -> rusqlite::Result<PendingAction> {
                Ok((
                    row.get(0)?,
                    row.get(1)?,
                    row.get(2)?,
                    row.get(3)?,
                    row.get(4)?,
                    row.get(5)?,
                ))
            },
        )
        .optional()?;
    let Some((
        action_id,
        authority_id,
        authority_generation,
        provider_instance_id,
        action_provider_node_id,
        proof_generation,
    )) = pending
    else {
        return Ok(());
    };

    let decision_id = uuid::Uuid::new_v4().to_string();
    let audit_event_id = AuditEventId::new().to_string();
    let safe_correlation_digest = format!("sha256:{:x}", Sha256::digest(action_id.as_bytes()));
    tx.execute(
        "INSERT INTO audit_events (event_id,timestamp,network_id,device_id,actor_source,actor_id,event_kind,outcome,generation,metadata_json) VALUES (?1,?2,?3,NULL,?4,?5,'device.adoption_action_conflicted','success',?6,'{}')",
        params![
            audit_event_id,
            now.to_rfc3339(),
            network_id.to_string(),
            actor.source,
            actor.actor_id,
            i64::try_from(observation_generation).map_err(|_| {
                StateError::Conflict("observation generation exceeds SQLite integer range".into())
            })?,
        ],
    )?;
    tx.execute(
        "INSERT INTO n5_adoption_decisions (decision_id,action_id,proof_operation_id,audit_event_id,decision_kind,prior_action_state,new_action_state,authority_id,authority_generation,network_id,provider_instance_id,provider_node_id,observation_generation,proof_generation,evidence_id,device_id,provider_binding_id,safe_correlation_digest,reason_code,decided_at_ms) VALUES (?1,?2,NULL,?3,'conflict','proof_pending','conflicted',?4,?5,?6,?7,?8,?9,?10,NULL,NULL,NULL,?11,?12,?13)",
        params![
            decision_id,
            action_id,
            audit_event_id,
            authority_id,
            authority_generation,
            network_id.to_string(),
            provider_instance_id,
            action_provider_node_id,
            observation_generation,
            proof_generation,
            safe_correlation_digest,
            reason,
            now.timestamp_millis(),
        ],
    )?;
    tx.execute(
        "UPDATE provider_observations SET adoption_state='unmanaged' WHERE network_id=?1 AND provider_node_id=?2 AND adoption_state='pending_device_credential_proof'",
        params![network_id.to_string(), provider_node_id],
    )?;
    Ok(())
}

fn validate_snapshot(
    mut nodes: Vec<ProviderNode>,
    expected_instance: ProviderInstanceId,
) -> Result<Vec<ProviderNode>, ReconciliationFailure> {
    nodes.sort_by(|left, right| left.identity.node_id.cmp(&right.identity.node_id));
    let mut ids = BTreeSet::new();
    for node in &nodes {
        if node.identity.provider_instance_id != expected_instance
            || !ids.insert(node.identity.node_id.to_string())
        {
            return Err(ReconciliationFailure::IdentityConflict);
        }
    }
    Ok(nodes)
}

fn insert_new_observation(
    tx: &Transaction<'_>,
    network_id: NetworkId,
    provider_instance_id: ProviderInstanceId,
    node: &ProviderNode,
    classification: ObservationClassification,
    snapshot_at: DateTime<Utc>,
) -> Result<(), StateError> {
    tx.execute(
        "INSERT INTO provider_observations (observation_id,network_id,device_id,provider_instance_id,provider_node_id,stable_key_fingerprint,classification,adoption_state,semantic_fingerprint,normalized_json,first_observed_at,last_observed_at,snapshot_at) VALUES (?1,?2,NULL,?3,?4,?5,?6,'unmanaged',?7,?8,?9,?9,?9)",
        params![
            uuid::Uuid::new_v4().to_string(),
            network_id.to_string(),
            provider_instance_id.to_string(),
            node.identity.node_id.to_string(),
            node.identity.stable_key_fingerprint,
            classification_name(classification),
            semantic_fingerprint(node)?,
            serde_json::to_string(node)?,
            snapshot_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

fn validate_inspection(
    inspection: &ServerInspection,
    config: &HeadscaleImportConfig,
) -> Result<(), ReconciliationFailure> {
    validate_read_only_inspection(
        inspection,
        config.provider_instance_id,
        "headscale",
        &config.compatibility_pin,
    )
}

fn validate_read_only_inspection(
    inspection: &ServerInspection,
    provider_instance_id: ProviderInstanceId,
    provider_name: &str,
    compatibility_pin: &str,
) -> Result<(), ReconciliationFailure> {
    if inspection.provider_name != provider_name
        || inspection.instance_id != provider_instance_id
        || inspection.mutation_allowed
        || !matches!(
            inspection.compatibility,
            CompatibilityStatus::Compatible | CompatibilityStatus::CompatibleWithConstraints
        )
        || inspection.provider_version.trim_start_matches('v')
            != compatibility_pin.trim_start_matches('v')
    {
        return Err(ReconciliationFailure::Incompatible);
    }
    Ok(())
}

fn map_provider_failure(error: ProviderError) -> ReconciliationFailure {
    match error {
        ProviderError::AuthenticationFailed => ReconciliationFailure::AuthenticationFailed,
        ProviderError::MalformedResponse(_) => ReconciliationFailure::Malformed,
        ProviderError::Conflict(_) => ReconciliationFailure::IdentityConflict,
        ProviderError::Unsupported(_) | ProviderError::Rejected(_) => {
            ReconciliationFailure::Incompatible
        }
        ProviderError::Unreachable(_)
        | ProviderError::Timeout
        | ProviderError::TlsFailure
        | ProviderError::AmbiguousMutation(_) => ReconciliationFailure::Unreachable,
    }
}

fn next_classification(
    previous: ObservationClassification,
    node: &ProviderNode,
) -> ObservationClassification {
    if node.expired {
        return ObservationClassification::ProviderExpired;
    }
    match previous {
        ObservationClassification::Active
        | ObservationClassification::ExpectedJoining
        | ObservationClassification::Quarantined
        | ObservationClassification::Revoked => previous,
        _ => ObservationClassification::DiscoveredUnmanaged,
    }
}

fn semantic_fingerprint(node: &ProviderNode) -> Result<String, StateError> {
    let mut stable = node.clone();
    stable.observed_at = DateTime::parse_from_rfc3339("1970-01-01T00:00:00Z")
        .expect("fixed timestamp")
        .with_timezone(&Utc);
    let bytes = serde_json::to_vec(&stable)?;
    Ok(format!("sha256:{:x}", Sha256::digest(bytes)))
}

fn compatibility_name(value: CompatibilityStatus) -> &'static str {
    match value {
        CompatibilityStatus::Compatible => "compatible",
        CompatibilityStatus::CompatibleWithConstraints => "compatible_with_constraints",
        CompatibilityStatus::ReadOnlyDegraded => "read_only_degraded",
        CompatibilityStatus::Unsupported => "unsupported",
        CompatibilityStatus::Unreachable => "unreachable",
        CompatibilityStatus::AuthenticationFailed => "authentication_failed",
    }
}

fn parse_compatibility(value: &str) -> Result<CompatibilityStatus, StateError> {
    match value {
        "compatible" => Ok(CompatibilityStatus::Compatible),
        "compatible_with_constraints" => Ok(CompatibilityStatus::CompatibleWithConstraints),
        "read_only_degraded" => Ok(CompatibilityStatus::ReadOnlyDegraded),
        "unsupported" => Ok(CompatibilityStatus::Unsupported),
        "unreachable" => Ok(CompatibilityStatus::Unreachable),
        "authentication_failed" => Ok(CompatibilityStatus::AuthenticationFailed),
        _ => Err(StateError::Conflict(
            "unknown persisted provider compatibility".into(),
        )),
    }
}

fn classification_name(value: ObservationClassification) -> &'static str {
    match value {
        ObservationClassification::ExpectedJoining => "expected_joining",
        ObservationClassification::DiscoveredUnmanaged => "discovered_unmanaged",
        ObservationClassification::Active => "active",
        ObservationClassification::ProviderMissing => "provider_missing",
        ObservationClassification::ProviderExpired => "provider_expired",
        ObservationClassification::ProviderRemoved => "provider_removed",
        ObservationClassification::IdentityConflict => "identity_conflict",
        ObservationClassification::Quarantined => "quarantined",
        ObservationClassification::Revoked => "revoked",
    }
}

fn parse_adoption_state(value: &str) -> Result<AdoptionState, StateError> {
    match value {
        "unmanaged" => Ok(AdoptionState::Unmanaged),
        "pending_device_credential_proof" => Ok(AdoptionState::PendingDeviceCredentialProof),
        "adopted" => Ok(AdoptionState::Adopted),
        _ => Err(StateError::Conflict(
            "unknown provider observation adoption state".into(),
        )),
    }
}

fn parse_classification(value: &str) -> Result<ObservationClassification, StateError> {
    match value {
        "expected_joining" => Ok(ObservationClassification::ExpectedJoining),
        "discovered_unmanaged" => Ok(ObservationClassification::DiscoveredUnmanaged),
        "active" => Ok(ObservationClassification::Active),
        "provider_missing" => Ok(ObservationClassification::ProviderMissing),
        "provider_expired" => Ok(ObservationClassification::ProviderExpired),
        "provider_removed" => Ok(ObservationClassification::ProviderRemoved),
        "identity_conflict" => Ok(ObservationClassification::IdentityConflict),
        "quarantined" => Ok(ObservationClassification::Quarantined),
        "revoked" => Ok(ObservationClassification::Revoked),
        _ => Err(StateError::Conflict(
            "unknown provider observation classification".into(),
        )),
    }
}

type RawProviderObservation = (
    Option<String>,
    String,
    String,
    String,
    String,
    String,
    String,
    u64,
    String,
    String,
    String,
    String,
);

fn read_raw_observation(row: &rusqlite::Row<'_>) -> rusqlite::Result<RawProviderObservation> {
    Ok((
        row.get(0)?,
        row.get(1)?,
        row.get(2)?,
        row.get(3)?,
        row.get(4)?,
        row.get(5)?,
        row.get(6)?,
        row.get(7)?,
        row.get(8)?,
        row.get(9)?,
        row.get(10)?,
        row.get(11)?,
    ))
}

fn decode_observation(
    network_id: NetworkId,
    row: RawProviderObservation,
) -> Result<ProviderObservation, StateError> {
    let (
        device_id,
        provider_instance_id,
        provider_node_id,
        fingerprint,
        classification,
        adoption_state,
        semantic_fingerprint,
        semantic_generation,
        normalized_json,
        first,
        last,
        snapshot,
    ) = row;
    let device_id = device_id
        .map(|value| DeviceId::parse(&value))
        .transpose()
        .map_err(|error| StateError::Conflict(error.to_string()))?;
    let provider_instance_id = ProviderInstanceId::parse(&provider_instance_id)
        .map_err(|error| StateError::Conflict(error.to_string()))?;
    let node = serde_json::from_str(&normalized_json)?;
    let first_observed_at = first
        .parse::<DateTime<Utc>>()
        .map_err(|_| StateError::Conflict("invalid observation timestamp".into()))?;
    let last_observed_at = last
        .parse::<DateTime<Utc>>()
        .map_err(|_| StateError::Conflict("invalid observation timestamp".into()))?;
    let snapshot_at = snapshot
        .parse::<DateTime<Utc>>()
        .map_err(|_| StateError::Conflict("invalid observation timestamp".into()))?;
    Ok(ProviderObservation {
        network_id,
        device_id,
        provider_instance_id,
        canonical_provider_node_id: provider_node_id,
        stable_machine_key_fingerprint: fingerprint,
        node,
        classification: parse_classification(&classification)?,
        adoption_state: parse_adoption_state(&adoption_state)?,
        semantic_fingerprint,
        semantic_generation,
        first_observed_at,
        last_observed_at,
        snapshot_at,
    })
}

fn load_observations(
    connection: &Connection,
    network_id: NetworkId,
) -> Result<BTreeMap<String, ProviderObservation>, StateError> {
    let mut statement = connection.prepare("SELECT device_id,provider_instance_id,provider_node_id,stable_key_fingerprint,classification,adoption_state,semantic_fingerprint,semantic_generation,normalized_json,first_observed_at,last_observed_at,snapshot_at FROM provider_observations WHERE network_id=?1 ORDER BY provider_node_id")?;
    let rows = statement.query_map([network_id.to_string()], read_raw_observation)?;
    let mut observations = BTreeMap::new();
    for row in rows {
        let observation = decode_observation(network_id, row?)?;
        observations.insert(observation.canonical_provider_node_id.clone(), observation);
    }
    Ok(observations)
}

fn load_observation_page(
    connection: &Connection,
    network_id: NetworkId,
    after_provider_node_id: Option<&str>,
    limit: usize,
) -> Result<Vec<ProviderObservation>, StateError> {
    let mut statement = connection.prepare("SELECT device_id,provider_instance_id,provider_node_id,stable_key_fingerprint,classification,adoption_state,semantic_fingerprint,semantic_generation,normalized_json,first_observed_at,last_observed_at,snapshot_at FROM provider_observations WHERE network_id=?1 AND (?2 IS NULL OR provider_node_id>?2) ORDER BY provider_node_id LIMIT ?3")?;
    let rows = statement.query_map(
        params![
            network_id.to_string(),
            after_provider_node_id,
            i64::try_from(limit)
                .map_err(|_| StateError::Conflict("observation page limit is invalid".into()))?
        ],
        read_raw_observation,
    )?;
    rows.map(|row| decode_observation(network_id, row?))
        .collect()
}

fn validate_next(expected: Generation, next: Generation) -> Result<(), StateError> {
    if next.get() <= expected.get() {
        return Err(StateError::Conflict(
            "generation must advance monotonically".into(),
        ));
    }
    Ok(())
}

fn stale_network_generation(
    tx: &Transaction<'_>,
    network_id: NetworkId,
    expected: Generation,
) -> Result<StateError, StateError> {
    let actual = tx
        .query_row(
            "SELECT generation FROM membership_generations WHERE network_id=?1",
            [network_id.to_string()],
            |row| row.get::<_, u64>(0),
        )
        .optional()?
        .ok_or_else(|| StateError::NotFound(network_id.to_string()))?;
    Ok(StateError::StaleGeneration {
        expected: expected.get(),
        actual,
    })
}

fn generation(value: u64) -> Result<Generation, StateError> {
    Generation::new(value).map_err(|error| StateError::Conflict(error.to_string()))
}
fn to_i64(value: Generation) -> Result<i64, StateError> {
    i64::try_from(value.get())
        .map_err(|_| StateError::Conflict("generation exceeds SQLite integer range".into()))
}
fn valid_sha256_fingerprint(value: &str) -> bool {
    value.len() == 71
        && value.starts_with("sha256:")
        && value[7..]
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
fn mutation_capability_name(value: ProviderMutationCapability) -> &'static str {
    match value {
        ProviderMutationCapability::EnsureNetworkPrincipal => "EnsureNetworkPrincipal",
        ProviderMutationCapability::CreateJoinCredential => "CreateJoinCredential",
        ProviderMutationCapability::InvalidateJoinCredential => "InvalidateJoinCredential",
        ProviderMutationCapability::ReplaceNodeTags => "ReplaceNodeTags",
        ProviderMutationCapability::ExpireNode => "ExpireNode",
        ProviderMutationCapability::DeleteNode => "DeleteNode",
        ProviderMutationCapability::ManagePolicy => "ManagePolicy",
    }
}
fn policy_mode_name(value: MutationPolicyMode) -> &'static str {
    match value {
        MutationPolicyMode::Database => "database",
        MutationPolicyMode::File => "file",
        MutationPolicyMode::Unknown => "unknown",
    }
}
fn parse_policy_mode(value: &str) -> Result<MutationPolicyMode, StateError> {
    match value {
        "database" => Ok(MutationPolicyMode::Database),
        "file" => Ok(MutationPolicyMode::File),
        "unknown" => Ok(MutationPolicyMode::Unknown),
        _ => Err(StateError::MutationAuthorizationDenied(
            "invalid policy mode",
        )),
    }
}
fn safe_identifier(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 255
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b':' | b'.'))
}
fn n4_approved_tag(value: &str) -> bool {
    matches!(
        value,
        "tag:nodescale-node"
            | "tag:nodescale-worker"
            | "tag:nodescale-controller"
            | "tag:nodescale-profile-host"
            | "tag:nodescale-observer"
            | "tag:nodescale-admin"
    )
}
fn lower(value: &str) -> String {
    value.to_ascii_lowercase()
}

fn map_constraint(error: rusqlite::Error) -> StateError {
    if matches!(&error, rusqlite::Error::SqliteFailure(details, _) if details.code == ErrorCode::ConstraintViolation)
    {
        StateError::Conflict(error.to_string())
    } else {
        StateError::Sqlite(error)
    }
}

fn validate_metadata(value: &Value) -> Result<(), StateError> {
    const BANNED_KEYS: &[&str] = &[
        "secret",
        "token",
        "password",
        "credential",
        "api_key",
        "private_key",
        "nonce",
    ];
    match value {
        Value::Object(map) => {
            for (key, nested) in map {
                let normalized = key.to_ascii_lowercase();
                if BANNED_KEYS.iter().any(|banned| normalized.contains(banned)) {
                    return Err(StateError::UnsafeAuditMetadata(key.clone()));
                }
                if n6_audit_secret_value(key) {
                    return Err(StateError::UnsafeAuditMetadata("N6 secret key".into()));
                }
                validate_metadata(nested)?;
            }
        }
        Value::Array(values) => {
            for nested in values {
                validate_metadata(nested)?;
            }
        }
        Value::String(value) => {
            if value.len() > 1024 {
                return Err(StateError::UnsafeAuditMetadata("oversized string".into()));
            }
            if n6_audit_secret_value(value) {
                return Err(StateError::UnsafeAuditMetadata("N6 secret value".into()));
            }
        }
        _ => {}
    }
    Ok(())
}

fn n6_audit_secret_value(value: &str) -> bool {
    const BINDING_NONCE_PREFIX: &str = "nsbind_";
    const BINDING_NONCE_ENCODED_LEN: usize = 43;
    const N6_VERIFIER_PREFIX: &str = "$argon2id$v=19$m=19456,t=2,p=1$";

    let canonical_nonce = value
        .strip_prefix(BINDING_NONCE_PREFIX)
        .is_some_and(|encoded| {
            encoded.len() == BINDING_NONCE_ENCODED_LEN
                && encoded
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_'))
                && encoded.as_bytes().last().is_some_and(|byte| {
                    matches!(
                        byte,
                        b'A' | b'E'
                            | b'I'
                            | b'M'
                            | b'Q'
                            | b'U'
                            | b'Y'
                            | b'c'
                            | b'g'
                            | b'k'
                            | b'o'
                            | b's'
                            | b'w'
                            | b'0'
                            | b'4'
                            | b'8'
                    )
                })
        });

    canonical_nonce || value.starts_with(N6_VERIFIER_PREFIX)
}
