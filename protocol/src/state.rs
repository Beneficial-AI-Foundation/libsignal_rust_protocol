//
// Copyright 2020 Signal Messenger, LLC.
// SPDX-License-Identifier: AGPL-3.0-only
//

mod bundle;
mod kyber_prekey;
mod prekey;
mod session;
mod signed_prekey;

pub use bundle::{PreKeyBundle, PreKeyBundleContent};
pub use kyber_prekey::{KyberPreKeyId, KyberPreKeyRecord};
pub use prekey::{PreKeyId, PreKeyRecord};
pub use session::SessionRecord;
pub(crate) use session::{InvalidSessionError, SessionState};
pub use signed_prekey::{GenericSignedPreKey, SignedPreKeyId, SignedPreKeyRecord};

// Add to state transitions
debug!("State transition: {} -> {}", previous_state, new_state);
debug!("Updating session state: session_id={}", session_id);
