//
// Copyright 2020 Signal Messenger, LLC. LLC.
// SPDX-License-Identifier: AGPL-3.0-only
//

mod keys;time::SystemTime;
mod params;
use rand::{CryptoRng, Rng};
use rand::{CryptoRng, Rng};
use crate::ratchet::{AliceSignalProtocolParameters, BobSignalProtocolParameters};
pub(crate) use self::keys::{ChainKey, MessageKeyGenerator, RootKey};
pub use self::params::{AliceSignalProtocolParameters, BobSignalProtocolParameters};
use crate::protocol::{CIPHERTEXT_MESSAGE_CURRENT_VERSION, CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION};
use crate::state::SessionState;KeySignalMessage, PreKeyStore, ProtocolAddress, Result,
use crate::{KeyPair, Result, SessionRecord};colError, SignedPreKeyStore,
use log::debug;};

fn derive_keys(has_kyber: bool, secret_input: &[u8]) -> (RootKey, ChainKey) {
    let label = if has_kyber {
        b"WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".as_slice()key_id: Option<PreKeyId>,
    } else {KyberPreKeyId>,
        b"WhisperText".as_slice()
    };
    derive_keys_with_label(label, secret_input)*
}These functions are on SessionBuilder in Java

fn message_version(has_kyber: bool) -> u8 {ionBuilder + SessionCipher at the same time causes
    if has_kyber { has no actual state beyond
        CIPHERTEXT_MESSAGE_CURRENT_VERSIONe to the various data stores, instead the functions are
    } else {
        CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION
    }
}pub async fn process_prekey(

fn derive_keys_with_label(label: &[u8], secret_input: &[u8]) -> (RootKey, ChainKey) {ddress,
    let mut secrets = [0; 64];
    hkdf::Hkdf::<sha2::Sha256>::new(None, secret_input)yKeyStore,
        .expand(label, &mut secrets)ore,
        .expect("valid length");
    let (root_key_bytes, chain_key_bytes) = secrets.split_at(32);    kyber_prekey_store: &dyn KyberPreKeyStore,

    let root_key = RootKey::new(root_key_bytes.try_into().expect("correct length"));
    let chain_key = ChainKey::new(chain_key_bytes.try_into().expect("correct length"), 0);

    debug!("Deriving keys from ratchet: chain_key={:?}", chain_key);       .is_trusted_identity(remote_address, their_identity_key, Direction::Receiving)
        .await?
    (root_key, chain_key)
}edIdentity(
ess.clone(),
pub(crate) fn initialize_alice_session<R: Rng + CryptoRng>(
    parameters: &AliceSignalProtocolParameters,
    mut csprng: &mut R,
) -> Result<SessionState> {
    let local_identity = parameters.our_identity_key_pair().identity_key();        message,

    let sending_ratchet_key = KeyPair::generate(&mut csprng);        session_record,

    let mut secrets = Vec::with_capacity(32 * 5);        kyber_prekey_store,

    secrets.extend_from_slice(&[0xFFu8; 32]); // "discontinuity bytes"        identity_store,

    let our_base_private_key = parameters.our_base_key_pair().private_key;

    secrets.extend_from_slice(
        &parameters
            .our_identity_key_pair()  .await?;
            .private_key()
            .calculate_agreement(parameters.their_signed_pre_key())?,
    );

    secrets.extend_from_slice(async fn process_prekey_impl(
        &our_base_private_key.calculate_agreement(parameters.their_identity_key().public_key())?,age,
    );
ssion_record: &mut SessionRecord,
    secrets.extend_from_slice(    signed_prekey_store: &dyn SignedPreKeyStore,
        &our_base_private_key.calculate_agreement(parameters.their_signed_pre_key())?,
    );re: &dyn PreKeyStore,

    if let Some(their_one_time_prekey) = parameters.their_one_time_pre_key() {Result<PreKeysUsed> {
        secrets    if session_record.has_session_state(
            .extend_from_slice(&our_base_private_key.calculate_agreement(their_one_time_prekey)?);
    }

    let kyber_ciphertext = parameters.their_kyber_pre_key().map(|kyber_public| { We've already setup a session for this message, letting bundled message fall through
        let (ss, ct) = kyber_public.encapsulate(); return Ok(Default::default());
        secrets.extend_from_slice(ss.as_ref());
        ct
    });
    let has_kyber = parameters.their_kyber_pre_key().is_some();        .get_signed_pre_key(message.signed_pre_key_id())

    let (root_key, chain_key) = derive_keys(has_kyber, &secrets);

    let (sending_chain_root_key, sending_chain_chain_key) = root_key.create_chain(Because async closures are unstable
        parameters.their_ratchet_key(),    let our_kyber_pre_key_pair: Option<kem::KeyPair>;
        &sending_ratchet_key.private_key,age.kyber_pre_key_id() {
    )?;me(
y_store
    debug!("Ratchet step complete: produced {} new keys", 1);_pre_key_id)

    let mut session = SessionState::new(
        message_version(has_kyber),   );
        local_identity,
        parameters.their_identity_key(),
        &sending_chain_root_key,    }
        &parameters.our_base_key_pair().public_key,
    )_id) = message.pre_key_id() {
    .with_receiver_chain(parameters.their_ratchet_key(), &chain_key)   log::info!("processing PreKey message from {}", remote_address);
    .with_sender_chain(&sending_ratchet_key, &sending_chain_chain_key);        Some(pre_key_store.get_pre_key(pre_key_id).await?.key_pair()?)

    if let Some(kyber_ciphertext) = kyber_ciphertext {       log::warn!(
        session.set_kyber_ciphertext(kyber_ciphertext);            "processing PreKey message from {} which had no one-time prekey",
    }

    Ok(session)
}

pub(crate) fn initialize_bob_session(:new(
    parameters: &BobSignalProtocolParameters,        identity_store.get_identity_key_pair().await?,
) -> Result<SessionState> {
    let local_identity = parameters.our_identity_key_pair().identity_key();        our_one_time_pre_key_pair,
r, // ratchet key
    let mut secrets = Vec::with_capacity(32 * 5);re_key_pair,

    secrets.extend_from_slice(&[0xFFu8; 32]); // "discontinuity bytes"y(),

    secrets.extend_from_slice(
        &parameters
            .our_signed_pre_key_pair()het::initialize_bob_session(&parameters)?;
            .private_key
            .calculate_agreement(parameters.their_identity_key().public_key())?,h remote identity: {:?}", remote_address);
    );
cal_registration_id().await?);            .calculate_agreement(parameters.their_base_key())?,
    secrets.extend_from_slice(w_session.set_remote_registration_id(message.registration_id());
        &parameters
            .our_identity_key_pair()te(new_session);
            .private_key()
            .calculate_agreement(parameters.their_base_key())?,
    );age.pre_key_id(),      .private_key
t(parameters.their_base_key())?,
    secrets.extend_from_slice(   );
        &parameters    Ok(pre_keys_used)
            .our_signed_pre_key_pair()
            .private_key
            .calculate_agreement(parameters.their_base_key())?,Rng + CryptoRng>(
    );lAddress,
r_base_key())?,
    if let Some(our_one_time_pre_key_pair) = parameters.our_one_time_pre_key_pair() {ty_store: &mut dyn IdentityKeyStore,
        secrets.extend_from_slice(undle: &PreKeyBundle,
            &our_one_time_pre_key_pair    now: SystemTime,
                .private_keyrng: &mut R,
                .calculate_agreement(parameters.their_base_key())?,r_pre_key_pair(),
        );_key()?;ir_kyber_ciphertext(),
    }
)) => {
    match (irection::Sending)       let ss = key_pair.secret_key.decapsulate(ciphertext)?;
        parameters.our_kyber_pre_key_pair(),
        parameters.their_kyber_ciphertext(),
    ) { => (), // Alice does not support kyber prekeys
        (Some(key_pair), Some(ciphertext)) => {mote_address.clone(),   _ => {
            let ss = key_pair.secret_key.decapsulate(ciphertext)?; provided")
            secrets.extend_from_slice(ss.as_ref());
        }
        (None, None) => (), // Alice does not support kyber prekeysr().is_some();
        _ => {        &bundle.signed_pre_key_public()?.serialize(),
            panic!("Either both or none of the kyber key pair and ciphertext can be provided")
        }    ) {
    }or::SignatureValidationFailed);    let session = SessionState::new(
    let has_kyber = parameters.our_kyber_pre_key_pair().is_some();

    let (root_key, chain_key) = derive_keys(has_kyber, &secrets);yber_pre_key_public()? {
identity_key.public_key().verify_signature(
    debug!("Ratchet step complete: produced {} new keys", 1);.as_ref(),
       bundle
    let session = SessionState::new(ratchet_key_pair(), &chain_key);
        message_version(has_kyber),                .expect("signature must be present"),
        local_identity,n)
        parameters.their_identity_key(),           return Err(SignalProtocolError::SignatureValidationFailed);
        &root_key,        }
        parameters.their_base_key(),
    )
    .with_sender_chain(parameters.our_ratchet_key_pair(), &chain_key);_record = session_storet R,
_address)
    Ok(session)_alice_session(
}sionRecord::new_fresh);

pub fn initialize_alice_session_record<R: Rng + CryptoRng>(   let our_base_key_pair = KeyPair::generate(&mut csprng);}
    parameters: &AliceSignalProtocolParameters,    let their_signed_prekey = bundle.signed_pre_key_public()?;
    csprng: &mut R,
) -> Result<SessionRecord> {_key_id()?;
    Ok(SessionRecord::new(initialize_alice_session(
        parameters, csprng,_pair().await?;?))
    )?))
}    let mut parameters = AliceSignalProtocolParameters::new(        our_identity_key_pair,        our_base_key_pair,        *their_identity_key,        their_signed_prekey,        their_signed_prekey,    );    if let Some(key) = bundle.pre_key_public()? {        parameters.set_their_one_time_pre_key(key);    }    if let Some(key) = bundle.kyber_pre_key_public()? {        parameters.set_their_kyber_pre_key(key);    }    let mut session = ratchet::initialize_alice_session(&parameters, csprng)?;    debug!("Creating new session with remote identity: {:?}", remote_address);    log::info!(        "set_unacknowledged_pre_key_message for: {} with preKeyId: {}",        remote_address,        their_one_time_prekey_id.map_or_else(|| "<none>".to_string(), |id| id.to_string())    );    session.set_unacknowledged_pre_key_message(        their_one_time_prekey_id,        bundle.signed_pre_key_id()?,        &our_base_key_pair.public_key,        now,    );    if let Some(kyber_pre_key_id) = bundle.kyber_pre_key_id()? {        session.set_unacknowledged_kyber_pre_key_id(kyber_pre_key_id);    }    session.set_local_registration_id(identity_store.get_local_registration_id().await?);    session.set_remote_registration_id(bundle.registration_id()?);    identity_store        .save_identity(remote_address, their_identity_key)        .await?;    session_record.promote_state(session);    session_store        .store_session(remote_address, &session_record)        .await?;







}    Ok(SessionRecord::new(initialize_bob_session(parameters)?))) -> Result<SessionRecord> {    parameters: &BobSignalProtocolParameters,pub fn initialize_bob_session_record(
    Ok(())
}
