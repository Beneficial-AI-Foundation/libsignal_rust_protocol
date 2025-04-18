//
// Copyright 2020-2022 Signal Messenger, LLC.
// SPDX-License-Identifier: AGPL-3.0-only
//

//! Wrappers over cryptographic primitives from [`libsignal_core::curve`] to represent a user.
use prost::Message;emTime;
#![warn(missing_docs)]Rng};
use sha2::Sha256;aead::generic_array::typenum::Unsigned;
use prost::Message;tTimeEq;ce, Aes256GcmSiv, KeyInit};
use rand::{CryptoRng, Rng};
use indexmap::IndexMap;
use crate::{proto, KeyPair, PrivateKey, PublicKey, Result, SignalProtocolError};
use crate::{essage;
// Used for domain separation between alternate-identity signatures and other key-to-key signatures.
const ALTERNATE_IDENTITY_SIGNATURE_PREFIX_1: &[u8] = &[0xFF; 32];
const ALTERNATE_IDENTITY_SIGNATURE_PREFIX_2: &[u8] = b"Signal_PNI_Signature";
pub(crate) const CIPHERTEXT_MESSAGE_CURRENT_VERSION: u8 = 4;
/// A public key that represents the identity of a user.
///(crate) const CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION: u8 = 3;
/// Wrapper for [`PublicKey`].SAGE_CURRENT_VERSION: u8 = 3;phertextMessageType, DeviceId,
#[derive(tion, IdentityKey, IdentityKeyPair, IdentityKeyStore, KeyPair, KyberPreKeyStore,
    Debug, PartialOrd, Ord, PartialEq, Eq, Clone, Copy, derive_more::From, derive_more::Into,Id,
)]b enum CiphertextMessage {yBytes, SessionRecord, SessionStore, SignalMessage,
pub struct IdentityKey {Message),eKeyStore, Timestamp,
    public_key: PublicKey,eKeySignalMessage),
}   SenderKeyMessage(SenderKeyMessage),
    PlaintextContent(PlaintextContent),
impl IdentityKey {ertificate {
    /// Initialize a public-facing identity from a public key.
    pub fn new(public_key: PublicKey) -> Self {_enum::TryFromPrimitive)]
        Self { public_key }
    }num CiphertextMessageType {
    Whisper = 2,ec<u8>,
    /// Return the public key representing this identity.
    #[inline] = 7,
    pub fn public_key(&self) -> &PublicKey {
        &self.public_keyertificate ID which is used to test the
    }ation logic. As of this writing, no prod server certificates have
impl CiphertextMessage {r does, add its key ID here.
    /// Return an owned byte slice which can be deserialized with [`Self::decode`].
    #[inline] self {er certificate is ever generated which collides
    pub fn serialize(&self) -> Box<[u8]> {ge(_) => CiphertextMessageType::Whisper,
        self.public_key.serialize()eySignalMessage(_) => CiphertextMessageType::PreKey,
    }       CiphertextMessage::SenderKeyMessage(_) => CiphertextMessageType::SenderKey,
            CiphertextMessage::PlaintextContent(_) => CiphertextMessageType::Plaintext,
    /// Deserialize a public identity from a byte slice.
    pub fn decode(value: &[u8]) -> Result<Self> {ype.
        let pk = PublicKey::try_from(value)?;F;
        Ok(Self { public_key: pk })] {
    }   match self {is as part of constructing DeviceId.
            CiphertextMessage::SignalMessage(x) => x.serialized(),
    /// Given a trusted identity `self`, verify that `other` represents an alternate identity for
    /// this user.textMessage::SenderKeyMessage(x) => x.serialized(),
    ///     CiphertextMessage::PlaintextContent(x) => x.serialized(),
    /// `signature` must be calculated from [`IdentityKeyPair::sign_alternate_identity`].
    pub fn verify_alternate_identity(&self, other: &IdentityKey, signature: &[u8]) -> Result<bool> {
        let is_valid = self.public_key.verify_signature_for_multipart_message(
            &[certificate.is_none() || pb.signature.is_none() {
                ALTERNATE_IDENTITY_SIGNATURE_PREFIX_1,tobufEncoding);
                ALTERNATE_IDENTITY_SIGNATURE_PREFIX_2,
                &other.serialize(),
            ],chet_key: PublicKey,
            signature,te
        );w(dead_code)]alProtocolError::InvalidProtobufEncoding)?;
        println!(revious_counter: u32,
            "IdentityKey: Verifying signature from identity: {:?}",   ciphertext: Box<[u8]>,
            self.public_key.serialize()    serialized: Box<[u8]>,rotocolError::InvalidProtobufEncoding)?;
        );
        println!("IdentityKey: Signature verification result: {}", is_valid);ver_certificate::Certificate::decode(certificate.as_ref())
        Ok(is_valid)impl SignalMessage {_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;
    }
}
ub fn new( .key
impl TryFrom<&[u8]> for IdentityKey {       message_version: u8,lProtocolError::InvalidProtobufEncoding)?[..],
    type Error = SignalProtocolError;        mac_key: &[u8],
ey,
    fn try_from(value: &[u8]) -> Result<Self> {     counter: u32,
        IdentityKey::decode(value)idProtobufEncoding)?;
    }u8],
} &IdentityKey,
 &IdentityKey,
/// The private identity of a user.
///       println!("Protocol: Serializing message with version: {}", message_version);
/// Can be converted to and from [`KeyPair`].        let message = proto::wire::SignalMessage {
#[derive(Copy, Clone)]y: Some(sender_ratchet_key.serialize().into_vec()),
pub struct IdentityKeyPair {
    identity_key: IdentityKey,
    private_key: PrivateKey,phertext: Some(Vec::<u8>::from(ciphertext)),
}
ed = Vec::with_capacity(1 + message.encoded_len() + Self::MAC_LENGTH);
impl IdentityKeyPair {erialized.push(((message_version & 0xF) << 4) | CIPHERTEXT_MESSAGE_CURRENT_VERSION);blicKey,
    /// Create a key pair from a public `identity_key` and a private `private_key`.   message
    pub fn new(identity_key: IdentityKey, private_key: PrivateKey) -> Self {            .encode(&mut serialized)
        Self {
            identity_key,tificate::Certificate {
            private_key,
        }            receiver_identity_key,e(key.serialize().to_vec()),
    }c_key,

    /// Generate a random new identity from randomness in `csprng`.
    pub fn generate<R: CryptoRng + Rng>(csprng: &mut R) -> Self {erialized.extend_from_slice(&mac);
        let keypair = KeyPair::generate(csprng);   let serialized = serialized.into_boxed_slice();ture = trust_root.calculate_signature(&certificate, rng)?.to_vec();
        Ok(Self {
        Self {erCertificate {
            identity_key: keypair.public_key.into(),ender_ratchet_key,ate: Some(certificate.clone()),
            private_key: keypair.private_key,
        }er,
    }       ciphertext: ciphertext.into(),);
            serialized,
    /// Return the public identity of this user.
    #[inline]    serialized,
    pub fn identity_key(&self) -> &IdentityKey {
        &self.identity_key
    }ub fn message_version(&self) -> u8 {
        self.message_version       key_id,
    /// Return the public key that defines this identity.
    #[inline]
    pub fn public_key(&self) -> &PublicKey {
        self.identity_key.public_key()_key(&self) -> &PublicKey {elf) -> Result<proto::sealed_sender::ServerCertificate> {
    }   &self.sender_ratchet_key   Ok(proto::sealed_sender::ServerCertificate {
    }            certificate: Some(self.certificate.clone()),
    /// Return the private key that defines this identity.
    #[inline]
    pub fn private_key(&self) -> &PrivateKey {
        &self.private_key
    }lt<bool> {
ER_CERTIFICATE_KEY_IDS.contains(&self.key_id()?) {
    /// Return a byte slice which can later be deserialized with [`Self::try_from`].    #[inline]
    pub fn serialize(&self) -> Box<[u8]> { certificate with revoked ID {:x}",
        let structure = proto::storage::IdentityKeyPairStructure {  self.key_id()?
            public_key: self.identity_key.serialize().to_vec(),            );
            private_key: self.private_key.serialize().to_vec(),eturn Ok(false);
        };
ertificate, &self.signature))
        let result = structure.encode_to_vec();ciphertext
        result.into_boxed_slice()
    }
id)
    /// Generate a signature claiming that `other` represents the same user as `self`.
    pub fn sign_alternate_identity<R: Rng + CryptoRng>(_identity_key: &IdentityKey,
        &self,esult<PublicKey> {
        other: &IdentityKey,
        rng: &mut R,
    ) -> Result<Box<[u8]>> {r_mac = &Self::compute_mac(
        Ok(self.private_key.calculate_signature_for_multipart_message(er_identity_key,esult<&[u8]> {
            &[ receiver_identity_key,tificate)
                ALTERNATE_IDENTITY_SIGNATURE_PREFIX_1,       mac_key,
                ALTERNATE_IDENTITY_SIGNATURE_PREFIX_2,           &self.serialized[..self.serialized.len() - Self::MAC_LENGTH],
                &other.serialize(),        )?;
            ],self.serialized.len() - Self::MAC_LENGTH..];
            rng,_eq(their_mac).into();
        )?)        if !result {
    }cause we try multiple sessions.self) -> Result<&[u8]> {
}

impl TryFrom<&[u8]> for IdentityKeyPair {ex::encode(their_mac),
    type Error = SignalProtocolError;

    fn try_from(value: &[u8]) -> Result<Self> {rtificate {
        let structure = proto::storage::IdentityKeyPairStructure::decode(value)   Ok(result)igner: ServerCertificate,
            .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;   }    key: PublicKey,
        Ok(Self {d: DeviceId,
            identity_key: IdentityKey::try_from(&structure.public_key[..])?,
            private_key: PrivateKey::deserialize(&structure.private_key)?,yKey,
        })        receiver_identity_key: &IdentityKey,mp,
    }
}

impl TryFrom<PrivateKey> for IdentityKeyPair {   if mac_key.len() != 32 {
    type Error = SignalProtocolError;           return Err(SignalProtocolError::InvalidMacKeyLength(mac_key.len()));
        }
    fn try_from(private_key: PrivateKey) -> Result<Self> {w_from_slice(mac_key)
        let identity_key = IdentityKey::new(private_key.public_key()?);ld accept any size key");        let pb = proto::sealed_sender::SenderCertificate::decode(data)
        Ok(Self::new(identity_key, private_key))
    }).serialize().as_ref());
}blic_key().serialize().as_ref());
ac.update(message);otobufEncoding)?;
impl From<KeyPair> for IdentityKeyPair {   let mut result = [0u8; Self::MAC_LENGTH];
    fn from(value: KeyPair) -> Self {       result.copy_from_slice(&mac.finalize().into_bytes()[..Self::MAC_LENGTH]);ture
        Self {        Ok(result)       .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
            identity_key: value.public_key.into(),
            private_key: value.private_key,tificate::Certificate::decode(certificate.as_ref())
        }
    }AsRef<[u8]> for SignalMessage {
}   fn as_ref(&self) -> &[u8] {e_id: DeviceId = certificate_data
        &self.serialized       .sender_device
impl From<IdentityKeyPair> for KeyPair {    .ok_or(SignalProtocolError::InvalidProtobufEncoding)?
    fn from(value: IdentityKeyPair) -> Self {  .into();
        Self::new(value.identity_key.into(), value.private_key)
    }impl TryFrom<&[u8]> for SignalMessage {
}SignalProtocolError;            .map(Timestamp::from_epoch_millis)
ProtobufEncoding)?;
#[cfg(test)]from(value: &[u8]) -> Result<Self> {
mod tests {ssage::MAC_LENGTH + 1 {
    use rand::rngs::OsRng;tMessageTooShort(value.len()));   .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;

    use super::*;
 message_version);
    #[test]   if message_version < CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION {icate_data.sender_e164;
    fn test_identity_key_from() {            return Err(SignalProtocolError::LegacyCiphertextVersion(
                message_version,et key_pair = KeyPair::generate(&mut OsRng); key = PublicKey::try_from(
            ));alize();
        }
        if message_version > CIPHERTEXT_MESSAGE_CURRENT_VERSION {ic_serialized, identity_key.serialize());obufEncoding)?[..],
            return Err(SignalProtocolError::UnrecognizedCiphertextVersion(
                message_version,
            ));    #[test]_vec();
        }y_key_pair() -> Result<()> {er_bits)?;

        let proto_structure =
            proto::wire::SignalMessage::decode(&value[1..value.len() - SignalMessage::MAC_LENGTH])        let deserialized_identity_key_pair = IdentityKeyPair::try_from(&serialized[..])?;
                .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;
_pair.identity_key(),  sender_device_id,
        let sender_ratchet_key = proto_structure
            .ratchet_key
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
        let sender_ratchet_key = PublicKey::deserialize(&sender_ratchet_key)?;_key_pair.private_key().key_type(),  serialized: data.to_vec(),
        let counter = proto_structure)            certificate,
            .counter
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
        let previous_counter = proto_structure.previous_counter.unwrap_or(0);y_pair.private_key().serialize(),    }
        let ciphertext = proto_structuree()
            .ciphertext
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?
            .into_boxed_slice();

        Ok(SignalMessage {
            message_version,
            sender_ratchet_key,y_signing() -> Result<()> {ficate,
            counter,dentityKeyPair::generate(&mut OsRng);
            previous_counter,generate(&mut OsRng);
            ciphertext,
            serialized: Box::from(value),   let signature = secondary.sign_alternate_identity(primary.identity_key(), &mut OsRng)?;= proto::sealed_sender::sender_certificate::Certificate {
        })       assert!(secondary
    }            .identity_key()            sender_e164: sender_e164.clone(),
}ernate_identity(primary.identity_key(), &signature)?);(sender_device_id.into()),

#[derive(Debug, Clone)]),
pub struct KyberPayload {buf()?),
    pre_key_id: KyberPreKeyId,           .verify_alternate_identity(secondary.identity_key(), &signature)?);
    ciphertext: kem::SerializedCiphertext,
}_signature =        let certificate = certificate_pb.encode_to_vec();
;
impl KyberPayload {_ne!(signature, another_signature);gner_key.calculate_signature(&certificate, rng)?.to_vec();
    pub fn new(id: KyberPreKeyId, ciphertext: kem::SerializedCiphertext) -> Self {
        Self {ey()
            pre_key_id: id,   .verify_alternate_identity(primary.identity_key(), &another_signature)?);ome(certificate.clone()),
            ciphertext,ature.clone()),
        }       let unrelated = IdentityKeyPair::generate(&mut OsRng);
    }        assert!(!secondary        .encode_to_vec();
}ey()
entity(unrelated.identity_key(), &signature)?);   Ok(Self {
#[derive(Debug, Clone)]ed           signer,
pub struct PreKeySignalMessage {()            key,
    message_version: u8,
    registration_id: u32,
    pre_key_id: Option<PreKeyId>,
    signed_pre_key_id: SignedPreKeyId,
    kyber_payload: Option<KyberPayload>,
    base_key: PublicKey,
    identity_key: IdentityKey,      .verify_alternate_identity(primary.identity_key(), &signature)?);            sender_device_id,
    message: SignalMessage,           sender_uuid,
    serialized: Box<[u8]>,            sender_e164,
}

impl PreKeySignalMessage {tificate,
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        message_version: u8,
        registration_id: u32,
        pre_key_id: Option<PreKeyId>,icKey, validation_time: Timestamp) -> Result<bool> {
        signed_pre_key_id: SignedPreKeyId,date(trust_root)? {
        kyber_payload: Option<KyberPayload>,
        base_key: PublicKey,cate contained server certificate that wasn't signed by trust root"
        identity_key: IdentityKey,
        message: SignalMessage,
    ) -> Result<Self> {
        println!("Protocol: Serializing message with version: {}", message_version);
        let proto_message = proto::wire::PreKeySignalMessage {
            registration_id: Some(registration_id),
            pre_key_id: pre_key_id.map(|id| id.into()),
            signed_pre_key_id: Some(signed_pre_key_id.into()),ture(&self.certificate, &self.signature)
            kyber_pre_key_id: kyber_payload.as_ref().map(|kyber| kyber.pre_key_id.into()),
            kyber_ciphertext: kyber_payloadrver");
                .as_ref()
                .map(|kyber| kyber.ciphertext.to_vec()),
            base_key: Some(base_key.serialize().into_vec()),
            identity_key: Some(identity_key.serialize().into_vec()),
            message: Some(Vec::from(message.as_ref())),
        };er certificate is expired (expiration: {}, validation_time: {})",
        let mut serialized = Vec::with_capacity(1 + proto_message.encoded_len());h_millis(),
        serialized.push(((message_version & 0xF) << 4) | CIPHERTEXT_MESSAGE_CURRENT_VERSION);
        proto_message
            .encode(&mut serialized);
            .expect("can always append to a Vec");
        Ok(Self {
            message_version,
            registration_id,
            pre_key_id,
            signed_pre_key_id,-> Result<&ServerCertificate> {
            kyber_payload,ner)
            base_key,
            identity_key,
            message,ub fn key(&self) -> Result<PublicKey> {
            serialized: serialized.into_boxed_slice(),        Ok(self.key)
        })
    }
&self) -> Result<DeviceId> {
    #[inline]   Ok(self.sender_device_id)
    pub fn message_version(&self) -> u8 {    }
        self.message_version
    }tr> {
)
    #[inline]
    pub fn registration_id(&self) -> u32 {
        self.registration_idnder_e164(&self) -> Result<Option<&str>> {
    }

    #[inline]
    pub fn pre_key_id(&self) -> Option<PreKeyId> {    pub fn expiration(&self) -> Result<Timestamp> {
        self.pre_key_idlf.expiration)
    }

    #[inline]ub fn serialized(&self) -> Result<&[u8]> {
    pub fn signed_pre_key_id(&self) -> SignedPreKeyId {        Ok(&self.serialized)
        self.signed_pre_key_id
    }

    #[inline]   Ok(&self.certificate)
    pub fn kyber_pre_key_id(&self) -> Option<KyberPreKeyId> {    }
        self.kyber_payload.as_ref().map(|kyber| kyber.pre_key_id)
    }

    #[inline]
    pub fn kyber_ciphertext(&self) -> Option<&kem::SerializedCiphertext> {}
        self.kyber_payload.as_ref().map(|kyber| &kyber.ciphertext)
    }MessageType {
pe: ProtoMessageType) -> Self {
    #[inline]   let result = match message_type {
    pub fn base_key(&self) -> &PublicKey {            ProtoMessageType::Message => Self::Whisper,
        &self.base_keyrotoMessageType::PrekeyMessage => Self::PreKey,
    }> Self::SenderKey,
pe::PlaintextContent => Self::Plaintext,
    #[inline]   };
    pub fn identity_key(&self) -> &IdentityKey {        // Keep raw values in sync from now on, for efficient codegen.
        &self.identity_keyt!(result == Self::PreKey || message_type as i32 == result as i32);
    }

    #[inline]
    pub fn message(&self) -> &SignalMessage {
        &self.messagehertextMessageType> for ProtoMessageType {
    }sageType) -> Self {
ch message_type {
    #[inline]       CiphertextMessageType::PreKey => Self::PrekeyMessage,
    pub fn serialized(&self) -> &[u8] {           CiphertextMessageType::Whisper => Self::Message,
        &self.serialized            CiphertextMessageType::SenderKey => Self::SenderkeyMessage,
    }xt => Self::PlaintextContent,
}
es in sync from now on, for efficient codegen.
impl AsRef<[u8]> for PreKeySignalMessage {   assert!(result == Self::PrekeyMessage || message_type as i32 == result as i32);
    fn as_ref(&self) -> &[u8] {       result
        &self.serialized    }
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
impl TryFrom<&[u8]> for PreKeySignalMessage {
    type Error = SignalProtocolError;

    fn try_from(value: &[u8]) -> Result<Self> {cit,
        if value.is_empty() {    Unknown(u32),
            return Err(SignalProtocolError::CiphertextMessageTooShort(value.len()));
        }

        let message_version = value[0] >> 4;i32> {
        println!("Protocol: Deserializing message, detected version: {}", message_version); == ContentHint::Default {
        if message_version < CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION {   None
            return Err(SignalProtocolError::LegacyCiphertextVersion(
                message_version,
            ));
        }
        if message_version > CIPHERTEXT_MESSAGE_CURRENT_VERSION {
            return Err(SignalProtocolError::UnrecognizedCiphertextVersion(    pub const fn to_u32(self) -> u32 {
                message_version, as ProtoContentHint;
            ));
        }            ContentHint::Default => 0,
 ProtoContentHint::Resendable as u32,
        let proto_structure = proto::wire::PreKeySignalMessage::decode(&value[1..])nt::Implicit => ProtoContentHint::Implicit as u32,
            .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;

        let base_key = proto_structure
            .base_key
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
        let identity_key = proto_structureontentHint {
            .identity_key
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;sender_message::message::ContentHint as ProtoContentHint;
        let message = proto_structureint::is_valid(0));
            .message
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;            Err(_) if raw_value == 0 => ContentHint::Default,
        let signed_pre_key_id = proto_structure
            .signed_pre_key_id            Ok(ProtoContentHint::Resendable) => ContentHint::Resendable,
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;plicit) => ContentHint::Implicit,

        let base_key = PublicKey::deserialize(base_key.as_ref())?;

        let kyber_payload = match (
            proto_structure.kyber_pre_key_id,
            proto_structure.kyber_ciphertext,) -> Self {
        ) {
            (Some(id), Some(ct)) => Some(KyberPayload::new(id.into(), ct.into_boxed_slice())),
            (None, None) if message_version <= CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION => None,
            (None, None) => {
                return Err(SignalProtocolError::InvalidMessage(identifiedSenderMessageContent {
                    CiphertextMessageType::PreKey,c<u8>,
                    "Kyber pre key must be present for this session version",
                ));
            }
            _ => {ontentHint,
                return Err(SignalProtocolError::InvalidMessage( Option<Vec<u8>>,
                    CiphertextMessageType::PreKey,
                    "Both or neither kyber pre_key_id and kyber_ciphertext can be present",
                ));ntent {
            } &[u8]) -> Result<Self> {
        };e::decode(data)
;
        Ok(PreKeySignalMessage {
            message_version,
            registration_id: proto_structure.registration_id.unwrap_or(0),
            pre_key_id: proto_structure.pre_key_id.map(|id| id.into()),
            signed_pre_key_id: signed_pre_key_id.into(),
            kyber_payload,nvalidProtobufEncoding)?;
            base_key,t sender = pb
            identity_key: IdentityKey::try_from(identity_key.as_ref())?,       .sender_certificate
            message: SignalMessage::try_from(message.as_ref())?,           .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
            serialized: Box::from(value),        let contents = pb
        })
    }ocolError::InvalidProtobufEncoding)?;
} = pb

#[derive(Debug, Clone)]raw| ContentHint::from(raw as u32))
pub struct SenderKeyMessage {_or(ContentHint::Default);
    message_version: u8,group_id;
    distribution_id: Uuid,
    chain_id: u32,       let sender = SenderCertificate::deserialize(&sender)?;
    iteration: u32,
    ciphertext: Box<[u8]>,= data.to_vec();
    serialized: Box<[u8]>,
}        log::info!(
iedSenderMessageContent from {}.{} with type {:?}",
impl SenderKeyMessage {id()?,
    const SIGNATURE_LEN: usize = 64;ce_id()?,

    pub fn new<R: CryptoRng + Rng>(
        message_version: u8,
        distribution_id: Uuid,
        chain_id: u32,
        iteration: u32,
        ciphertext: Box<[u8]>,
        csprng: &mut R,
        signature_key: &PrivateKey,
    ) -> Result<Self> {
        println!("Protocol: Serializing message with version: {}", message_version);
        let proto_message = proto::wire::SenderKeyMessage {
            distribution_uuid: Some(distribution_id.as_bytes().to_vec()),
            chain_id: Some(chain_id),
            iteration: Some(iteration),
            ciphertext: Some(ciphertext.to_vec()),rCertificate,
        };
        let proto_message_len = proto_message.encoded_len();
        let mut serialized = Vec::with_capacity(1 + proto_message_len + Self::SIGNATURE_LEN);
        serialized.push(((message_version & 0xF) << 4) | SENDERKEY_MESSAGE_CURRENT_VERSION);
        proto_message_msg_type = ProtoMessageType::from(msg_type);
            .encode(&mut serialized)sage::Message {
            .expect("can always append to a buffer");ntents.clone()),
        let signature = signature_key.calculate_signature(&serialized, csprng)?;ome(proto_msg_type.into()),
        serialized.extend_from_slice(&signature[..]);tificate: Some(sender.serialized()?.to_vec()),
        Ok(Self {t: content_hint.to_proto(),
            message_version: SENDERKEY_MESSAGE_CURRENT_VERSION, {
            distribution_id,      if buf.is_empty() {
            chain_id,               None
            iteration,                } else {
            ciphertext,
            serialized: serialized.into_boxed_slice(),
        })
    }

    pub fn verify_signature(&self, signature_key: &PublicKey) -> Result<bool> {        let serialized = msg.encode_to_vec();
        let valid = signature_key.verify_signature(
            &self.serialized[..self.serialized.len() - Self::SIGNATURE_LEN],   Ok(Self {
            &self.serialized[self.serialized.len() - Self::SIGNATURE_LEN..],            serialized,
        );sg_type,

        Ok(valid)
    }       content_hint,
            group_id,
    #[inline]
    pub fn message_version(&self) -> u8 {
        self.message_version
    }ub fn msg_type(&self) -> Result<CiphertextMessageType> {
        Ok(self.msg_type)
    #[inline]
    pub fn distribution_id(&self) -> Uuid {
        self.distribution_idlf) -> Result<&SenderCertificate> {
    }   Ok(&self.sender)
    }
    #[inline]
    pub fn chain_id(&self) -> u32 {<&[u8]> {
        self.chain_idnts)
    }

    #[inline]ntent_hint(&self) -> Result<ContentHint> {
    pub fn iteration(&self) -> u32 {
        self.iteration
    }
    pub fn group_id(&self) -> Result<Option<&[u8]>> {
    #[inline]lf.group_id.as_deref())
    pub fn ciphertext(&self) -> &[u8] {
        &self.ciphertext
    }ub fn serialized(&self) -> Result<&[u8]> {
       Ok(&self.serialized)
    #[inline]    }
    pub fn serialized(&self) -> &[u8] {
        &self.serialized
    }essage<'a> {
}1 {
       ephemeral_public: PublicKey,
impl AsRef<[u8]> for SenderKeyMessage {        encrypted_static: Vec<u8>,
    fn as_ref(&self) -> &[u8] {
        &self.serialized
    }    V2 {
}
der_v2::MESSAGE_KEY_LEN],
impl TryFrom<&[u8]> for SenderKeyMessage {
    type Error = SignalProtocolError;ncrypted_message: &'a [u8],

    fn try_from(value: &[u8]) -> Result<Self> {
        if value.len() < 1 + Self::SIGNATURE_LEN {
            return Err(SignalProtocolError::CiphertextMessageTooShort(value.len()));SION: u8 = 1;
        }NDER_V1_FULL_VERSION: u8 = 0x11;
        let message_version = value[0] >> 4;LED_SENDER_V2_MAJOR_VERSION: u8 = 2;
        println!("Protocol: Deserializing message, detected version: {}", message_version);
        if message_version < SENDERKEY_MESSAGE_CURRENT_VERSION {
            return Err(SignalProtocolError::LegacyCiphertextVersion(
                message_version,tifiedSenderMessage<'a> {
            ));serialize(data: &'a [u8]) -> Result<Self> {
        }maining) = data.split_first().ok_or_else(|| {
        if message_version > SENDERKEY_MESSAGE_CURRENT_VERSION {
            return Err(SignalProtocolError::UnrecognizedCiphertextVersion(
                message_version,        let version = version_byte >> 4;
            ));
        }dentifiedSenderMessage with version {}",
        let proto_structure =
            proto::wire::SenderKeyMessage::decode(&value[1..value.len() - Self::SIGNATURE_LEN])
                .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;
 {
        let distribution_id = proto_structure
            .distribution_uuid be accepted version == 0 here?
            .and_then(|bytes| Uuid::from_slice(bytes.as_slice()).ok()) = proto::sealed_sender::UnidentifiedSenderMessage::decode(remaining)
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;bufEncoding)?;
        let chain_id = proto_structure
            .chain_idemeral_public = pb
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
        let iteration = proto_structurelProtocolError::InvalidProtobufEncoding)?;
            .iteration                let encrypted_static = pb
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;d_static
        let ciphertext = proto_structureignalProtocolError::InvalidProtobufEncoding)?;
            .ciphertextd_message = pb
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?encrypted_message
            .into_boxed_slice();k_or(SignalProtocolError::InvalidProtobufEncoding)?;

        Ok(SenderKeyMessage {blicKey::try_from(&ephemeral_public[..])?;
            message_version,
            distribution_id,           Ok(Self::V1 {
            chain_id,                   ephemeral_public,
            iteration,                    encrypted_static,
            ciphertext,rypted_message,
            serialized: Box::from(value),
        })
    }V2_MAJOR_VERSION => {
}/ Uses a flat representation: C || AT || E.pub || ciphertext
erive(FromBytes, Immutable, KnownLayout)]
#[derive(Debug, Clone)]C, packed)]
pub struct SenderKeyDistributionMessage {ixRepr {
    message_version: u8,ted_message_key: [u8; sealed_sender_v2::MESSAGE_KEY_LEN],
    distribution_id: Uuid,                   encrypted_authentication_tag: [u8; sealed_sender_v2::AUTH_TAG_LEN],
    chain_id: u32,                    ephemeral_public: [u8; sealed_sender_v2::PUBLIC_KEY_LEN],
    iteration: u32,
    chain_key: Vec<u8>, let (prefix, encrypted_message) =
    signing_key: PublicKey,::Ref::<_, PrefixRepr>::from_prefix(remaining)
    serialized: Box<[u8]>,rr(|_| SignalProtocolError::InvalidProtobufEncoding)?;
}
fixRepr {
impl SenderKeyDistributionMessage {ed_message_key,
    pub fn new(uthentication_tag,
        message_version: u8,emeral_public,
        distribution_id: Uuid,
        chain_id: u32,
        iteration: u32,
        chain_key: Vec<u8>,ublicKey::from_djb_public_key_bytes(
        signing_key: PublicKey,ce(),
    ) -> Result<Self> {
        println!("Protocol: Serializing message with version: {}", message_version);          encrypted_message_key,
        let proto_message = proto::wire::SenderKeyDistributionMessage {
            distribution_uuid: Some(distribution_id.as_bytes().to_vec()),
            chain_id: Some(chain_id),
            iteration: Some(iteration),
            chain_key: Some(chain_key.clone()),edSenderVersion(version)),
            signing_key: Some(signing_key.serialize().to_vec()),        }
        };
        let mut serialized = Vec::with_capacity(1 + proto_message.encoded_len());
        serialized.push(((message_version & 0xF) << 4) | SENDERKEY_MESSAGE_CURRENT_VERSION);
        proto_message{
            .encode(&mut serialized)
            .expect("can always append to a buffer");

        Ok(Self {
            message_version,
            distribution_id,// A symmetric cipher key and a MAC key, along with a "chain key" consumed in
            chain_id,    /// [`StaticKeys::calculate`].
            iteration,) struct EphemeralKeys {
            chain_key,
            signing_key,y: [u8; 32],
            serialized: serialized.into_boxed_slice(),   pub(super) mac_key: [u8; 32],
        })    }
    }
ry";
    #[inline]: usize = 96;
    pub fn message_version(&self) -> u8 {
        self.message_version    impl EphemeralKeys {
    }erive a set of symmetric keys from the key agreement between the sender and

    #[inline]culate(
    pub fn distribution_id(&self) -> Result<Uuid> {       our_keys: &KeyPair,
        Ok(self.distribution_id)            their_public: &PublicKey,
    }irection: Direction,

    #[inline]y = our_keys.public_key.serialize();
    pub fn chain_id(&self) -> Result<u32> {       let their_pub_key = their_public.serialize();
        Ok(self.chain_id)            let ephemeral_salt = match direction {
    }   Direction::Sending => [SALT_PREFIX, &their_pub_key, &our_pub_key],
PREFIX, &our_pub_key, &their_pub_key],
    #[inline]
    pub fn iteration(&self) -> Result<u32> {       .concat();
        Ok(self.iteration)
    }et shared_secret = our_keys.private_key.calculate_agreement(their_public)?;
YS_KDF_LEN];
    #[inline]::Sha256>::new(Some(&ephemeral_salt), &shared_secret)
    pub fn chain_key(&self) -> Result<&[u8]> {           .expand(&[], &mut derived_values)
        Ok(&self.chain_key)                .expect("valid output length");
    }

    #[inline]y: *array_ref![&derived_values, 0, 32],
    pub fn signing_key(&self) -> Result<&PublicKey> {           cipher_key: *array_ref![&derived_values, 32, 32],
        Ok(&self.signing_key)               mac_key: *array_ref![&derived_values, 64, 32],
    }            })

    #[inline]
    pub fn serialized(&self) -> &[u8] {
        &self.serialized[cfg(test)]
    }   impl PartialEq for EphemeralKeys {
}        fn eq(&self, other: &Self) -> bool {

impl AsRef<[u8]> for SenderKeyDistributionMessage { other.cipher_key
    fn as_ref(&self) -> &[u8] {                && self.mac_key == other.mac_key
        &self.serialized
    }
}

impl TryFrom<&[u8]> for SenderKeyDistributionMessage {Eq for EphemeralKeys {}
    type Error = SignalProtocolError;

    fn try_from(value: &[u8]) -> Result<Self> {    impl fmt::Debug for EphemeralKeys {
        // The message contains at least a X25519 key and a chain key
        if value.len() < 1 + 32 + 32 {
            return Err(SignalProtocolError::CiphertextMessageTooShort(value.len()));
        } "EphemeralKeys {{ chain_key: {:?}, cipher_key: {:?}, mac_key: {:?} }}",
       self.chain_key, self.cipher_key, self.mac_key
        let message_version = value[0] >> 4;
        println!("Protocol: Deserializing message, detected version: {}", message_version);

        if message_version < SENDERKEY_MESSAGE_CURRENT_VERSION {
            return Err(SignalProtocolError::LegacyCiphertextVersion( symmetric cipher key and a MAC key.
                message_version,    pub(super) struct StaticKeys {
            ));
        }
        if message_version > SENDERKEY_MESSAGE_CURRENT_VERSION {    }
            return Err(SignalProtocolError::UnrecognizedCiphertextVersion(
                message_version,
            ));the sender and
        }ain_key`].

        let proto_structure = proto::wire::SenderKeyDistributionMessage::decode(&value[1..]) &IdentityKeyPair,
            .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;

        let distribution_id = proto_structure8],
            .distribution_uuid
            .and_then(|bytes| Uuid::from_slice(bytes.as_slice()).ok())t].concat();
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
        let chain_id = proto_structuregreement(their_key)?;
            .chain_idthe first 32 are discarded/unused. This is intended to
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;e way the EphemeralKeys are derived, even though StaticKeys does not end up
        let iteration = proto_structure
            .iteration            let mut derived_values = [0; 96];
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;red_secret)
        let chain_key = proto_structure
            .chain_key       .expect("valid output length");
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
        let signing_key = proto_structure
            .signing_key                cipher_key: *array_ref![&derived_values, 32, 32],
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;ived_values, 64, 32],

        if chain_key.len() != 32 || signing_key.len() != 33 {
            return Err(SignalProtocolError::InvalidProtobufEncoding);
        }

        let signing_key = PublicKey::deserialize(&signing_key)?;d_authentication() -> Result<()> {
have a long-term identity key pair.
        Ok(SenderKeyDistributionMessage {t sender_identity = IdentityKeyPair::generate(&mut rand::thread_rng());
            message_version,   let recipient_identity = IdentityKeyPair::generate(&mut rand::thread_rng());
            distribution_id,
            chain_id,        // Generate an ephemeral key pair.
            iteration,meral = KeyPair::generate(&mut rand::thread_rng());
            chain_key,= sender_ephemeral.public_key;
            signing_key,ral cipher, chain, and MAC keys.
            serialized: Box::from(value),       let sender_eph_keys = EphemeralKeys::calculate(
        })            &sender_ephemeral,
    }dentity.public_key(),
}
 )?;
#[derive(Debug, Clone)]
pub struct PlaintextContent {
    serialized: Box<[u8]>,r_hmacsha256_encrypt(
}            &sender_identity.public_key().serialize(),

impl PlaintextContent {     &sender_eph_keys.mac_key,
    /// Identifies a serialized PlaintextContent.
    ///
    /// This ensures someone doesn't try to serialize an arbitrary Content message as
    /// PlaintextContent; only messages that are okay to send as plaintext should be allowed.        // Generate another cipher and MAC key.
    const PLAINTEXT_CONTEXT_IDENTIFIER_BYTE: u8 = 0xC0;ender_static_keys = StaticKeys::calculate(

    /// Marks the end of a message and the start of any padding.y.public_key(),
    ///       &sender_eph_keys.chain_key,
    /// Usually messages are padded to avoid exposing patterns,            &sender_static_key_ctext,
    /// but PlaintextContent messages are all fixed-length anyway, so there won't be any padding.
    const PADDING_BOUNDARY_BYTE: u8 = 0x80;
ge_contents = b"this is a binary message";
    #[inline]   let sender_message_data = crypto::aes256_ctr_hmacsha256_encrypt(
    pub fn body(&self) -> &[u8] {           sender_message_contents,
        &self.serialized[1..]            &sender_static_keys.cipher_key,
    }

    #[inline] be correct");
    pub fn serialized(&self) -> &[u8] {
        &self.serialized calculates the ephemeral key and the sender's public key.
    }t recipient_eph_keys = EphemeralKeys::calculate(
}
public,
impl From<DecryptionErrorMessage> for PlaintextContent {
    fn from(message: DecryptionErrorMessage) -> Self {
        let proto_structure = proto::service::Content {s);
            decryption_error_message: Some(message.serialized().to_vec()),
            ..Default::default()to::aes256_ctr_hmacsha256_decrypt(
        };   &sender_static_key_ctext,
        let mut serialized = vec![Self::PLAINTEXT_CONTEXT_IDENTIFIER_BYTE];       &recipient_eph_keys.cipher_key,
        proto_structure           &recipient_eph_keys.mac_key,
            .encode(&mut serialized)        )
            .expect("can always encode to a Vec");ly");
        serialized.push(Self::PADDING_BOUNDARY_BYTE);Key = PublicKey::try_from(&recipient_message_key_bytes[..])?;
        Self {        assert_eq!(sender_identity.public_key(), &sender_public_key);
            serialized: Box::from(serialized),
        }keys = StaticKeys::calculate(
    }
}   &sender_public_key,

impl TryFrom<&[u8]> for PlaintextContent {
    type Error = SignalProtocolError;

    fn try_from(value: &[u8]) -> Result<Self> {et recipient_message_contents = crypto::aes256_ctr_hmacsha256_decrypt(
        if value.is_empty() {er_message_data,
            return Err(SignalProtocolError::CiphertextMessageTooShort(0));_key,
        }  &recipient_static_keys.mac_key,
        if value[0] != Self::PLAINTEXT_CONTEXT_IDENTIFIER_BYTE {   )
            return Err(SignalProtocolError::UnrecognizedMessageVersion(       .expect("should decrypt successfully");
                value[0] as u32,        assert_eq!(recipient_message_contents, sender_message_contents);
            ));
        }
        Ok(Self {
            serialized: Box::from(value),
        })
    }message `ptext`, generate an [`UnidentifiedSenderMessageContent`], then
}// pass the result to [`sealed_sender_encrypt_from_usmc`].
///
#[derive(Debug, Clone)]ncrypt a message in a 1:1 using [Sealed Sender v1].
pub struct DecryptionErrorMessage {
    ratchet_key: Option<PublicKey>,_sender_encrypt_from_usmc
    timestamp: Timestamp,ryptoRng>(
    device_id: u32,
    serialized: Box<[u8]>,
}

impl DecryptionErrorMessage {
    pub fn for_original(
        original_bytes: &[u8], R,
        original_type: CiphertextMessageType,
        original_timestamp: Timestamp,tore, identity_store, now).await?;
        original_sender_device_id: u32,derMessageContent::new(
    ) -> Result<Self> {
        let ratchet_key = match original_type {_cert.clone(),
            CiphertextMessageType::Whisper => {
                Some(*SignalMessage::try_from(original_bytes)?.sender_ratchet_key())
            }
            CiphertextMessageType::PreKey => Some(
                *PreKeySignalMessage::try_from(original_bytes)?ncrypt_from_usmc(destination, &usmc, identity_store, rng).await
                    .message()
                    .sender_ratchet_key(),
            ),/// This method implements the single-key single-recipient [KEM] described in [this Signal blog
            CiphertextMessageType::SenderKey => None,
            CiphertextMessageType::Plaintext => {
                return Err(SignalProtocolError::InvalidArgument(
                    "cannot create a DecryptionErrorMessage for plaintext content; it is not encrypted".to_string()aled-sender/
                ));
            }decrypt the Sealed Sender message produced by
        };/// this method.

        let proto_message = proto::service::DecryptionErrorMessage {ed Sender v2
            timestamp: Some(original_timestamp.epoch_millis()),emented by this method partially derives the encryption
            ratchet_key: ratchet_key.map(|k| k.serialize().into()),would then require re-encrypting the same message
            device_id: Some(original_sender_device_id),contrast,
        };d Sender v2](sealed_sender_multi_recipient_encrypt) uses a *multi-recipient* KEM scheme
        let serialized = proto_message.encode_to_vec();hich avoids this repeated work, but makes a few additional design tradeoffs.
///
        Ok(Self {vel algorithmic overview
            ratchet_key,hod is described in [this Signal blog post]. The
            timestamp: original_timestamp,f this process are listed below:
            device_id: original_sender_device_id,. Generate a random key pair.
            serialized: serialized.into_boxed_slice(),/// 2. Derive a symmetric chain key, cipher key, and MAC key from the recipient's public key and the
        })'s public/private key pair.
    }using the cipher key and MAC key from (2) with

    #[inline]. Derive a second symmetric cipher key and MAC key from the sender's private key, the
    pub fn timestamp(&self) -> Timestamp {///    recipient's public key, and the chain key from (2).
        self.timestamprically encrypt the underlying [`UnidentifiedSenderMessageContent`] using the cipher key
    }-256 in CTR mode.
ral public key from (1) and the encrypted public key from (3) to the
    #[inline]  recipient, along with the encrypted message (5).
    pub fn ratchet_key(&self) -> Option<&PublicKey> {///
        self.ratchet_key.as_ref()code
    }
           = X25519.generateEphemeral()
    #[inline]_chain, e_cipherKey, e_macKey = HKDF(salt="UnidentifiedDelivery" || recipientIdentityPublic || e_pub, ikm=ECDH(recipientIdentityPublic, e_priv), info="")
    pub fn device_id(&self) -> u32 {// e_ciphertext                   = AES_CTR(key=e_cipherKey, input=senderIdentityPublic)
        self.device_id/// e_mac                          = Hmac256(key=e_macKey, input=e_ciphertext)
    }
=e_chain || e_ciphertext || e_mac, ikm=ECDH(recipientIdentityPublic, senderIdentityPrivate), info="")
    #[inline]/// s_ciphertext          = AES_CTR(key=s_cipherKey, input=sender_certificate || message_ciphertext)
    pub fn serialized(&self) -> &[u8] {y, input=s_ciphertext)
        &self.serialized
    }
}

impl TryFrom<&[u8]> for DecryptionErrorMessage {
    type Error = SignalProtocolError;Message.Message` from
 an additional byte to indicate the version of Sealed
    fn try_from(value: &[u8]) -> Result<Self> {further documentation on the version
        let proto_structure = proto::service::DecryptionErrorMessage::decode(value)the-version-byte)).
            .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;_encrypt_from_usmc<R: Rng + CryptoRng>(
        let timestamp = proto_structure
            .timestamptifiedSenderMessageContent,
            .map(Timestamp::from_epoch_millis)yn IdentityKeyStore,
            .ok_or(SignalProtocolError::InvalidProtobufEncoding)?;
        let ratchet_key = proto_structure
            .ratchet_key_identity_key_pair().await?;
            .map(|k| PublicKey::deserialize(&k))eir_identity = identity_store
            .transpose()?;   .get_identity(destination)
        let device_id = proto_structure.device_id.unwrap_or_default();       .await?
        Ok(Self {        .ok_or_else(|| SignalProtocolError::SessionNotFound(destination.clone()))?;
            timestamp,
            ratchet_key,
            device_id,
            serialized: Box::from(value),EphemeralKeys::calculate(
        })
    }
}   Direction::Sending,

/// For testing
pub fn extract_decryption_error_message_from_serialized_content(tic_key_ctext = crypto::aes256_ctr_hmacsha256_encrypt(
    bytes: &[u8],).serialize(),
) -> Result<DecryptionErrorMessage> {ipher_key,
    if bytes.last() != Some(&PlaintextContent::PADDING_BOUNDARY_BYTE) {y,
        return Err(SignalProtocolError::InvalidProtobufEncoding);
    }
    let content = proto::service::Content::decode(bytes.split_last().expect("checked above").1)
        .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;atic_keys = sealed_sender_v1::StaticKeys::calculate(
    content
        .decryption_error_message       their_identity.public_key(),
        .as_deref()        &eph_keys.chain_key,
        .ok_or_else(|| {tic_key_ctext,
            SignalProtocolError::InvalidArgument(
                "Content does not contain DecryptionErrorMessage".to_owned(),
            )aes256_ctr_hmacsha256_encrypt(
        })        usmc.serialized()?,
        .and_then(DecryptionErrorMessage::try_from)eys.cipher_key,
}c_key,
    )
#[cfg(test)]
mod tests {
    use rand::rngs::OsRng;c![SEALED_SENDER_V1_FULL_VERSION];
    use rand::{CryptoRng, Rng};et pb = proto::sealed_sender::UnidentifiedSenderMessage {
eral.public_key.serialize().to_vec()),
    use super::*;y_ctext),
    use crate::KeyPair;e(message_data),
    };
    fn create_signal_message<T>(csprng: &mut T) -> Result<SignalMessage>
    where;
        T: Rng + CryptoRng,
    {    Ok(serialized)
        let mut mac_key = [0u8; 32];
        csprng.fill_bytes(&mut mac_key);
        let mac_key = mac_key;
    use super::*;
        let mut ciphertext = [0u8; 20];
        csprng.fill_bytes(&mut ciphertext);byte strings used as part of a MAC in HKDF.
        let ciphertext = ciphertext;u8] = b"Sealed Sender v2: r (2023-08)";
K";
        let sender_ratchet_key_pair = KeyPair::generate(csprng);_DH: &[u8] = b"Sealed Sender v2: DH";
        let sender_identity_key_pair = KeyPair::generate(csprng);_DH_S: &[u8] = b"Sealed Sender v2: DH-sender";
        let receiver_identity_key_pair = KeyPair::generate(csprng);

        SignalMessage::new(
            4,Aes256GcmSiv as aes_gcm_siv::aead::KeySizeUser>::KeySize::USIZE;
            &mac_key,ub const AUTH_TAG_LEN: usize = 16;
            sender_ratchet_key_pair.public_key,    /// SSv2 hardcodes that its keys are Curve25519 public keys.
            42,
            41,
            &ciphertext,
            &sender_identity_key_pair.public_key.into(),
            &receiver_identity_key_pair.public_key.into(),
        )
    }
mpl DerivedKeys {
    fn assert_signal_message_equals(m1: &SignalMessage, m2: &SignalMessage) {        /// Initialize from a slice of random bytes `m`.
        assert_eq!(m1.message_version, m2.message_version);(super) fn new(m: &[u8]) -> DerivedKeys {
        assert_eq!(m1.sender_ratchet_key, m2.sender_ratchet_key);
        assert_eq!(m1.counter, m2.counter);::<sha2::Sha256>::new(None, m),
        assert_eq!(m1.previous_counter, m2.previous_counter);
        assert_eq!(m1.ciphertext, m2.ciphertext);
        assert_eq!(m1.serialized, m2.serialized);
    }
per) fn derive_e(&self) -> KeyPair {
    #[test]       let mut r = [0; 32];
    fn test_signal_message_serialize_deserialize() -> Result<()> {            self.kdf
        let mut csprng = OsRng;     .expand(LABEL_R, &mut r)
        let message = create_signal_message(&mut csprng)?;
        let deser_message =:try_from(&r[..]).expect("valid PrivateKey");
            SignalMessage::try_from(message.as_ref()).expect("should deserialize without error");)
        assert_signal_message_equals(&message, &deser_message);
        Ok(())
    }
per) fn derive_k(&self) -> [u8; CIPHER_KEY_LEN] {
    #[test]mut k = [0; CIPHER_KEY_LEN];
    fn test_pre_key_signal_message_serialize_deserialize() -> Result<()> {kdf
        let mut csprng = OsRng;d(LABEL_K, &mut k)
        let identity_key_pair = KeyPair::generate(&mut csprng);");
        let base_key_pair = KeyPair::generate(&mut csprng);
        let message = create_signal_message(&mut csprng)?;
        let pre_key_signal_message = PreKeySignalMessage::new(
            3,
            365,om bytes `input` using a shared secret derived from
            None,
            97.into(),
            None, // TODO: add kyber prekeysof this method when called with [`Direction::Sending`] can be inverted to produce
            base_key_pair.public_key,`Direction::Receiving`] with `our_keys` and
            identity_key_pair.public_key.into(),
            message,per) fn apply_agreement_xor(
        )?;KeyPair,
        let deser_pre_key_signal_message =
            PreKeySignalMessage::try_from(pre_key_signal_message.as_ref())
                .expect("should deserialize without error");put: &[u8; MESSAGE_KEY_LEN],
        assert_eq!(; MESSAGE_KEY_LEN]> {
            pre_key_signal_message.message_version,eement(their_key)?;
            deser_pre_key_signal_message.message_version
        );  Direction::Sending => [
        assert_eq!(eement,
            pre_key_signal_message.registration_id,
            deser_pre_key_signal_message.registration_id
        );  ],
        assert_eq!(on::Receiving => [
            pre_key_signal_message.pre_key_id,
            deser_pre_key_signal_message.pre_key_id
        );      our_keys.public_key.serialize(),
        assert_eq!(
            pre_key_signal_message.signed_pre_key_id,
            deser_pre_key_signal_message.signed_pre_key_id
        );
        assert_eq!(KEY_LEN];
            pre_key_signal_message.base_key,, &agreement_key_input)
            deser_pre_key_signal_message.base_key
        );  .expect("valid output length");
        assert_eq!(
            pre_key_signal_message.identity_key.public_key(),
            deser_pre_key_signal_message.identity_key.public_key()
        );  .for_each(|(result_byte, input_byte)| *result_byte ^= input_byte);
        assert_signal_message_equals(ult)
            &pre_key_signal_message.message,
            &deser_pre_key_signal_message.message,
        );pute an [authentication tag] for the bytes `encrypted_message_key` using a shared secret
        assert_eq!(
            pre_key_signal_message.serialized,
            deser_pre_key_signal_message.serializedage_authentication_code
        );
        Ok(())tion::Sending`] should be the same bytes produced by
    }keys` and `their_key`
, if `ephemeral_pub_key` and `encrypted_message_key` are the same.
    #[test] fn compute_authentication_tag(
    fn test_sender_key_message_serialize_deserialize() -> Result<()> {air,
        let mut csprng = OsRng;tityKey,
        let signature_key_pair = KeyPair::generate(&mut csprng);
        let sender_key_message = SenderKeyMessage::new(emeral_pub_key: &PublicKey,
            SENDERKEY_MESSAGE_CURRENT_VERSION,
            Uuid::from_u128(0xd1d1d1d1_7000_11eb_b32a_33b8a8a487a6),
            42,nt = our_keys
            7,
            [1u8, 2, 3].into(),y())?;
            &mut csprng,t mut agreement_key_input = agreement.into_vec();
            &signature_key_pair.private_key,ey_input.extend_from_slice(&ephemeral_pub_key.serialize());
        )?;slice(encrypted_message_key);
        let deser_sender_key_message = SenderKeyMessage::try_from(sender_key_message.as_ref())
            .expect("should deserialize without error");  Direction::Sending => {
        assert_eq!(eement_key_input.extend_from_slice(&our_keys.public_key().serialize());
            sender_key_message.message_version,d_from_slice(&their_key.serialize());
            deser_sender_key_message.message_version
        );  Direction::Receiving => {
        assert_eq!(eement_key_input.extend_from_slice(&their_key.serialize());
            sender_key_message.chain_id,_from_slice(&our_keys.public_key().serialize());
            deser_sender_key_message.chain_id
        );
        assert_eq!(
            sender_key_message.iteration,;
            deser_sender_key_message.iterationagreement_key_input)
        );  .expand(LABEL_DH_S, &mut result)
        assert_eq!(xpect("valid output length");
            sender_key_message.ciphertext,   Ok(result)
            deser_sender_key_message.ciphertext    }
        );
        assert_eq!(
            sender_key_message.serialized,ntication() -> Result<()> {
            deser_sender_key_message.serializedity key pair.
        );t rand::thread_rng());
        Ok(())(&mut rand::thread_rng());
    }
d for our multi-recipient encoding scheme.
    #[test]        let m: [u8; MESSAGE_KEY_LEN] = rand::thread_rng().gen();
    fn test_decryption_error_message() -> Result<()> {/ Derive an ephemeral key pair from those random bytes.
        let mut csprng = OsRng;
        let identity_key_pair = KeyPair::generate(&mut csprng);_e();
        let base_key_pair = KeyPair::generate(&mut csprng);
        let message = create_signal_message(&mut csprng)?;emeral key pair.
        let timestamp: Timestamp = Timestamp::from_epoch_millis(0x2_0000_0001);8; MESSAGE_KEY_LEN] =
        let device_id = 0x8086_2021;ly_agreement_xor(&e, recipient_identity.public_key(), Direction::Sending, &m)?;

        { = compute_authentication_tag(
            let error_message = DecryptionErrorMessage::for_original(
                message.serialized(),
                CiphertextMessageType::Whisper,rection::Sending,
                timestamp,
                device_id,
            )?;?;
            let error_message = DecryptionErrorMessage::try_from(error_message.serialized())?;
            assert_eq!(m bytes and authenticates the result.
                error_message.ratchet_key(),cv_m = apply_agreement_xor(
                Some(message.sender_ratchet_key())ipient_identity.into(),
            );blic_key,
            assert_eq!(error_message.timestamp(), timestamp);:Receiving,
            assert_eq!(error_message.device_id(), device_id);
        }

        let pre_key_signal_message = PreKeySignalMessage::new(
            3, recv_at_0 = compute_authentication_tag(
            365,            &recipient_identity,
            None,   sender_identity.identity_key(),
            97.into(),
            None, // TODO: add kyber prekeys
            base_key_pair.public_key,
            identity_key_pair.public_key.into(),
            message,t_0, &sender_at_0);
        )?;

        {
            let error_message = DecryptionErrorMessage::for_original(
                pre_key_signal_message.serialized(),
                CiphertextMessageType::PreKey,d implements a single-key multi-recipient [KEM] as defined in Manuel Barbosa's
                timestamp, Sealed Sender v2.
                device_id,
            )?;: https://en.wikipedia.org/wiki/Key_encapsulation
            let error_message = DecryptionErrorMessage::try_from(error_message.serialized())?;/// ["Randomness Reuse: Extensions and Improvements"]: https://haslab.uminho.pt/mbb/files/reuse.pdf
            assert_eq!(
                error_message.ratchet_key(), with Sealed Sender v1
                Some(pre_key_signal_message.message().sender_ratchet_key())mented by this method uses the "Generic Construction" in `4.1` of [Barbosa's
            );ndomness Reuse: Extensions and Improvements"], instantiated with [ElGamal encryption].
            assert_eq!(error_message.timestamp(), timestamp);ique enables reusing a single sequence of random bytes across multiple messages with
            assert_eq!(error_message.device_id(), device_id);ation time for clients sending the same message to
        }(without compromising the message security).

        let sender_key_message = SenderKeyMessage::new(re a few additional design tradeoffs this method makes vs [Sealed Sender v1] which may
            3,/// make it comparatively unwieldy for certain scenarios:
            Uuid::nil(), requires a [`SessionRecord`] to exist already for the recipient, i.e. that a Double
            1,`SessionStore`] via
            2,prekey_bundle] after an initial
            Box::from(b"test".to_owned()),
            &mut csprng, additional information in its encoding which makes the resulting message
            &base_key_pair.private_key,ssage produced by [Sealed Sender v1]. For sending, this will generally
        )?; more compact than sending the same message N times, but on the receiver side the

        {encoded message returned by this method
            let error_message = DecryptionErrorMessage::for_original(s produced by protobuf's packing (see
                sender_key_message.serialized(),
                CiphertextMessageType::SenderKey,
                timestamp,/// [ElGamal encryption]: https://en.wikipedia.org/wiki/ElGamal_encryption
                device_id,nder v1]: sealed_sender_encrypt_from_usmc
            )?;Wire Format]: #wire-format
            let error_message = DecryptionErrorMessage::try_from(error_message.serialized())?;///
            assert_eq!(error_message.ratchet_key(), None);level algorithmic overview
            assert_eq!(error_message.timestamp(), timestamp);d below:
            assert_eq!(error_message.device_id(), device_id);of random bytes.
        }
ipient:* Encrypt (1) using a shared secret derived from the private ephemeral
        Ok(())y key.
    }on tag for (3) using a secret derived from the
rivate identity key and the recipient's public identity key.
    #[test]e a symmetric key from (1) and use it to symmetrically encrypt the underlying
    fn test_decryption_error_message_for_plaintext() {cryption]. *This step is only performed once
        assert!(matches!(message, regardless of the number of recipients.*
            DecryptionErrorMessage::for_original(. Send the public ephemeral key (2) to the server, along with the sequence of encrypted random
                &[],//    bytes (3) and authentication tags (4), and the single encrypted message (5).
                CiphertextMessageType::Plaintext,///








}    }        ));            Err(SignalProtocolError::InvalidArgument(_))            ),                7                Timestamp::from_epoch_millis(5),/// [AEAD encryption]:
///    https://en.wikipedia.org/wiki/Authenticated_encryption#Authenticated_encryption_with_associated_data_(AEAD)
///
/// ## Pseudocode
///```text
/// ENCRYPT(message, R_i):
///     M = Random(32)
///     r = KDF(label_r, M, len=32)
///     K = KDF(label_K, M, len=32)
///     E = DeriveKeyPair(r)
///     for i in num_recipients:
///         C_i = KDF(label_DH, DH(E, R_i) || E.public || R_i.public, len=32) XOR M
///         AT_i = KDF(label_DH_s, DH(S, R_i) || E.public || C_i || S.public || R_i.public, len=16)
///     ciphertext = AEAD_Encrypt(K, message)
///     return E.public, C_i, AT_i, ciphertext
///
/// DECRYPT(E.public, C, AT, ciphertext):
///     M = KDF(label_DH, DH(E, R) || E.public || R.public, len=32) xor C
///     r = KDF(label_r, M, len=32)
///     K = KDF(label_K, M, len=32)
///     E' = DeriveKeyPair(r)
///     if E.public != E'.public:
///         return DecryptionError
///     message = AEAD_Decrypt(K, ciphertext) // includes S.public
///     AT' = KDF(label_DH_s, DH(S, R) || E.public || C || S.public || R.public, len=16)
///     if AT != AT':
///         return DecryptionError
///     return message
///```
///
/// # Routing messages to recipients
///
/// The server will split up the set of messages and securely route each individual [received
/// message][receiving] to its intended recipient. [`SealedSenderV2SentMessage`] can perform this
/// fan-out operation.
///
/// # Wire Format
/// Multi-recipient sealed-sender does not use protobufs for its payload format. Instead, it uses a
/// flat format marked with a [version byte](#the-version-byte). The format is different for
/// [sending] and [receiving]. The decrypted content is a protobuf-encoded
/// `UnidentifiedSenderMessage.Message` from `sealed_sender.proto`.
///
/// The public key used in Sealed Sender v2 is always a Curve25519 DJB key.
///
/// [sending]: #sent-messages
/// [receiving]: #received-messages
///
/// ## The version byte
///
/// Sealed sender messages (v1 and v2) in serialized form begin with a version [byte][u8]. This byte
/// has the form:
///
/// ```text
/// (requiredVersion << 4) | currentVersion
/// ```
///
/// v1 messages thus have a version byte of `0x11`. v2 messages have a version byte of `0x22` or
/// `0x23`. A hypothetical version byte `0x34` would indicate a message encoded as Sealed Sender v4,
/// but decodable by any client that supports Sealed Sender v3.
///
/// ## Received messages
///
/// ```text
/// ReceivedMessage {
///     version_byte: u8,
///     c: [u8; 32],
///     at: [u8; 16],
///     e_pub: [u8; 32],
///     message: [u8] // remaining bytes
/// }
/// ```
///
/// Each individual Sealed Sender message received from the server is decoded in the Signal client
/// by calling [`sealed_sender_decrypt`].
///
/// ## Sent messages
///
/// ```text
/// SentMessage {
///     version_byte: u8,
///     count: varint,
///     recipients: [PerRecipientData | ExcludedRecipient; count],
///     e_pub: [u8; 32],
///     message: [u8] // remaining bytes
/// }
///
/// PerRecipientData {
///     recipient: Recipient,
///     devices: [DeviceList], // last element's has_more = 0
///     c: [u8; 32],
///     at: [u8; 16],
/// }
///
/// ExcludedRecipient {
///     recipient: Recipient,
///     no_devices_marker: u8 = 0, // never a valid device ID
/// }
///
/// DeviceList {
///     device_id: u8,
///     has_more: u1, // high bit of following field
///     unused: u1,   // high bit of following field
///     registration_id: u14,
/// }
///
/// Recipient {
///     service_id_fixed_width_binary: [u8; 17],
/// }
/// ```
///
/// The varint encoding used is the same as [protobuf's][varint]. Values are unsigned.
/// Fixed-width-binary encoding is used for the [ServiceId] values.
/// Fixed-width integers are unaligned and in network byte order (big-endian).
///
/// [varint]: https://developers.google.com/protocol-buffers/docs/encoding#varints
pub async fn sealed_sender_multi_recipient_encrypt<
    R: Rng + CryptoRng,
    X: IntoIterator<Item = ServiceId>,
>(
    destinations: &[&ProtocolAddress],
    destination_sessions: &[&SessionRecord],
    excluded_recipients: X,
    usmc: &UnidentifiedSenderMessageContent,
    identity_store: &dyn IdentityKeyStore,
    rng: &mut R,
) -> Result<Vec<u8>>
where
    X::IntoIter: ExactSizeIterator,
{
    sealed_sender_multi_recipient_encrypt_impl(
        destinations,
        destination_sessions,
        excluded_recipients,
        usmc,
        identity_store,
        rng,
    )
    .await
}

async fn sealed_sender_multi_recipient_encrypt_impl<
    R: Rng + CryptoRng,
    X: IntoIterator<Item = ServiceId>,
>(
    destinations: &[&ProtocolAddress],
    destination_sessions: &[&SessionRecord],
    excluded_recipients: X,
    usmc: &UnidentifiedSenderMessageContent,
    identity_store: &dyn IdentityKeyStore,
    rng: &mut R,
) -> Result<Vec<u8>>
where
    X::IntoIter: ExactSizeIterator,
{
    if destinations.len() != destination_sessions.len() {
        return Err(SignalProtocolError::InvalidArgument(
            "must have the same number of destination sessions as addresses".to_string(),
        ));
    }

    let excluded_recipients = excluded_recipients.into_iter();
    let our_identity = identity_store.get_identity_key_pair().await?;

    let m: [u8; sealed_sender_v2::MESSAGE_KEY_LEN] = rng.gen();
    let keys = sealed_sender_v2::DerivedKeys::new(&m);
    let e = keys.derive_e();
    let e_pub = &e.public_key;

    // Encrypt the shared ciphertext using AES-GCM-SIV.
    let ciphertext = {
        let mut ciphertext = usmc.serialized()?.to_vec();
        let symmetric_authentication_tag = Aes256GcmSiv::new(&keys.derive_k().into())
            .encrypt_in_place_detached(
                // There's no nonce because the key is already one-use.
                &aes_gcm_siv::Nonce::default(),
                // And there's no associated data.
                &[],
                &mut ciphertext,
            )
            .expect("AES-GCM-SIV encryption should not fail with a just-computed key");
        // AES-GCM-SIV expects the authentication tag to be at the end of the ciphertext
        // when decrypting.
        ciphertext.extend_from_slice(&symmetric_authentication_tag);
        ciphertext
    };

    // Group the destinations by name, and fetch identity keys once for each name. This optimizes
    // for the common case where all of a recipient's devices are included contiguously in the
    // destination list. (If the caller *doesn't* do this, that's on them; the message will still be
    // valid but some key material will be redundantly computed and encoded in the output.)
    let identity_keys_and_ranges: Vec<(IdentityKey, Range<usize>)> = {
        let mut identity_keys_and_ranges = vec![];
        for (_, mut next_group) in &destinations
            .iter()
            .enumerate()
            .chunk_by(|(_i, next)| next.name())
        {
            let (i, &destination) = next_group
                .next()
                .expect("at least one element in every group");
            // We can't put this before the call to `next()` because `count` consumes the rest of
            // the iterator.
            let count = 1 + next_group.count();
            let their_identity =
                identity_store
                    .get_identity(destination)
                    .await?
                    .ok_or_else(|| {
                        log::error!("missing identity key for {}", destination);
                        // Returned as a SessionNotFound error because (a) we don't have an identity
                        // error that includes the address, and (b) re-establishing the session should
                        // re-fetch the identity.
                        SignalProtocolError::SessionNotFound(destination.clone())
                    })?;
            identity_keys_and_ranges.push((their_identity, i..i + count));
        }
        identity_keys_and_ranges
    };

    // Next, fan out the work of generating the per-recipient to multiple cores, since we do two key
    // agreements per recipient (though not per device) and those are CPU-bound.

    // I know this looks complicated enough to pull out into a separate function altogether, but it
    // also depends on a bunch of local state: our identity, E and E_pub, and M.
    let serialize_recipient_destinations_into = |serialized: &mut Vec<u8>,
                                                 destinations: &[&ProtocolAddress],
                                                 sessions: &[&SessionRecord],
                                                 their_identity: &IdentityKey|
     -> Result<()> {
        let their_service_id = ServiceId::parse_from_service_id_string(destinations[0].name())
            .ok_or_else(|| {
                SignalProtocolError::InvalidArgument(format!(
                    "multi-recipient sealed sender requires recipients' ServiceId (not {})",
                    destinations[0].name()
                ))
            })?;

        serialized.extend_from_slice(&their_service_id.service_id_fixed_width_binary());

        debug_assert_eq!(
            destinations.len(),
            sessions.len(),
            "should be sliced with the same range"
        );
        let mut destinations_and_sessions = destinations.iter().zip(sessions);
        while let Some((&destination, session)) = destinations_and_sessions.next() {
            let their_registration_id = session.remote_registration_id().map_err(|_| {
                SignalProtocolError::InvalidState(
                    "sealed_sender_multi_recipient_encrypt",
                    format!(
                        concat!(
                            "cannot get registration ID from session with {} ",
                            "(maybe it was recently archived)"
                        ),
                        destination
                    ),
                )
            })?;
            if their_registration_id & u32::from(VALID_REGISTRATION_ID_MASK)
                != their_registration_id
            {
                return Err(SignalProtocolError::InvalidRegistrationId(
                    destination.clone(),
                    their_registration_id,
                ));
            }
            let mut their_registration_id =
                u16::try_from(their_registration_id).expect("just checked range");
            if destinations_and_sessions.len() > 0 {
                their_registration_id |= 0x8000;
            }

            let device_id: u32 = destination.device_id().into();
            if device_id == 0 || device_id > MAX_VALID_DEVICE_ID {
                return Err(SignalProtocolError::InvalidState(
                    "sealed_sender_multi_recipient_encrypt",
                    format!("destination {destination} has invalid device ID"),
                ));
            }
            serialized.push(device_id.try_into().expect("just checked range"));
            serialized.extend_from_slice(&their_registration_id.to_be_bytes());
        }

        let c_i = sealed_sender_v2::apply_agreement_xor(
            &e,
            their_identity.public_key(),
            Direction::Sending,
            &m,
        )?;
        serialized.extend_from_slice(&c_i);

        let at_i = sealed_sender_v2::compute_authentication_tag(
            &our_identity,
            their_identity,
            Direction::Sending,
            e_pub,
            &c_i,
        )?;
        serialized.extend_from_slice(&at_i);

        Ok(())
    };

    let process_chunk =
        |serialized: &mut Vec<u8>, chunk: &[(IdentityKey, Range<usize>)]| -> Result<()> {
            for (their_identity, destination_range) in chunk {
                let these_destinations = &destinations[destination_range.clone()];
                let these_sessions = &destination_sessions[destination_range.clone()];
                serialize_recipient_destinations_into(
                    serialized,
                    these_destinations,
                    these_sessions,
                    their_identity,
                )?;
            }
            Ok(())
        };

    let mut serialized: Vec<u8> = vec![SEALED_SENDER_V2_SERVICE_ID_FULL_VERSION];

    let count_of_recipients = identity_keys_and_ranges.len() + excluded_recipients.len();
    prost::encode_length_delimiter(count_of_recipients, &mut serialized)
        .expect("can always resize a Vec");

    // Fan out to N threads, like Rayon would. But don't bother for less than 6 items.
    let parallelism = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let chunk_size = std::cmp::max(6, identity_keys_and_ranges.len().div_ceil(parallelism));

    if parallelism == 1 || chunk_size >= identity_keys_and_ranges.len() {
        process_chunk(&mut serialized, &identity_keys_and_ranges)?;
    } else {
        let mut chunks = identity_keys_and_ranges.chunks(chunk_size);
        // We'll process the first chunk on the current thread once we've spawned all the others.
        let first_chunk = chunks.next().expect("at least one chunk, tested above");

        let mut all_outputs = Vec::new();
        all_outputs.resize_with(chunks.len(), || Ok(vec![]));

        rayon::scope(|scope| -> Result<()> {
            let mut outputs = &mut all_outputs[..];
            for chunk in chunks {
                let (next_output, remaining_outputs) = outputs
                    .split_first_mut()
                    .expect("as many outputs as remaining chunks");
                scope.spawn(|_| {
                    let mut serialized = vec![];
                    *next_output = process_chunk(&mut serialized, chunk).map(|_| serialized);
                });
                outputs = remaining_outputs;
            }

            process_chunk(&mut serialized, first_chunk)
        })?;

        for output in all_outputs {
            serialized.extend(output?);
        }
    }

    for excluded in excluded_recipients {
        serialized.extend_from_slice(&excluded.service_id_fixed_width_binary());
        serialized.push(0);
    }

    serialized.extend_from_slice(e_pub.public_key_bytes());
    serialized.extend_from_slice(&ciphertext);

    Ok(serialized)
}

/// Represents a single recipient in an SSv2 SentMessage.
///
/// See [`SealedSenderV2SentMessage`].
pub struct SealedSenderV2SentMessageRecipient<'a> {
    /// The recipient's devices and their registration IDs. May be empty.
    pub devices: Vec<(DeviceId, u16)>,
    /// A concatenation of the `C_i` and `AT_i` SSv2 fields for this recipient, or an empty slice if
    /// the recipient has no devices.
    c_and_at: &'a [u8],
}

/// A parsed representation of a Sealed Sender v2 SentMessage.
///
/// This only parses enough to fan out the message as a series of ReceivedMessages.
pub struct SealedSenderV2SentMessage<'a> {
    /// The full message, for calculating offsets.
    full_message: &'a [u8],
    /// The version byte at the head of the message.
    pub version: u8,
    /// The parsed list of recipients, grouped by ServiceId.
    ///
    /// The map is ordered by when a recipient first appears in the full message, even if they
    /// appear again later with more devices. This makes iteration over the full set of recipients
    /// deterministic.
    pub recipients: IndexMap<ServiceId, SealedSenderV2SentMessageRecipient<'a>>,
    /// A concatenation of the `e_pub` and `message` SSv2 fields for this recipient.
    shared_bytes: &'a [u8],
}

impl<'a> SealedSenderV2SentMessage<'a> {
    /// Parses the message, or produces an error if the message is invalid.
    pub fn parse(data: &'a [u8]) -> Result<Self> {
        if data.is_empty() {
            return Err(SignalProtocolError::InvalidSealedSenderMessage(
                "Message was empty".to_owned(),
            ));
        }

        let version = data[0];
        if !matches!(
            version,
            SEALED_SENDER_V2_UUID_FULL_VERSION | SEALED_SENDER_V2_SERVICE_ID_FULL_VERSION
        ) {
            return Err(SignalProtocolError::UnknownSealedSenderVersion(version));
        }

        fn advance<'a, const N: usize>(buf: &mut &'a [u8]) -> Result<&'a [u8; N]> {
            if N > buf.len() {
                return Err(SignalProtocolError::InvalidProtobufEncoding);
            }
            // TODO: Replace with split_array_ref or split_first_chunk when stabilized.
            let (prefix, remaining) = buf.split_at(N);
            *buf = remaining;
            Ok(prefix.try_into().expect("checked length"))
        }
        fn decode_varint(buf: &mut &[u8]) -> Result<u32> {
            let result: usize = prost::decode_length_delimiter(*buf)
                .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)?;
            *buf = &buf[prost::length_delimiter_len(result)..];
            result
                .try_into()
                .map_err(|_| SignalProtocolError::InvalidProtobufEncoding)
        }

        let mut remaining = &data[1..];
        let recipient_count = decode_varint(&mut remaining)?
            .try_into()
            .unwrap_or(usize::MAX);

        // Cap our preallocated capacity; anything higher than this is *probably* a mistake, but
        // could just be a very large message.
        // (Callers can of course refuse to process messages with too many recipients.)
        let mut recipients: IndexMap<ServiceId, SealedSenderV2SentMessageRecipient<'a>> =
            IndexMap::with_capacity(std::cmp::min(recipient_count as usize, 6000));
        for _ in 0..recipient_count {
            let service_id = if version == SEALED_SENDER_V2_UUID_FULL_VERSION {
                // The original version of SSv2 assumed ACIs here, and only encoded the raw UUID.
                ServiceId::from(Aci::from_uuid_bytes(*advance::<
                    { std::mem::size_of::<uuid::Bytes>() },
                >(&mut remaining)?))
            } else {
                ServiceId::parse_from_service_id_fixed_width_binary(advance::<
                    { std::mem::size_of::<ServiceIdFixedWidthBinaryBytes>() },
                >(
                    &mut remaining
                )?)
                .ok_or(SignalProtocolError::InvalidProtobufEncoding)?
            };
            let mut devices = Vec::new();
            loop {
                let device_id: u32 = advance::<1>(&mut remaining)?[0].into();
                if device_id == 0 {
                    if !devices.is_empty() {
                        return Err(SignalProtocolError::InvalidProtobufEncoding);
                    }
                    break;
                }
                if device_id > MAX_VALID_DEVICE_ID {
                    return Err(SignalProtocolError::InvalidProtobufEncoding);
                }
                let registration_id_and_has_more =
                    u16::from_be_bytes(*advance::<2>(&mut remaining)?);
                devices.push((
                    device_id.into(),
                    registration_id_and_has_more & VALID_REGISTRATION_ID_MASK,
                ));
                let has_more = (registration_id_and_has_more & 0x8000) != 0;
                if !has_more {
                    break;
                }
            }

            let c_and_at: &[u8] = if devices.is_empty() {
                &[]
            } else {
                advance::<{ sealed_sender_v2::MESSAGE_KEY_LEN + sealed_sender_v2::AUTH_TAG_LEN }>(
                    &mut remaining,
                )?
            };

            match recipients.entry(service_id) {
                indexmap::map::Entry::Occupied(mut existing) => {
                    if existing.get().devices.is_empty() || devices.is_empty() {
                        return Err(SignalProtocolError::InvalidSealedSenderMessage(
                            "recipient redundantly encoded as empty".to_owned(),
                        ));
                    }
                    // We don't unique the recipient devices; the server is going to check this
                    // against the account's canonical list of devices anyway.
                    existing.get_mut().devices.extend(devices);
                    // Note that we don't check that c_and_at matches. Any case where it doesn't
                    // match would already result in a decryption error for at least one of the
                    // recipient's devices, though.
                }
                indexmap::map::Entry::Vacant(entry) => {
                    entry.insert(SealedSenderV2SentMessageRecipient { devices, c_and_at });
                }
            };
        }

        if remaining.len() < sealed_sender_v2::PUBLIC_KEY_LEN {
            return Err(SignalProtocolError::InvalidProtobufEncoding);
        }

        Ok(Self {
            full_message: data,
            version,
            recipients,
            shared_bytes: remaining,
        })
    }

    /// Returns a slice of slices that, when concatenated, form the ReceivedMessage appropriate for
    /// `recipient`.
    ///
    /// If `recipient` is not one of the recipients in `self`, the resulting message will not be
    /// decryptable.
    #[inline]
    pub fn received_message_parts_for_recipient(
        &self,
        recipient: &SealedSenderV2SentMessageRecipient<'a>,
    ) -> impl AsRef<[&[u8]]> {
        // Why not use `IntoIterator<Item = &[u8]>` as the result? Because the `concat` method on
        // slices is more efficient when the caller just wants a `Vec<u8>`.
        // Why use SEALED_SENDER_V2_UUID_FULL_VERSION as the version? Because the ReceivedMessage
        // format hasn't changed since then.
        [
            &[SEALED_SENDER_V2_UUID_FULL_VERSION],
            recipient.c_and_at,
            self.shared_bytes,
        ]
    }

    /// Returns the offset of `addr` within `self.full_message`, or `None` if `addr` does not lie
    /// within `self.full_message`.
    ///
    /// A stripped-down version of [a dormant Rust RFC][subslice-offset].
    ///
    /// [subslice-offset]: https://github.com/rust-lang/rfcs/pull/2796
    #[inline]
    fn offset_within_full_message(&self, addr: *const u8) -> Option<usize> {
        // Arithmetic on addresses is valid for offsets within a byte array.
        // If addr < start, we'll wrap around to a very large value, which will be out of range just
        // like if addr > end.
        let offset = (addr as usize).wrapping_sub(self.full_message.as_ptr() as usize);
        // We *do* want to allow the "one-past-the-end" offset here, because the offset might be
        // used as part of a range (e.g. 0..end).
        if offset <= self.full_message.len() {
            debug_assert!(
                offset == self.full_message.len() || std::ptr::eq(&self.full_message[offset], addr)
            );
            Some(offset)
        } else {
            None
        }
    }

    /// Returns the range within the full message of `recipient`'s user-specific key material.
    ///
    /// This can be concatenated as `[version, recipient_key_material, shared_bytes]` to produce a
    /// valid SSv2 ReceivedMessage, the payload delivered to recipients.
    ///
    /// **Panics** if `recipient` is not one of the recipients in `self`.
    pub fn range_for_recipient_key_material(
        &self,
        recipient: &SealedSenderV2SentMessageRecipient<'a>,
    ) -> Range<usize> {
        if recipient.c_and_at.is_empty() {
            return 0..0;
        }
        let offset = self
            .offset_within_full_message(recipient.c_and_at.as_ptr())
            .expect("'recipient' is not one of the recipients in this SealedSenderV2SentMessage");
        let end_offset = offset.saturating_add(recipient.c_and_at.len());
        assert!(
            end_offset <= self.full_message.len(),
            "invalid 'recipient' passed to range_for_recipient_key_material"
        );
        offset..end_offset
    }

    /// Returns the offset of the shared bytes within the full message.
    ///
    /// This can be concatenated as `[version, recipient_key_material, shared_bytes]` to produce a
    /// valid SSv2 ReceivedMessage, the payload delivered to recipients.
    pub fn offset_of_shared_bytes(&self) -> usize {
        debug_assert_eq!(
            self.full_message.as_ptr_range().end,
            self.shared_bytes.as_ptr_range().end,
            "SealedSenderV2SentMessage parsed incorrectly"
        );
        self.offset_within_full_message(self.shared_bytes.as_ptr())
            .expect("constructed correctly")
    }
}

/// Decrypt the payload of a sealed-sender message in either the v1 or v2 format.
///
/// [`sealed_sender_decrypt`] consumes the output of this method to validate the sender's identity
/// before decrypting the underlying message.
pub async fn sealed_sender_decrypt_to_usmc(
    ciphertext: &[u8],
    identity_store: &dyn IdentityKeyStore,
) -> Result<UnidentifiedSenderMessageContent> {
    let our_identity = identity_store.get_identity_key_pair().await?;

    match UnidentifiedSenderMessage::deserialize(ciphertext)? {
        UnidentifiedSenderMessage::V1 {
            ephemeral_public,
            encrypted_static,
            encrypted_message,
        } => {
            let eph_keys = sealed_sender_v1::EphemeralKeys::calculate(
                &our_identity.into(),
                &ephemeral_public,
                Direction::Receiving,
            )?;

            let message_key_bytes = match crypto::aes256_ctr_hmacsha256_decrypt(
                &encrypted_static,
                &eph_keys.cipher_key,
                &eph_keys.mac_key,
            ) {
                Ok(plaintext) => plaintext,
                Err(crypto::DecryptionError::BadKeyOrIv) => {
                    unreachable!("just derived these keys; they should be valid");
                }
                Err(crypto::DecryptionError::BadCiphertext(msg)) => {
                    log::error!("failed to decrypt sealed sender v1 message key: {}", msg);
                    return Err(SignalProtocolError::InvalidSealedSenderMessage(
                        "failed to decrypt sealed sender v1 message key".to_owned(),
                    ));
                }
            };

            let static_key = PublicKey::try_from(&message_key_bytes[..])?;

            let static_keys = sealed_sender_v1::StaticKeys::calculate(
                &our_identity,
                &static_key,
                &eph_keys.chain_key,
                &encrypted_static,
            )?;

            let message_bytes = match crypto::aes256_ctr_hmacsha256_decrypt(
                &encrypted_message,
                &static_keys.cipher_key,
                &static_keys.mac_key,
            ) {
                Ok(plaintext) => plaintext,
                Err(crypto::DecryptionError::BadKeyOrIv) => {
                    unreachable!("just derived these keys; they should be valid");
                }
                Err(crypto::DecryptionError::BadCiphertext(msg)) => {
                    log::error!(
                        "failed to decrypt sealed sender v1 message contents: {}",
                        msg
                    );
                    return Err(SignalProtocolError::InvalidSealedSenderMessage(
                        "failed to decrypt sealed sender v1 message contents".to_owned(),
                    ));
                }
            };

            let usmc = UnidentifiedSenderMessageContent::deserialize(&message_bytes)?;

            if !bool::from(message_key_bytes.ct_eq(&usmc.sender()?.key()?.serialize())) {
                return Err(SignalProtocolError::InvalidSealedSenderMessage(
                    "sender certificate key does not match message key".to_string(),
                ));
            }

            Ok(usmc)
        }
        UnidentifiedSenderMessage::V2 {
            ephemeral_public,
            encrypted_message_key,
            authentication_tag,
            encrypted_message,
        } => {
            let m = sealed_sender_v2::apply_agreement_xor(
                &our_identity.into(),
                &ephemeral_public,
                Direction::Receiving,
                encrypted_message_key,
            )?;

            let keys = sealed_sender_v2::DerivedKeys::new(&m);
            if !bool::from(keys.derive_e().public_key.ct_eq(&ephemeral_public)) {
                return Err(SignalProtocolError::InvalidSealedSenderMessage(
                    "derived ephemeral key did not match key provided in message".to_string(),
                ));
            }

            let mut message_bytes = Vec::from(encrypted_message);
            Aes256GcmSiv::new(&keys.derive_k().into())
                .decrypt_in_place(
                    // There's no nonce because the key is already one-use.
                    &aes_gcm_siv::Nonce::default(),
                    // And there's no associated data.
                    &[],
                    &mut message_bytes,
                )
                .map_err(|err| {
                    SignalProtocolError::InvalidSealedSenderMessage(format!(
                        "failed to decrypt inner message: {}",
                        err
                    ))
                })?;

            let usmc = UnidentifiedSenderMessageContent::deserialize(&message_bytes)?;

            let at = sealed_sender_v2::compute_authentication_tag(
                &our_identity,
                &usmc.sender()?.key()?.into(),
                Direction::Receiving,
                &ephemeral_public,
                encrypted_message_key,
            )?;
            if !bool::from(authentication_tag.ct_eq(&at)) {
                return Err(SignalProtocolError::InvalidSealedSenderMessage(
                    "sender certificate key does not match authentication tag".to_string(),
                ));
            }

            Ok(usmc)
        }
    }
}

#[derive(Debug)]
pub struct SealedSenderDecryptionResult {
    pub sender_uuid: String,
    pub sender_e164: Option<String>,
    pub device_id: DeviceId,
    pub message: Vec<u8>,
}

impl SealedSenderDecryptionResult {
    pub fn sender_uuid(&self) -> Result<&str> {
        Ok(self.sender_uuid.as_ref())
    }

    pub fn sender_e164(&self) -> Result<Option<&str>> {
        Ok(self.sender_e164.as_deref())
    }

    pub fn device_id(&self) -> Result<DeviceId> {
        Ok(self.device_id)
    }

    pub fn message(&self) -> Result<&[u8]> {
        Ok(self.message.as_ref())
    }
}

/// Decrypt a Sealed Sender message `ciphertext` in either the v1 or v2 format, validate its sender
/// certificate, and then decrypt the inner message payload.
///
/// This method calls [`sealed_sender_decrypt_to_usmc`] to extract the sender information, including
/// the embedded [`SenderCertificate`]. The sender certificate (signed by the [`ServerCertificate`])
/// is then validated against the `trust_root` baked into the client to ensure that the sender's
/// identity was not forged.
#[allow(clippy::too_many_arguments)]
pub async fn sealed_sender_decrypt(
    ciphertext: &[u8],
    trust_root: &PublicKey,
    timestamp: Timestamp,
    local_e164: Option<String>,
    local_uuid: String,
    local_device_id: DeviceId,
    identity_store: &mut dyn IdentityKeyStore,
    session_store: &mut dyn SessionStore,
    pre_key_store: &mut dyn PreKeyStore,
    signed_pre_key_store: &dyn SignedPreKeyStore,
    kyber_pre_key_store: &mut dyn KyberPreKeyStore,
) -> Result<SealedSenderDecryptionResult> {
    let usmc = sealed_sender_decrypt_to_usmc(ciphertext, identity_store).await?;

    if !usmc.sender()?.validate(trust_root, timestamp)? {
        return Err(SignalProtocolError::InvalidSealedSenderMessage(
            "trust root validation failed".to_string(),
        ));
    }

    let is_local_uuid = local_uuid == usmc.sender()?.sender_uuid()?;

    let is_local_e164 = match (local_e164, usmc.sender()?.sender_e164()?) {
        (Some(l), Some(s)) => l == s,
        (_, _) => false,
    };

    if (is_local_e164 || is_local_uuid) && usmc.sender()?.sender_device_id()? == local_device_id {
        return Err(SignalProtocolError::SealedSenderSelfSend);
    }

    let mut rng = rand::rngs::OsRng;

    let remote_address = ProtocolAddress::new(
        usmc.sender()?.sender_uuid()?.to_string(),
        usmc.sender()?.sender_device_id()?,
    );

    let message = match usmc.msg_type()? {
        CiphertextMessageType::Whisper => {
            let ctext = SignalMessage::try_from(usmc.contents()?)?;
            session_cipher::message_decrypt_signal(
                &ctext,
                &remote_address,
                session_store,
                identity_store,
                &mut rng,
            )
            .await?
        }
        CiphertextMessageType::PreKey => {
            let ctext = PreKeySignalMessage::try_from(usmc.contents()?)?;
            session_cipher::message_decrypt_prekey(
                &ctext,
                &remote_address,
                session_store,
                identity_store,
                pre_key_store,
                signed_pre_key_store,
                kyber_pre_key_store,
                &mut rng,
            )
            .await?
        }
        msg_type => {
            return Err(SignalProtocolError::InvalidMessage(
                msg_type,
                "unexpected message type for sealed_sender_decrypt",
            ));
        }
    };

    Ok(SealedSenderDecryptionResult {
        sender_uuid: usmc.sender()?.sender_uuid()?.to_string(),
        sender_e164: usmc.sender()?.sender_e164()?.map(|s| s.to_string()),
        device_id: usmc.sender()?.sender_device_id()?,
        message,
    })
}

#[test]
fn test_lossless_round_trip() -> Result<()> {
    let trust_root = PrivateKey::deserialize(&[0u8; 32])?;

    // To test a hypothetical addition of a new field:
    //
    // Step 1: temporarily add a new field to the .proto.
    //
    //    --- a/rust/protocol/src/proto/sealed_sender.proto
    //    +++ b/rust/protocol/src/proto/sealed_sender.proto
    //    @@ -26,3 +26,4 @@ message SenderCertificate {
    //             optional bytes             identityKey   = 4;
    //             optional ServerCertificate signer        = 5;
    //    +        optional string someFakeField = 999;
    //     }
    //
    // Step 2: Add `some_fake_field: None` to the above construction of
    // proto::sealed_sender::sender_certificate::Certificate.
    //
    // Step 3: Serialize and print out the new fixture data (uncomment the following)
    //
    // let mut rng = rand::rngs::OsRng;
    // let server_key = KeyPair::generate(&mut rng);
    // let sender_key = KeyPair::generate(&mut rng);
    //
    // let server_cert =
    //     ServerCertificate::new(1, server_key.public_key, &trust_root, &mut rng)?;
    //
    // let sender_cert = proto::sealed_sender::sender_certificate::Certificate {
    //     sender_uuid: Some("aaaaaaaa-7000-11eb-b32a-33b8a8a487a6".to_string()),
    //     sender_e164: None,
    //     sender_device: Some(1),
    //     expires: Some(31337),
    //     identity_key: Some(sender_key.public_key.serialize().to_vec()),
    //     signer: Some(server_cert.to_protobuf()?),
    //     some_fake_field: Some("crashing right down".to_string()),
    // };
    //
    // eprintln!("<SNIP>");
    // let serialized_certificate_data = sender_cert.encode_to_vec();
    // let certificate_data_encoded = hex::encode(&serialized_certificate_data);
    // eprintln!("let certificate_data_encoded = \"{}\";", certificate_data_encoded);
    //
    // let certificate_signature = server_key.calculate_signature(&serialized_certificate_data, &mut rng)?;
    // let certificate_signature_encoded = hex::encode(certificate_signature);
    // eprintln!("let certificate_signature_encoded = \"{}\";", certificate_signature_encoded);

    // Step 4: update the following *_encoded fixture data with the new values from above.
    let certificate_data_encoded = "100119697a0000000000002221056c9d1f8deb82b9a898f9c277a1b74989ec009afb5c0acb5e8e69e3d5ca29d6322a690a2508011221053b03ca070e6f6b2f271d32f27321689cdf4e59b106c10b58fbe15063ed868a5a124024bc92954e52ad1a105b5bda85c9db410dcfeb42a671b45a523b3a46e9594a8bde0efc671d8e8e046b32c67f59b80a46ffdf24071850779bc21325107902af89322461616161616161612d373030302d313165622d623332612d333362386138613438376136ba3e136372617368696e6720726967687420646f776e";
    let certificate_signature_encoded = "a22d8f86f5d00794f319add821e342c6ffffb6b34f741e569f8b321ab0255f2d1757ecf648e53a3602cae8f09b3fc80dcf27534d67efd272b6739afc31f75c8c";

    // The rest of the test should be stable.
    let certificate_data = hex::decode(certificate_data_encoded).expect("valid hex");
    let certificate_signature = hex::decode(certificate_signature_encoded).expect("valid hex");

    let sender_certificate_data = proto::sealed_sender::SenderCertificate {
        certificate: Some(certificate_data),
        signature: Some(certificate_signature),
    };

    let sender_certificate =
        SenderCertificate::deserialize(&sender_certificate_data.encode_to_vec())?;
    assert!(sender_certificate.validate(
        &trust_root.public_key()?,
        Timestamp::from_epoch_millis(31336)
    )?);
    Ok(())
}
