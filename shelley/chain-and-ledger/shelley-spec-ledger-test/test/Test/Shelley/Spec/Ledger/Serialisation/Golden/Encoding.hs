{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Golden tests that check CBOR token encoding.
module Test.Shelley.Spec.Ledger.Serialisation.Golden.Encoding (tests) where

import Cardano.Binary
  ( Annotator,
    Decoder,
    DecoderError,
    FromCBOR (..),
    ToCBOR (..),
    decodeAnnotator,
    decodeFullDecoder,
    toCBOR,
  )
import Cardano.Crypto.DSIGN (encodeSignedDSIGN, encodeVerKeyDSIGN)
import qualified Cardano.Crypto.Hash as Monomorphic
import Cardano.Crypto.KES (SignedKES)
import Cardano.Crypto.VRF (CertifiedVRF)
import Cardano.Ledger.Address
  ( Addr (..),
  )
import Cardano.Ledger.AuxiliaryData (hashAuxiliaryData)
import Cardano.Ledger.BaseTypes
  ( BoundedRational (..),
    Network (..),
    Nonce (..),
    StrictMaybe (..),
    UnitInterval,
    mkNonceFromNumber,
    textToDns,
    textToUrl,
  )
import Cardano.Ledger.Coin (Coin (..), DeltaCoin (..))
import Cardano.Ledger.Credential (Credential (..), StakeReference (..))
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Era (Crypto (..))
import Cardano.Ledger.Hashes (EraIndependentTxBody)
import Cardano.Ledger.Keys
  ( Hash,
    KeyHash (..),
    KeyPair (..),
    KeyRole (..),
    SignKeyKES,
    SignKeyVRF,
    SignedDSIGN,
    VKey (..),
    VerKeyKES,
    VerKeyVRF,
    asWitness,
    encodeSignedKES,
    hashKey,
    hashVerKeyVRF,
    hashWithSerialiser,
    sKey,
    signedDSIGN,
    signedKES,
    vKey,
  )
import Cardano.Ledger.SafeHash (SafeHash, extractHash, hashAnnotated)
import Cardano.Ledger.Serialization
  ( FromCBORGroup (..),
    ToCBORGroup (..),
    decodeMapTraverse,
    ipv4ToBytes,
  )
import Cardano.Ledger.Shelley (ShelleyEra)
import Cardano.Ledger.Shelley.Constraints (UsesTxBody)
import Cardano.Ledger.Slot (BlockNo (..), EpochNo (..), SlotNo (..))
import Cardano.Prelude (LByteString)
import Codec.CBOR.Encoding (Encoding (..), Tokens (..))
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS (pack)
import Data.Coerce (coerce)
import Data.Default.Class (def)
import Data.IP (toIPv4)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe (fromJust)
import Data.Ratio ((%))
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import Data.String (fromString)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.API
  ( MultiSig,
    ScriptHash,
  )
import Shelley.Spec.Ledger.BlockChain
  ( BHBody (..),
    BHeader (..),
    Block (..),
    HashHeader (..),
    PrevHash (..),
    TxSeq (..),
    bbHash,
    bhash,
    bheaderBlockNo,
    bheaderEta,
    bheaderL,
    bheaderOCert,
    bheaderPrev,
    bheaderSlotNo,
    bheaderVk,
    bheaderVrfVk,
    bprotver,
    bsize,
    mkSeed,
    seedEta,
    seedL,
  )
import Shelley.Spec.Ledger.Delegation.Certificates
  ( pattern DeRegKey,
    pattern Delegate,
    pattern GenesisDelegCert,
    pattern MIRCert,
    pattern PoolDistr,
    pattern RegKey,
    pattern RegPool,
    pattern RetirePool,
  )
import Shelley.Spec.Ledger.EpochBoundary
  ( BlocksMade (..),
    PulsingStakeDistr (..),
    SnapShot (..),
    SnapShots (..),
    Stake (..),
  )
import Shelley.Spec.Ledger.LedgerState
  ( AccountState (..),
    EpochState (..),
    NewEpochState (..),
    PulsingRewUpdate (Complete),
    RewardUpdate (..),
  )
import qualified Shelley.Spec.Ledger.Metadata as MD
import Shelley.Spec.Ledger.OCert
  ( KESPeriod (..),
    OCert,
    OCertSignable (..),
    pattern OCert,
  )
import Shelley.Spec.Ledger.PParams
  ( PParams' (..),
    PParamsUpdate,
    ProtVer (..),
    emptyPParams,
    pattern ProposedPPUpdates,
    pattern Update,
  )
import Shelley.Spec.Ledger.Rewards ()
import Shelley.Spec.Ledger.Scripts (pattern RequireSignature)
import Shelley.Spec.Ledger.Tx (Tx (..), WitnessSet, WitnessSetHKD (..), hashScript)
import Shelley.Spec.Ledger.TxBody
  ( MIRPot (..),
    MIRTarget (..),
    PoolMetadata (..),
    StakePoolRelay (..),
    TxBody (..),
    TxId,
    TxIn (..),
    TxOut (..),
    Wdrl (..),
    WitVKey (..),
    _poolCost,
    _poolId,
    _poolMD,
    _poolMDHash,
    _poolMDUrl,
    _poolMargin,
    _poolOwners,
    _poolPledge,
    _poolRAcnt,
    _poolRelays,
    _poolVrf,
    pattern DCertDeleg,
    pattern DCertGenesis,
    pattern DCertMir,
    pattern DCertPool,
    pattern Delegation,
    pattern PoolParams,
    pattern RewardAcnt,
  )
import Shelley.Spec.Ledger.UTxO (makeWitnessVKey)
import Test.Cardano.Crypto.VRF.Fake (WithResult (..))
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C, C_Crypto, ExMock, Mock)
import Test.Shelley.Spec.Ledger.Generator.Core (PreAlonzo)
import Test.Shelley.Spec.Ledger.Generator.EraGen (genesisId)
import Test.Shelley.Spec.Ledger.Serialisation.GoldenUtils
  ( ToTokens (..),
    checkEncoding,
    checkEncodingCBOR,
    checkEncodingCBORAnnotated,
  )
import Test.Shelley.Spec.Ledger.Utils
import Test.Tasty (TestTree, testGroup)

-- ============================================

type MultiSigMap = Map.Map (ScriptHash C_Crypto) (MultiSig C_Crypto)

decodeMultiSigMap :: Decoder s (Annotator MultiSigMap)
decodeMultiSigMap = decodeMapTraverse (pure <$> fromCBOR) fromCBOR

deserializeMultiSigMap :: LByteString -> Either DecoderError MultiSigMap
deserializeMultiSigMap = decodeAnnotator "Map ScriptHash MultiSig" decodeMultiSigMap

checkEncodingCBORCBORGroup ::
  (FromCBORGroup a, ToCBORGroup a, Show a, Eq a) =>
  String ->
  a ->
  ToTokens ->
  TestTree
checkEncodingCBORCBORGroup name x t =
  let d = decodeFullDecoder (fromString name) fromCBORGroup
   in checkEncoding toCBORGroup d name x t

getRawKeyHash :: KeyHash 'Payment h -> ByteString
getRawKeyHash (KeyHash hsh) = Monomorphic.hashToBytes hsh

getRawNonce :: Nonce -> ByteString
getRawNonce (Nonce hsh) = Monomorphic.hashToBytes hsh
getRawNonce NeutralNonce = error "The neutral nonce has no bytes"

testGKey :: CC.Crypto crypto => GenesisKeyPair crypto
testGKey = KeyPair vk sk
  where
    (sk, vk) = mkGenKey (RawSeed 0 0 0 0 0)

testGKeyHash :: CC.Crypto crypto => KeyHash 'Genesis crypto
testGKeyHash = (hashKey . vKey) testGKey

testVRF :: CC.Crypto crypto => (SignKeyVRF crypto, VerKeyVRF crypto)
testVRF = mkVRFKeyPair (RawSeed 0 0 0 0 5)

testVRFKH :: forall crypto. CC.Crypto crypto => Hash crypto (VerKeyVRF crypto)
testVRFKH = hashVerKeyVRF $ snd (testVRF @crypto)

testTxb :: ShelleyTest era => TxBody era
testTxb =
  TxBody
    Set.empty
    StrictSeq.empty
    StrictSeq.empty
    (Wdrl Map.empty)
    (Coin 0)
    (SlotNo 0)
    SNothing
    SNothing

testTxbHash ::
  forall era.
  ShelleyTest era =>
  SafeHash (Crypto era) EraIndependentTxBody
testTxbHash = hashAnnotated $ testTxb @era

testKey1 :: CC.Crypto crypto => KeyPair 'Payment crypto
testKey1 = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (RawSeed 0 0 0 0 1)

testKey2 :: CC.Crypto crypto => KeyPair kr crypto
testKey2 = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (RawSeed 0 0 0 0 2)

testBlockIssuerKey :: CC.Crypto crypto => KeyPair 'BlockIssuer crypto
testBlockIssuerKey = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (RawSeed 0 0 0 0 4)

testStakePoolKey :: CC.Crypto crypto => KeyPair 'StakePool crypto
testStakePoolKey = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (RawSeed 0 0 0 0 5)

testGenesisDelegateKey ::
  CC.Crypto crypto =>
  KeyPair 'GenesisDelegate crypto
testGenesisDelegateKey = KeyPair vk sk
  where
    (sk, vk) = mkKeyPair (RawSeed 0 0 0 0 6)

testBlockIssuerKeyTokens :: Tokens -> Tokens
testBlockIssuerKeyTokens = e
  where
    (VKey vk) = vKey (testBlockIssuerKey @C_Crypto)
    Encoding e = encodeVerKeyDSIGN vk

testKey1SigToken ::
  forall era.
  (ShelleyTest era, Mock (Crypto era)) =>
  Tokens ->
  Tokens
testKey1SigToken = e
  where
    s =
      signedDSIGN @(Crypto era)
        (sKey $ testKey1 @(Crypto era))
        (extractHash (testTxbHash @era)) ::
        SignedDSIGN (Crypto era) (Hash (Crypto era) EraIndependentTxBody)
    Encoding e = encodeSignedDSIGN s

testOpCertSigTokens ::
  forall crypto.
  (Mock crypto) =>
  Tokens ->
  Tokens
testOpCertSigTokens = e
  where
    s =
      signedDSIGN @crypto
        (sKey $ testKey1 @crypto)
        (OCertSignable @crypto (snd $ testKESKeys @crypto) 0 (KESPeriod 0))
    Encoding e = encodeSignedDSIGN s

testKeyHash1 :: CC.Crypto crypto => KeyHash 'Payment crypto
testKeyHash1 = (hashKey . vKey) testKey1

testKeyHash2 :: CC.Crypto crypto => KeyHash 'Staking crypto
testKeyHash2 = (hashKey . vKey) testKey2

testKESKeys :: CC.Crypto crypto => (SignKeyKES crypto, VerKeyKES crypto)
testKESKeys = mkKESKeyPair (RawSeed 0 0 0 0 3)

testAddrE :: CC.Crypto crypto => Addr crypto
testAddrE =
  Addr
    Testnet
    (KeyHashObj testKeyHash1)
    StakeRefNull

testPayCred :: forall crypto. CC.Crypto crypto => Credential 'Payment crypto
testPayCred = KeyHashObj (testKeyHash1 @crypto)

testStakeCred :: forall crypto. CC.Crypto crypto => Credential 'Staking crypto
testStakeCred = KeyHashObj $ testKeyHash2 @crypto

testScript :: forall crypto. CC.Crypto crypto => MultiSig crypto
testScript = RequireSignature $ asWitness (testKeyHash1 @crypto)

testScriptHash :: forall crypto. CC.Crypto crypto => ScriptHash crypto
testScriptHash = hashScript @(ShelleyEra crypto) testScript

testScript2 :: forall crypto. CC.Crypto crypto => MultiSig crypto
testScript2 = RequireSignature $ asWitness (testKeyHash2 @crypto)

testHeaderHash ::
  forall crypto.
  CC.Crypto crypto =>
  HashHeader crypto
testHeaderHash =
  HashHeader $
    coerce
      (hashWithSerialiser toCBOR 0 :: Hash crypto Int)

testBHB ::
  forall era crypto.
  ( Era era,
    PreAlonzo era,
    UsesTxBody era,
    ExMock crypto,
    crypto ~ Crypto era
  ) =>
  BHBody crypto
testBHB =
  BHBody
    { bheaderBlockNo = BlockNo 44,
      bheaderSlotNo = SlotNo 33,
      bheaderPrev = BlockHash testHeaderHash,
      bheaderVk = vKey testBlockIssuerKey,
      bheaderVrfVk = snd $ testVRF @crypto,
      bheaderEta =
        mkCertifiedVRF
          ( WithResult
              (mkSeed seedEta (SlotNo 33) (mkNonceFromNumber 0))
              1
          )
          (fst $ testVRF @crypto),
      bheaderL =
        mkCertifiedVRF
          ( WithResult
              (mkSeed seedL (SlotNo 33) (mkNonceFromNumber 0))
              1
          )
          (fst $ testVRF @crypto),
      bsize = 0,
      bhash = bbHash @era $ TxSeq @era StrictSeq.empty,
      bheaderOCert =
        OCert
          (snd $ testKESKeys @crypto)
          0
          (KESPeriod 0)
          ( signedDSIGN @crypto
              (sKey $ testKey1 @crypto)
              (OCertSignable (snd $ testKESKeys @crypto) 0 (KESPeriod 0))
          ),
      bprotver = ProtVer 0 0
    }

testBHBSigTokens ::
  forall era.
  ( Era era,
    PreAlonzo era,
    ExMock (Crypto era),
    UsesTxBody era
  ) =>
  Tokens ->
  Tokens
testBHBSigTokens = e
  where
    s =
      signedKES @(CC.KES (Crypto era))
        ()
        0
        (testBHB @era)
        (fst $ testKESKeys @(Crypto era))
    Encoding e = encodeSignedKES s

tests :: TestTree
tests =
  testGroup
    "CBOR Serialization Tests (Encoding)"
    [ checkEncodingCBOR
        "list"
        [1 :: Integer]
        (T (TkListBegin . TkInteger 1 . TkBreak)),
      checkEncodingCBOR
        "set"
        (Set.singleton (1 :: Integer))
        (T (TkTag 258 . TkListLen 1 . TkInteger 1)),
      checkEncodingCBOR
        "map"
        (Map.singleton (1 :: Integer) (1 :: Integer))
        (T (TkMapLen 1 . TkInteger 1 . TkInteger 1)),
      checkEncodingCBOR
        "coin"
        (Coin 30)
        (T (TkWord64 30)),
      checkEncodingCBOR
        "rational"
        (unsafeBoundRational (1 % 2) :: UnitInterval)
        (T (TkTag 30 . TkListLen 2 . TkWord64 1 . TkWord64 2)),
      checkEncodingCBOR
        "slot"
        (SlotNo 7)
        (T (TkWord64 7)),
      checkEncodingCBOR
        "neutral_nonce"
        NeutralNonce
        (T (TkListLen 1 . TkWord 0)),
      checkEncodingCBOR
        "nonce"
        (mkNonceFromNumber 99)
        (T (TkListLen 2 . TkWord 1 . TkBytes (getRawNonce $ mkNonceFromNumber 99))),
      checkEncodingCBOR
        "key_hash"
        (testKeyHash1 @C_Crypto)
        (T (TkBytes (getRawKeyHash (testKeyHash1 @C_Crypto)))),
      checkEncodingCBOR
        "credential_key_hash"
        (testPayCred @C_Crypto)
        (T (TkListLen 2 . TkWord 0) <> S (testKeyHash1 @C_Crypto)),
      checkEncodingCBOR
        "txin"
        (TxIn @C_Crypto genesisId 0)
        (T (TkListLen 2) <> S (genesisId :: TxId C_Crypto) <> T (TkWord64 0)),
      let a = Addr Testnet testPayCred StakeRefNull
       in checkEncodingCBOR
            "txout"
            (TxOut @C a (Coin 2))
            ( T (TkListLen 2)
                <> S a
                <> S (Coin 2)
            ),
      case makeWitnessVKey @C_Crypto (testTxbHash @C) testKey1 of
        w@(WitVKey vk _sig) ->
          checkEncodingCBORAnnotated
            "vkey_witnesses"
            w -- Transaction _witnessVKeySet element
            ( T (TkListLen 2)
                <> S vk -- vkey
                <> T (testKey1SigToken @C) -- signature
            ),
      checkEncoding
        toCBOR
        deserializeMultiSigMap
        "script_hash_to_scripts"
        (Map.singleton (hashScript @C testScript) testScript) -- Transaction _witnessMSigMap
        ( T (TkMapLen 1)
            <> S (hashScript @C testScript)
            <> S (testScript @C_Crypto)
        ),
      -- checkEncodingCBOR "withdrawal_key"
      let r = RewardAcnt Testnet (testStakeCred @C_Crypto)
       in checkEncodingCBOR
            "withdrawal"
            (Map.singleton r (Coin 123))
            ( (T $ TkMapLen 1)
                <> S r
                <> S (Coin 123)
            ),
      -- checkEncodingCBOR "withdrawal_script"
      --
      let r = RewardAcnt Testnet (ScriptHashObj (testScriptHash @C_Crypto))
       in checkEncodingCBOR
            "withdrawal"
            (Map.singleton r (Coin 123))
            ( (T $ TkMapLen 1)
                <> S r
                <> S (Coin 123)
            ),
      checkEncodingCBOR
        "register_stake_reference"
        (DCertDeleg (RegKey (testStakeCred @C_Crypto)))
        ( T (TkListLen 2)
            <> T (TkWord 0) -- Reg cert
            <> S (testStakeCred @C_Crypto) -- keyhash
        ),
      checkEncodingCBOR
        "deregister_stake_reference"
        (DCertDeleg (DeRegKey (testStakeCred @C_Crypto)))
        ( T (TkListLen 2)
            <> T (TkWord 1) -- DeReg cert
            <> S (testStakeCred @C_Crypto) -- keyhash
        ),
      checkEncodingCBOR
        "stake_delegation"
        (DCertDeleg (Delegate (Delegation (testStakeCred @C_Crypto) (hashKey . vKey $ testStakePoolKey))))
        ( T
            ( TkListLen 3
                . TkWord 2 -- delegation cert with key
            )
            <> S (testStakeCred @C_Crypto)
            <> S (hashKey . vKey $ testStakePoolKey @C_Crypto)
        ),
      -- checkEncodingCBOR "register-pool"
      let poolOwner = testKeyHash2 @C_Crypto
          poolMargin = unsafeBoundRational 0.7
          poolRAcnt = RewardAcnt Testnet (testStakeCred @C_Crypto)
          poolPledge = Coin 11
          poolCost = Coin 55
          poolUrl = "pool.io"
          poolMDHash = BS.pack "{}"
          ipv4 = toIPv4 [127, 0, 0, 1]
          ipv4Bytes = ipv4ToBytes . toIPv4 $ [127, 0, 0, 1]
          poolRelays =
            StrictSeq.fromList
              [ SingleHostAddr SNothing (SJust ipv4) SNothing,
                SingleHostName (SJust 42) $ Maybe.fromJust $ textToDns "singlehost.relay.com",
                MultiHostName $ Maybe.fromJust $ textToDns "multihost.relay.com"
              ]
       in checkEncodingCBOR
            "register_pool"
            ( DCertPool
                ( RegPool
                    ( PoolParams
                        { _poolId = hashKey . vKey $ testStakePoolKey,
                          _poolVrf = testVRFKH @C_Crypto,
                          _poolPledge = poolPledge,
                          _poolCost = poolCost,
                          _poolMargin = poolMargin,
                          _poolRAcnt = poolRAcnt,
                          _poolOwners = Set.singleton poolOwner,
                          _poolRelays = poolRelays,
                          _poolMD =
                            SJust $
                              PoolMetadata
                                { _poolMDUrl = Maybe.fromJust $ textToUrl poolUrl,
                                  _poolMDHash = poolMDHash
                                }
                        }
                    )
                )
            )
            ( T (TkListLen 10)
                <> T (TkWord 3) -- Reg Pool
                <> S (hashKey . vKey $ testStakePoolKey @C_Crypto) -- operator
                <> S (testVRFKH @C_Crypto) -- vrf keyhash
                <> S poolPledge -- pledge
                <> S poolCost -- cost
                <> S poolMargin -- margin
                <> S poolRAcnt -- reward acct
                <> T (TkListLen 1)
                <> S poolOwner -- owners
                <> T (TkListLen 3) -- relays
                <> T (TkListLen 4 . TkWord 0 . TkNull . TkBytes ipv4Bytes . TkNull)
                <> T (TkListLen 3 . TkWord 1 . (TkWord 42) . TkString ("singlehost.relay.com"))
                <> T (TkListLen 2 . TkWord 2 . TkString ("multihost.relay.com"))
                <> T (TkListLen 2) -- metadata present
                <> S poolUrl -- metadata url
                <> S poolMDHash -- metadata hash
            ),
      checkEncodingCBOR
        "retire_pool"
        ( DCertPool
            ( RetirePool @C_Crypto
                (hashKey . vKey $ testStakePoolKey @C_Crypto)
                (EpochNo 1729)
            )
        )
        ( T
            ( TkListLen 3
                . TkWord 4 -- Pool Retire
            )
            <> S (hashKey . vKey $ testStakePoolKey @C_Crypto) -- key hash
            <> S (EpochNo 1729) -- epoch
        ),
      checkEncodingCBOR
        "genesis_delegation"
        ( DCertGenesis
            ( GenesisDelegCert @C_Crypto
                testGKeyHash
                (hashKey . vKey $ testGenesisDelegateKey @C_Crypto)
                (testVRFKH @C_Crypto)
            )
        )
        ( T
            ( TkListLen 4
                . TkWord 5 -- genesis delegation cert
            )
            <> S (testGKeyHash @C_Crypto) -- delegator credential
            <> S (hashKey . vKey $ testGenesisDelegateKey @C_Crypto) -- delegatee key hash
            <> S (testVRFKH @C_Crypto) -- delegatee vrf key hash
        ),
      -- checkEncodingCBOR "mir"
      let rws = StakeAddressesMIR $ Map.singleton (testStakeCred @C_Crypto) (DeltaCoin 77)
       in checkEncodingCBOR
            "mir"
            (DCertMir (MIRCert ReservesMIR rws))
            ( T
                ( TkListLen 2
                    . TkWord 6 -- make instantaneous rewards cert
                    . TkListLen 2
                    . TkWord 0 -- take from the reserves
                )
                <> S rws
            ),
      checkEncodingCBOR
        "pparams_update_key_deposit_only"
        ( PParams
            { _minfeeA = SNothing,
              _minfeeB = SNothing,
              _maxBBSize = SNothing,
              _maxTxSize = SNothing,
              _maxBHSize = SNothing,
              _keyDeposit = SJust (Coin 5),
              _poolDeposit = SNothing,
              _eMax = SNothing,
              _nOpt = SNothing,
              _a0 = SNothing,
              _rho = SNothing,
              _tau = SNothing,
              _d = SNothing,
              _extraEntropy = SNothing,
              _protocolVersion = SNothing,
              _minUTxOValue = SNothing,
              _minPoolCost = SNothing
            } ::
            PParamsUpdate C
        )
        ((T $ TkMapLen 1 . TkWord 5) <> S (Coin 5)),
      -- checkEncodingCBOR "pparams_update_all"
      let minfeea = 0
          minfeeb = 1
          maxbbsize = 2
          maxtxsize = 3
          maxbhsize = 4
          keydeposit = Coin 5
          pooldeposit = Coin 6
          emax = EpochNo 7
          nopt = 8
          a0 = unsafeBoundRational $ 1 % 6
          rho = unsafeBoundRational $ 1 % 6
          tau = unsafeBoundRational $ 1 % 7
          d = unsafeBoundRational $ 1 % 9
          extraEntropy = NeutralNonce
          protocolVersion = ProtVer 0 1
          minUTxOValue = Coin 121
          minPoolCost = Coin 987
       in checkEncodingCBOR
            "pparams_update_all"
            ( PParams
                { _minfeeA = SJust minfeea,
                  _minfeeB = SJust minfeeb,
                  _maxBBSize = SJust maxbbsize,
                  _maxTxSize = SJust maxtxsize,
                  _maxBHSize = SJust maxbhsize,
                  _keyDeposit = SJust keydeposit,
                  _poolDeposit = SJust pooldeposit,
                  _eMax = SJust emax,
                  _nOpt = SJust nopt,
                  _a0 = SJust a0,
                  _rho = SJust rho,
                  _tau = SJust tau,
                  _d = SJust d,
                  _extraEntropy = SJust extraEntropy,
                  _protocolVersion = SJust protocolVersion,
                  _minUTxOValue = SJust minUTxOValue,
                  _minPoolCost = SJust minPoolCost
                } ::
                PParamsUpdate C
            )
            ( (T $ TkMapLen 17)
                <> (T $ TkWord 0)
                <> S minfeea
                <> (T $ TkWord 1)
                <> S minfeeb
                <> (T $ TkWord 2)
                <> S maxbbsize
                <> (T $ TkWord 3)
                <> S maxtxsize
                <> (T $ TkWord 4)
                <> S maxbhsize
                <> (T $ TkWord 5)
                <> S keydeposit
                <> (T $ TkWord 6)
                <> S pooldeposit
                <> (T $ TkWord 7)
                <> S emax
                <> (T $ TkWord 8)
                <> S nopt
                <> (T $ TkWord 9 . TkTag 30)
                <> S (unboundRational a0)
                <> (T $ TkWord 10)
                <> S rho
                <> (T $ TkWord 11)
                <> S tau
                <> (T $ TkWord 12)
                <> S d
                <> (T $ TkWord 13)
                <> S extraEntropy
                <> (T $ TkWord 14)
                <> S protocolVersion
                <> (T $ TkWord 15)
                <> S minUTxOValue
                <> (T $ TkWord 16)
                <> S minPoolCost
            ),
      -- checkEncodingCBOR "full_update"
      let ppup =
            ProposedPPUpdates @C
              ( Map.singleton
                  (testGKeyHash @C_Crypto)
                  ( PParams
                      { _minfeeA = SNothing,
                        _minfeeB = SNothing,
                        _maxBBSize = SNothing,
                        _maxTxSize = SNothing,
                        _maxBHSize = SNothing,
                        _keyDeposit = SNothing,
                        _poolDeposit = SNothing,
                        _eMax = SNothing,
                        _nOpt = SJust 100,
                        _a0 = SNothing,
                        _rho = SNothing,
                        _tau = SNothing,
                        _d = SNothing,
                        _extraEntropy = SNothing,
                        _protocolVersion = SNothing,
                        _minUTxOValue = SNothing,
                        _minPoolCost = SNothing
                      }
                  )
              )
          e = EpochNo 0
       in checkEncodingCBOR
            "full_update"
            (Update ppup e)
            ( (T $ TkListLen 2)
                <> S ppup
                <> S e
            ),
      -- checkEncodingCBOR "minimal_txn_body"
      let tin = TxIn @C_Crypto genesisId 1
          tout = TxOut @C testAddrE (Coin 2)
       in checkEncodingCBORAnnotated
            "txbody"
            ( TxBody @C -- minimal transaction body
                (Set.fromList [tin])
                (StrictSeq.singleton tout)
                StrictSeq.empty
                (Wdrl Map.empty)
                (Coin 9)
                (SlotNo 500)
                SNothing
                SNothing
            )
            ( T (TkMapLen 4)
                <> T (TkWord 0) -- Tx Ins
                <> T (TkListLen 1)
                <> S tin
                <> T (TkWord 1) -- Tx Outs
                <> T (TkListLen 1)
                <> S tout
                <> T (TkWord 2) -- Tx Fee
                <> T (TkWord64 9)
                <> T (TkWord 3) -- Tx TTL
                <> T (TkWord64 500)
            ),
      -- checkEncodingCBOR "transaction_mixed"
      let tin = TxIn @C_Crypto genesisId 1
          tout = TxOut @C testAddrE (Coin 2)
          ra = RewardAcnt Testnet (KeyHashObj testKeyHash2)
          ras = Map.singleton ra (Coin 123)
          up =
            Update
              ( ProposedPPUpdates
                  ( Map.singleton
                      testGKeyHash
                      ( PParams
                          { _minfeeA = SNothing,
                            _minfeeB = SNothing,
                            _maxBBSize = SNothing,
                            _maxTxSize = SNothing,
                            _maxBHSize = SNothing,
                            _keyDeposit = SNothing,
                            _poolDeposit = SNothing,
                            _eMax = SNothing,
                            _nOpt = SJust 100,
                            _a0 = SNothing,
                            _rho = SNothing,
                            _tau = SNothing,
                            _d = SNothing,
                            _extraEntropy = SNothing,
                            _protocolVersion = SNothing,
                            _minUTxOValue = SNothing,
                            _minPoolCost = SNothing
                          }
                      )
                  )
              )
              (EpochNo 0)
       in checkEncodingCBORAnnotated
            "txbody_partial"
            ( TxBody @C -- transaction body with some optional components
                (Set.fromList [tin])
                (StrictSeq.singleton tout)
                StrictSeq.Empty
                (Wdrl ras)
                (Coin 9)
                (SlotNo 500)
                (SJust up)
                SNothing
            )
            ( T (TkMapLen 6)
                <> T (TkWord 0) -- Tx Ins
                <> T (TkListLen 1)
                <> S tin
                <> T (TkWord 1) -- Tx Outs
                <> T (TkListLen 1)
                <> S tout
                <> T (TkWord 2) -- Tx Fee
                <> S (Coin 9)
                <> T (TkWord 3) -- Tx TTL
                <> S (SlotNo 500)
                <> T (TkWord 5) -- Tx Reward Withdrawals
                <> S ras
                <> T (TkWord 6) -- Tx Update
                <> S up
            ),
      -- checkEncodingCBOR "full_txn_body"
      let tin = TxIn @C_Crypto genesisId 1
          tout = TxOut @C testAddrE (Coin 2)
          reg = DCertDeleg (RegKey (testStakeCred @C_Crypto))
          ra = RewardAcnt Testnet (KeyHashObj testKeyHash2)
          ras = Map.singleton ra (Coin 123)
          up =
            Update
              ( ProposedPPUpdates
                  ( Map.singleton
                      testGKeyHash
                      ( PParams
                          { _minfeeA = SNothing,
                            _minfeeB = SNothing,
                            _maxBBSize = SNothing,
                            _maxTxSize = SNothing,
                            _maxBHSize = SNothing,
                            _keyDeposit = SNothing,
                            _poolDeposit = SNothing,
                            _eMax = SNothing,
                            _nOpt = SJust 100,
                            _a0 = SNothing,
                            _rho = SNothing,
                            _tau = SNothing,
                            _d = SNothing,
                            _extraEntropy = SNothing,
                            _protocolVersion = SNothing,
                            _minUTxOValue = SNothing,
                            _minPoolCost = SNothing
                          }
                      )
                  )
              )
              (EpochNo 0)
          mdh = hashAuxiliaryData @C $ MD.Metadata $ Map.singleton 13 (MD.I 17)
       in checkEncodingCBORAnnotated
            "txbody_full"
            ( TxBody @C -- transaction body with all components
                (Set.fromList [tin])
                (StrictSeq.singleton tout)
                (StrictSeq.fromList [reg])
                (Wdrl ras)
                (Coin 9)
                (SlotNo 500)
                (SJust up)
                (SJust mdh)
            )
            ( T (TkMapLen 8)
                <> T (TkWord 0) -- Tx Ins
                <> T (TkListLen 1)
                <> S tin
                <> T (TkWord 1) -- Tx Outs
                <> T (TkListLen 1)
                <> S tout
                <> T (TkWord 2) -- Tx Fee
                <> S (Coin 9)
                <> T (TkWord 3) -- Tx TTL
                <> S (SlotNo 500)
                <> T (TkWord 4) -- Tx Certs
                <> T (TkListLen 1) -- Seq list begin
                <> S reg
                <> T (TkWord 5) -- Tx Reward Withdrawals
                <> S ras
                <> T (TkWord 6) -- Tx Update
                <> S up
                <> T (TkWord 7) -- Tx Metadata
                <> S mdh
            ),
      -- checkEncodingCBOR "minimal_txn"
      let txb =
            TxBody @C
              (Set.fromList [TxIn genesisId 1])
              (StrictSeq.singleton $ TxOut @C testAddrE (Coin 2))
              StrictSeq.empty
              (Wdrl Map.empty)
              (Coin 9)
              (SlotNo 500)
              SNothing
              SNothing
          txbh = (hashAnnotated txb)
          w = makeWitnessVKey @C_Crypto txbh testKey1
       in checkEncodingCBORAnnotated
            "tx_min"
            ( Tx @(ShelleyEra C_Crypto)
                txb
                (mempty {addrWits = Set.singleton w} :: Shelley.Spec.Ledger.Tx.WitnessSet C)
                SNothing
            )
            ( T (TkListLen 3)
                <> S txb
                <> T (TkMapLen 1)
                <> T (TkWord 0)
                <> T (TkListLen 1)
                <> S w
                <> T TkNull
            ),
      -- checkEncodingCBOR "full_txn"
      let txb =
            TxBody @C
              (Set.fromList [TxIn genesisId 1])
              (StrictSeq.singleton $ TxOut @C testAddrE (Coin 2))
              StrictSeq.empty
              (Wdrl Map.empty)
              (Coin 9)
              (SlotNo 500)
              SNothing
              SNothing
          txbh = (hashAnnotated txb)
          w = makeWitnessVKey @C_Crypto txbh testKey1
          s = Map.singleton (hashScript @C testScript) (testScript @C_Crypto)
          txwits :: Shelley.Spec.Ledger.Tx.WitnessSet C
          txwits = mempty {addrWits = Set.singleton w, scriptWits = s}
          md = (MD.Metadata @C) $ Map.singleton 17 (MD.I 42)
       in checkEncodingCBORAnnotated
            "tx_full"
            (Tx @(ShelleyEra C_Crypto) txb txwits (SJust md))
            ( T (TkListLen 3)
                <> S txb
                <> T (TkMapLen 2)
                <> T (TkWord 0)
                <> T (TkListLen 1)
                <> S w
                <> T (TkWord 1)
                <> T (TkListLen 1)
                <> S (testScript @C_Crypto)
                <> S md
            ),
      -- checkEncodingCBOR "block_header_body"
      let prevhash = BlockHash testHeaderHash
          vrfVkey = snd $ testVRF @C_Crypto
          slot = SlotNo 33
          nonce = mkSeed seedEta (SlotNo 33) (mkNonceFromNumber 0)
          nonceProof :: CertifiedVRF (CC.VRF C_Crypto) Nonce
          nonceProof =
            mkCertifiedVRF
              (WithResult nonce 1)
              (fst $ testVRF @C_Crypto)
          leaderValue = mkSeed seedL (SlotNo 33) (mkNonceFromNumber 0)
          leaderProof :: CertifiedVRF (CC.VRF C_Crypto) Natural
          leaderProof =
            mkCertifiedVRF
              (WithResult leaderValue 1)
              (fst $ testVRF @C_Crypto)
          size = 0
          blockNo = BlockNo 44
          bbhash = bbHash @C $ TxSeq StrictSeq.empty
          ocert :: OCert C_Crypto
          ocert =
            OCert
              (snd $testKESKeys @C_Crypto)
              0
              (KESPeriod 0)
              ( signedDSIGN @C_Crypto
                  (sKey (testBlockIssuerKey @C_Crypto))
                  (OCertSignable (snd $ testKESKeys @C_Crypto) 0 (KESPeriod 0))
              )
          protover = ProtVer 0 0
       in checkEncodingCBOR
            "block_header_body"
            ( BHBody
                { bheaderBlockNo = blockNo,
                  bheaderSlotNo = slot,
                  bheaderPrev = prevhash,
                  bheaderVk = vKey testBlockIssuerKey,
                  bheaderVrfVk = vrfVkey,
                  bheaderEta = nonceProof,
                  bheaderL = leaderProof,
                  bsize = size,
                  bhash = bbhash,
                  bheaderOCert = ocert,
                  bprotver = protover
                }
            )
            ( T (TkListLen $ 9 + 4 + 2)
                <> S blockNo
                <> S slot
                <> S prevhash
                <> T testBlockIssuerKeyTokens
                <> S vrfVkey
                <> S nonceProof
                <> S leaderProof
                <> S size
                <> S bbhash
                <> G ocert -- 5
                <> G protover -- 3
            ),
      -- checkEncodingCBOR "operational_cert"
      let vkHot = snd $ testKESKeys @C_Crypto
          counter = 0
          kesperiod = KESPeriod 0
          signature =
            signedDSIGN @C_Crypto
              (sKey $ testKey1 @C_Crypto)
              (OCertSignable (snd $ testKESKeys @C_Crypto) 0 (KESPeriod 0))
       in checkEncodingCBORCBORGroup
            "operational_cert"
            ( OCert @C_Crypto
                vkHot
                counter
                kesperiod
                signature
            )
            ( S vkHot
                <> S counter
                <> S kesperiod
                <> T (testOpCertSigTokens @C_Crypto)
            ),
      -- checkEncodingCBOR "block_header"
      let sig :: (SignedKES (CC.KES C_Crypto) (BHBody C_Crypto))
          sig = signedKES () 0 (testBHB @C) (fst $testKESKeys @C_Crypto)
       in checkEncodingCBORAnnotated
            "block_header"
            (BHeader (testBHB @C) sig)
            ( (T $ TkListLen 2)
                <> S (testBHB @C)
                <> T (testBHBSigTokens @C)
            ),
      -- checkEncodingCBOR "empty_block"
      let sig :: (SignedKES (CC.KES C_Crypto) (BHBody C_Crypto))
          sig = signedKES () 0 (testBHB @C) (fst $ testKESKeys @C_Crypto)
          bh = BHeader (testBHB @C) sig
          txns = TxSeq StrictSeq.Empty
       in checkEncodingCBORAnnotated
            "empty_block"
            (Block @C bh txns)
            ( (T $ TkListLen 4)
                <> S bh
                <> T (TkListLen 0 . TkListLen 0 . TkMapLen 0)
            ),
      -- checkEncodingCBOR "rich_block"
      let sig :: (SignedKES (CC.KES C_Crypto) (BHBody C_Crypto))
          sig = signedKES () 0 (testBHB @C) (fst $ testKESKeys @C_Crypto)
          bh = BHeader (testBHB @C) sig
          tin = Set.fromList [TxIn @C_Crypto genesisId 1]
          tout = StrictSeq.singleton $ TxOut @C testAddrE (Coin 2)
          txb s =
            TxBody @C
              tin
              tout
              StrictSeq.empty
              (Wdrl Map.empty)
              (Coin 9)
              (SlotNo s)
              SNothing
              SNothing
          txb1 = txb 500
          txb2 = txb 501
          txb3 = txb 502
          txb4 = txb 503
          txb5 = txb 504
          w1 = makeWitnessVKey (hashAnnotated txb1) testKey1
          w2 = makeWitnessVKey (hashAnnotated txb1) testKey2
          ws = Set.fromList [w1, w2]
          tx1 = Tx @C txb1 mempty {addrWits = Set.singleton w1} SNothing
          tx2 = Tx @C txb2 mempty {addrWits = ws} SNothing
          tx3 =
            Tx @C
              txb3
              mempty
                { scriptWits =
                    Map.singleton (hashScript @C testScript) testScript
                }
              SNothing
          ss =
            Map.fromList
              [ (hashScript @C testScript, testScript),
                (hashScript @C testScript2, testScript2)
              ]
          tx4 = Tx txb4 mempty {scriptWits = ss} SNothing
          tx5MD = MD.Metadata @C $ Map.singleton 17 (MD.I 42)
          tx5 = Tx txb5 mempty {addrWits = ws, scriptWits = ss} (SJust tx5MD)
          txns = TxSeq $ StrictSeq.fromList [tx1, tx2, tx3, tx4, tx5]
       in checkEncodingCBORAnnotated
            "rich_block"
            (Block @C bh txns)
            ( (T $ TkListLen 4)
                -- header
                <> S bh
                -- bodies
                <> T (TkListLen 5)
                <> S txb1
                <> S txb2
                <> S txb3
                <> S txb4
                <> S txb5
                -- witnesses
                <> T (TkListLen 5)
                -- tx 1, one key
                <> T (TkMapLen 1 . TkWord 0)
                <> T (TkListLen 1)
                <> S w1
                -- tx 2, two keys
                <> T (TkMapLen 1 . TkWord 0)
                <> T (TkListLen 2)
                -- The test is unfortunately sensitive to this ordering. TODO make it
                -- better
                <> S w2
                <> S w1
                -- tx 3, one script
                <> T (TkMapLen 1 . TkWord 1)
                <> T (TkListLen 1)
                <> S (testScript @C_Crypto)
                -- tx 4, two scripts
                <> T (TkMapLen 1 . TkWord 1)
                <> T (TkListLen 2)
                <> S (testScript2 @C_Crypto)
                <> S (testScript @C_Crypto)
                -- tx 5, two keys and two scripts
                <> T (TkMapLen 2)
                <> T (TkWord 0)
                <> T (TkListLen 2)
                <> S w2
                <> S w1
                <> T (TkWord 1)
                <> T (TkListLen 2)
                <> S (testScript2 @C_Crypto)
                <> S (testScript @C_Crypto)
                -- metadata
                <> T (TkMapLen 1)
                <> T (TkInt 4)
                <> S tx5MD
            ),
      checkEncodingCBOR
        "epoch"
        (EpochNo 13)
        (T (TkWord64 13)),
      let n = (17 :: Natural)
          bs = Map.singleton (hashKey . vKey $ testStakePoolKey @C_Crypto) n
       in checkEncodingCBOR
            "blocks_made"
            (BlocksMade bs)
            ( T (TkMapLen 1)
                <> S (hashKey . vKey $ testStakePoolKey @C_Crypto)
                <> S n
            ),
      checkEncodingCBOR
        "account_state"
        (AccountState (Coin 1) (Coin 2))
        ( T (TkListLen 2)
            <> S (Coin 1)
            <> S (Coin 2)
        ),
      let stk = Map.singleton (testStakeCred @C_Crypto) (Coin 13)
       in checkEncodingCBOR
            "stake"
            (Stake stk)
            ( T (TkMapLen 1)
                <> S (testStakeCred @C_Crypto)
                <> S (Coin 13)
            ),
      let mark' =
            SnapShot
              (Stake $ Map.singleton (testStakeCred @C_Crypto) (Coin 11))
              (Map.singleton (testStakeCred @C_Crypto) (hashKey $ vKey testStakePoolKey))
              ps
          mark = Completed mark'
          set =
            SnapShot
              (Stake $ Map.singleton (KeyHashObj testKeyHash2) (Coin 22))
              (Map.singleton (testStakeCred @C_Crypto) (hashKey $ vKey testStakePoolKey))
              ps
          go =
            SnapShot
              (Stake $ Map.singleton (testStakeCred @C_Crypto) (Coin 33))
              (Map.singleton (testStakeCred @C_Crypto) (hashKey $ vKey testStakePoolKey))
              ps
          params =
            PoolParams
              { _poolId = hashKey $ vKey testStakePoolKey,
                _poolVrf = testVRFKH @C_Crypto,
                _poolPledge = Coin 5,
                _poolCost = Coin 4,
                _poolMargin = unsafeBoundRational 0.7,
                _poolRAcnt = RewardAcnt Testnet (testStakeCred @C_Crypto),
                _poolOwners = Set.singleton testKeyHash2,
                _poolRelays = StrictSeq.empty,
                _poolMD =
                  SJust $
                    PoolMetadata
                      { _poolMDUrl = Maybe.fromJust $ textToUrl "web.site",
                        _poolMDHash = BS.pack "{}"
                      }
              }
          ps = Map.singleton (hashKey $ vKey testStakePoolKey) params
          fs = Coin 123
       in checkEncodingCBOR
            "snapshots"
            ((SnapShots mark set go fs) :: (SnapShots C))
            ( T (TkListLen 4)
                <> S mark'
                <> S set
                <> S go
                <> S fs
            ),
      let e = EpochNo 0
          ac = AccountState (Coin 100) (Coin 100)
          mark =
            SnapShot
              (Stake $ Map.singleton (testStakeCred @C_Crypto) (Coin 11))
              (Map.singleton (testStakeCred @C_Crypto) (hashKey $ vKey testStakePoolKey))
              ps
          set =
            SnapShot
              (Stake $ Map.singleton (KeyHashObj testKeyHash2) (Coin 22))
              (Map.singleton (testStakeCred @C_Crypto) (hashKey $ vKey testStakePoolKey))
              ps
          go =
            SnapShot
              (Stake $ Map.singleton (testStakeCred @C_Crypto) (Coin 33))
              (Map.singleton (testStakeCred @C_Crypto) (hashKey $ vKey testStakePoolKey))
              ps
          params =
            PoolParams
              { _poolId = hashKey $ vKey testStakePoolKey,
                _poolVrf = testVRFKH @C_Crypto,
                _poolPledge = Coin 5,
                _poolCost = Coin 4,
                _poolMargin = unsafeBoundRational 0.7,
                _poolRAcnt = RewardAcnt Testnet (testStakeCred @C_Crypto),
                _poolOwners = Set.singleton testKeyHash2,
                _poolRelays = StrictSeq.empty,
                _poolMD =
                  SJust $
                    PoolMetadata
                      { _poolMDUrl = Maybe.fromJust $ textToUrl "web.site",
                        _poolMDHash = BS.pack "{}"
                      }
              }
          ps = Map.singleton (hashKey $ vKey testStakePoolKey) params
          fs = Coin 123
          ss = SnapShots (Completed mark) set go fs
          ls = def
          pps = emptyPParams
          bs = Map.singleton (hashKey $ vKey testStakePoolKey) 1
          nm = def
          es = EpochState @C ac ss ls pps pps nm
          ru =
            ( Complete $
                RewardUpdate
                  { deltaT = DeltaCoin 100,
                    deltaR = DeltaCoin (-200),
                    rs = Map.empty,
                    deltaF = DeltaCoin (-10),
                    nonMyopic = nm
                  }
            )
          pd = PoolDistr @C_Crypto Map.empty
          nes =
            NewEpochState
              e
              (BlocksMade bs)
              (BlocksMade bs)
              es
              (SJust ru)
              pd
       in checkEncodingCBOR
            "new_epoch_state"
            nes
            ( T (TkListLen 6)
                <> S e
                <> S (BlocksMade @C_Crypto bs)
                <> S (BlocksMade @C_Crypto bs)
                <> S es
                <> S (SJust ru)
                <> S pd
            )
    ]
