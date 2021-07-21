{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators
  ( mkDummyHash,
    genCoherentBlock,
    genHash,
    genShelleyAddress,
    genByronAddress,
    MockGen,
    maxTxWits,
  )
where

import Cardano.Binary
  ( ToCBOR (..),
    toCBOR,
  )
import Cardano.Crypto.DSIGN.Class
  ( DSIGNAlgorithm,
    SignedDSIGN (..),
    rawDeserialiseSigDSIGN,
    rawDeserialiseVerKeyDSIGN,
    sizeSigDSIGN,
    sizeVerKeyDSIGN,
  )
import Cardano.Crypto.DSIGN.Mock (VerKeyDSIGN (..))
import Cardano.Crypto.Hash (HashAlgorithm, hashWithSerialiser)
import qualified Cardano.Crypto.Hash as Hash
import Cardano.Ledger.AuxiliaryData (AuxiliaryDataHash (..))
import Cardano.Ledger.BaseTypes
  ( ActiveSlotCoeff,
    DnsName,
    NonNegativeInterval,
    PositiveInterval,
    PositiveUnitInterval,
    UnitInterval,
    Url,
    mkActiveSlotCoeff,
    mkNonceFromNumber,
    promoteRatio,
    textToDns,
    textToUrl,
  )
import Cardano.Ledger.Coin (DeltaCoin (..))
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Crypto (DSIGN)
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era (Crypto, Era, SupportsSegWit (..), ValidateScript)
import Cardano.Ledger.SafeHash (HasAlgorithm, SafeHash, unsafeMakeSafeHash)
import Cardano.Ledger.Serialization (ToCBORGroup)
import Cardano.Ledger.Shelley.Constraints
  ( UsesScript,
    UsesTxBody,
    UsesTxOut,
    UsesValue,
  )
import Cardano.Slotting.Block (BlockNo (..))
import Cardano.Slotting.Slot (EpochNo (..), EpochSize (..), SlotNo (..))
import Control.SetAlgebra (biMapFromList)
import Control.State.Transition (STS (State))
import qualified Data.ByteString.Char8 as BS
import Data.Coerce (coerce)
import Data.IP (IPv4, IPv6, toIPv4, toIPv6)
import qualified Data.Map.Strict as Map (empty, fromList)
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Data.Ratio ((%))
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Text as T
import qualified Data.Time as Time
import qualified Data.Time.Calendar.OrdinalDate as Time
import Data.Typeable (Typeable)
import Data.Word (Word64, Word8)
import Generic.Random (genericArbitraryU)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.API hiding (SignedDSIGN, TxBody (..))
import Shelley.Spec.Ledger.Address.Bootstrap (ChainCode (..))
import Shelley.Spec.Ledger.Delegation.Certificates (IndividualPoolStake (..))
import Shelley.Spec.Ledger.EpochBoundary (BlocksMade (..))
import Shelley.Spec.Ledger.LedgerState (FutureGenDeleg)
import qualified Shelley.Spec.Ledger.Metadata as MD
import Shelley.Spec.Ledger.RewardProvenance
  ( Desirability (..),
    RewardProvenance (..),
    RewardProvenancePool (..),
  )
import Shelley.Spec.Ledger.RewardUpdate
  ( FreeVars (..),
    Pulser,
    PulsingRewUpdate (..),
    RewardAns (..),
    RewardPulser (..),
    RewardSnapShot (..),
  )
import Shelley.Spec.Ledger.Rewards
  ( Likelihood (..),
    LogWeight (..),
    PerformanceEstimate (..),
    Reward (..),
    RewardType (..),
  )
import qualified Shelley.Spec.Ledger.STS.Deleg as STS
import qualified Shelley.Spec.Ledger.STS.Delegs as STS
import qualified Shelley.Spec.Ledger.STS.Delpl as STS
import qualified Shelley.Spec.Ledger.STS.Ledger as STS
import qualified Shelley.Spec.Ledger.STS.Ledgers as STS
import qualified Shelley.Spec.Ledger.STS.Pool as STS
import qualified Shelley.Spec.Ledger.STS.Ppup as STS
import qualified Shelley.Spec.Ledger.STS.Prtcl as STS (PrtclState)
import qualified Shelley.Spec.Ledger.STS.Tickn as STS
import qualified Shelley.Spec.Ledger.STS.Utxow as STS
import Shelley.Spec.Ledger.Tx (WitnessSetHKD (WitnessSet), hashScript)
import Test.QuickCheck
  ( Arbitrary,
    Gen,
    Positive (..),
    arbitrary,
    choose,
    elements,
    genericShrink,
    listOf,
    oneof,
    recursivelyShrink,
    resize,
    shrink,
    vectorOf,
  )
import Test.QuickCheck.Gen (chooseAny)
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (Mock)
import Test.Shelley.Spec.Ledger.Generator.Constants (defaultConstants)
import Test.Shelley.Spec.Ledger.Generator.Core
  ( KeySpace (KeySpace_),
    geKeySpace,
    ksCoreNodes,
    mkBlock,
    mkBlockHeader,
    mkOCert,
  )
import Test.Shelley.Spec.Ledger.Generator.EraGen (EraGen)
import Test.Shelley.Spec.Ledger.Generator.Presets (coreNodeKeys, genEnv)
import Test.Shelley.Spec.Ledger.Serialisation.Generators.Bootstrap
  ( genBootstrapAddress,
    genSignature,
  )
import Test.Shelley.Spec.Ledger.Utils (unsafeBoundRational)

-- =======================================================

genHash :: forall a h. HashAlgorithm h => Gen (Hash.Hash h a)
genHash = mkDummyHash <$> arbitrary

mkDummyHash :: forall h a. HashAlgorithm h => Int -> Hash.Hash h a
mkDummyHash = coerce . hashWithSerialiser @h toCBOR

genSafeHash :: HasAlgorithm c => Gen (SafeHash c i)
genSafeHash = unsafeMakeSafeHash <$> arbitrary

{-------------------------------------------------------------------------------
  Generators

  These are generators for roundtrip tests, so the generated values are not
  necessarily valid
-------------------------------------------------------------------------------}

type MockGen era =
  ( Mock (Crypto era),
    Arbitrary (VerKeyDSIGN (DSIGN (Crypto era)))
  )

instance Mock crypto => Arbitrary (BHeader crypto) where
  arbitrary = do
    prevHash <- arbitrary :: Gen (HashHeader crypto)
    allPoolKeys <- elements (map snd (coreNodeKeys defaultConstants))
    curSlotNo <- SlotNo <$> choose (0, 10)
    curBlockNo <- BlockNo <$> choose (0, 100)
    epochNonce <- arbitrary :: Gen Nonce
    bodySize <- arbitrary
    bodyHash <- arbitrary
    let kesPeriod = 1
        keyRegKesPeriod = 1
        ocert = mkOCert allPoolKeys 1 (KESPeriod kesPeriod)
    return $
      mkBlockHeader
        prevHash
        allPoolKeys
        curSlotNo
        curBlockNo
        epochNonce
        kesPeriod
        keyRegKesPeriod
        ocert
        bodySize
        bodyHash

instance DSIGNAlgorithm crypto => Arbitrary (SignedDSIGN crypto a) where
  arbitrary =
    SignedDSIGN . fromJust . rawDeserialiseSigDSIGN
      <$> (genByteString . fromIntegral $ sizeSigDSIGN (Proxy @crypto))

instance DSIGNAlgorithm crypto => Arbitrary (VerKeyDSIGN crypto) where
  arbitrary =
    fromJust . rawDeserialiseVerKeyDSIGN
      <$> (genByteString . fromIntegral $ sizeVerKeyDSIGN (Proxy @crypto))

instance CC.Crypto crypto => Arbitrary (BootstrapWitness crypto) where
  arbitrary = do
    key <- arbitrary
    sig <- genSignature
    chainCode <- ChainCode <$> arbitrary
    attributes <- arbitrary
    pure $ BootstrapWitness key sig chainCode attributes

instance CC.Crypto crypto => Arbitrary (HashHeader crypto) where
  arbitrary = HashHeader <$> genHash

instance (Typeable kr, CC.Crypto crypto) => Arbitrary (WitVKey kr crypto) where
  arbitrary =
    WitVKey
      <$> arbitrary
      <*> arbitrary

instance CC.Crypto crypto => Arbitrary (Wdrl crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance (Era era, Mock (Crypto era)) => Arbitrary (ProposedPPUpdates era) where
  arbitrary = ProposedPPUpdates <$> pure Map.empty

instance (Era era, Mock (Crypto era)) => Arbitrary (Update era) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

maxMetadatumDepth :: Int
maxMetadatumDepth = 2

maxMetadatumListLens :: Int
maxMetadatumListLens = 5

sizedMetadatum :: Int -> Gen MD.Metadatum
sizedMetadatum 0 =
  oneof
    [ MD.I <$> arbitrary,
      MD.B <$> arbitrary,
      MD.S <$> (T.pack <$> arbitrary)
    ]
sizedMetadatum n =
  oneof
    [ MD.Map
        <$> ( zip
                <$> (resize maxMetadatumListLens (listOf (sizedMetadatum (n -1))))
                <*> (listOf (sizedMetadatum (n -1)))
            ),
      MD.List <$> resize maxMetadatumListLens (listOf (sizedMetadatum (n -1))),
      MD.I <$> arbitrary,
      MD.B <$> arbitrary,
      MD.S <$> (T.pack <$> arbitrary)
    ]

instance Arbitrary MD.Metadatum where
  arbitrary = sizedMetadatum maxMetadatumDepth

instance Arbitrary (MD.Metadata era) where
  arbitrary = MD.Metadata <$> arbitrary

maxTxWits :: Int
maxTxWits = 5

instance CC.Crypto crypto => Arbitrary (TxId crypto) where
  arbitrary = TxId <$> genSafeHash

instance CC.Crypto crypto => Arbitrary (TxIn crypto) where
  arbitrary =
    TxIn
      <$> (TxId <$> genSafeHash)
      <*> arbitrary

instance
  (UsesValue era, Mock (Crypto era), Arbitrary (Core.Value era)) =>
  Arbitrary (TxOut era)
  where
  arbitrary = TxOut <$> arbitrary <*> arbitrary

instance Arbitrary Nonce where
  arbitrary =
    oneof
      [ return NeutralNonce,
        mkNonceFromNumber <$> choose (1, 123 :: Word64)
      ]

instance Arbitrary UnitInterval where
  arbitrary = do
    x :: Word64 <- arbitrary
    Positive (y :: Word64) <- arbitrary
    pure $ unsafeBoundRational $ promoteRatio (if x > y then y % x else x % y)

instance Arbitrary PositiveUnitInterval where
  arbitrary = do
    Positive (x :: Word64) <- arbitrary
    Positive (y :: Word64) <- arbitrary
    pure $ unsafeBoundRational $ promoteRatio (if x > y then y % x else x % y)

instance Arbitrary PositiveInterval where
  arbitrary = do
    Positive (x :: Word64) <- arbitrary
    Positive (y :: Word64) <- arbitrary
    pure $ unsafeBoundRational $ promoteRatio (x % y)

instance Arbitrary NonNegativeInterval where
  arbitrary = do
    x :: Word64 <- arbitrary
    Positive (y :: Word64) <- arbitrary
    pure $ unsafeBoundRational $ promoteRatio (x % y)

instance CC.Crypto crypto => Arbitrary (KeyHash a crypto) where
  arbitrary = KeyHash <$> genHash

instance CC.Crypto crypto => Arbitrary (WitHashes crypto) where
  arbitrary = genericArbitraryU

instance Arbitrary MIRPot where
  arbitrary = genericArbitraryU

instance CC.Crypto crypto => Arbitrary (MIRTarget crypto) where
  arbitrary =
    oneof
      [ StakeAddressesMIR <$> arbitrary,
        SendToOppositePotMIR <$> arbitrary
      ]

instance Arbitrary Natural where
  arbitrary = fromInteger <$> choose (0, 1000)

instance Arbitrary STS.VotingPeriod where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary Coin where
  -- Cannot be negative even though it is an 'Integer'
  arbitrary = Coin <$> choose (0, 1000)
  shrink (Coin i) = Coin <$> shrink i

instance Arbitrary DeltaCoin where
  arbitrary = DeltaCoin <$> choose (-1000, 1000)

instance Arbitrary SlotNo where
  -- Cannot be negative even though it is an 'Integer'
  arbitrary = SlotNo <$> choose (1, 100000)

instance Arbitrary EpochNo where
  -- Cannot be negative even though it is an 'Integer'
  arbitrary = EpochNo <$> choose (1, 100000)

instance CC.Crypto crypto => Arbitrary (Addr crypto) where
  arbitrary = oneof [genShelleyAddress, genByronAddress]

genShelleyAddress :: CC.Crypto crypto => Gen (Addr crypto)
genShelleyAddress = Addr <$> arbitrary <*> arbitrary <*> arbitrary

genByronAddress :: Gen (Addr crypto)
genByronAddress = AddrBootstrap <$> genBootstrapAddress

instance CC.Crypto crypto => Arbitrary (StakeReference crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (Credential r crypto) where
  arbitrary =
    oneof
      [ ScriptHashObj . ScriptHash <$> genHash,
        KeyHashObj <$> arbitrary
      ]

instance Arbitrary Ptr where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (RewardAcnt crypto) where
  arbitrary = RewardAcnt <$> arbitrary <*> arbitrary

instance Arbitrary Network where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance (Arbitrary (VerKeyDSIGN (DSIGN crypto))) => Arbitrary (VKey kd crypto) where
  arbitrary = VKey <$> arbitrary

instance Arbitrary ProtVer where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (ScriptHash crypto) where
  arbitrary = ScriptHash <$> genHash

instance CC.Crypto crypto => Arbitrary (AuxiliaryDataHash crypto) where
  arbitrary = AuxiliaryDataHash <$> genSafeHash

instance HashAlgorithm h => Arbitrary (Hash.Hash h a) where
  arbitrary = genHash

instance Arbitrary STS.TicknState where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (STS.PrtclState crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance
  ( UsesTxOut era,
    UsesValue era,
    Mock (Crypto era),
    Arbitrary (Core.TxOut era)
  ) =>
  Arbitrary (UTxO era)
  where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (PState crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (InstantaneousRewards crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (FutureGenDeleg crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (GenDelegs crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (GenDelegPair crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (DState crypto) where
  arbitrary =
    DState
      <$> arbitrary
      <*> arbitrary
      <*> (biMapFromList const <$> arbitrary)
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance CC.Crypto crypto => Arbitrary (DelegCert crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (Delegation crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (PoolCert crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (GenesisDelegCert crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (MIRCert crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (DCert crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance (Era era, Mock (Crypto era)) => Arbitrary (PPUPState era) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (DPState crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance
  ( UsesTxOut era,
    UsesValue era,
    Mock (Crypto era),
    Arbitrary (Core.TxOut era),
    Arbitrary (State (Core.EraRule "PPUP" era))
  ) =>
  Arbitrary (UTxOState era)
  where
  arbitrary = genericArbitraryU
  shrink = recursivelyShrink

-- The 'genericShrink' function returns first the immediate subterms of a
-- value (in case it is a recursive data-type), and then shrinks the value
-- itself. Since 'UTxOState' is not a recursive data-type, there are no
-- subterms, and we can use `recursivelyShrink` directly. This is particularly
-- important when abstracting away the different fields of the ledger state,
-- since the generic subterms instances will overlap due to GHC not having
-- enough context to infer if 'a' and 'b' are the same types (since in this
-- case this will depend on the definition of 'era').
--
-- > instance OVERLAPPING_ GSubtermsIncl (K1 i a) a where
-- > instance OVERLAPPING_ GSubtermsIncl (K1 i a) b where

instance
  ( UsesTxOut era,
    UsesValue era,
    Mock (Crypto era),
    Arbitrary (Core.TxOut era),
    Arbitrary (State (Core.EraRule "PPUP" era))
  ) =>
  Arbitrary (LedgerState era)
  where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance
  ( UsesTxOut era,
    UsesValue era,
    Mock (Crypto era),
    Arbitrary (Core.TxOut era),
    Arbitrary (Core.Value era),
    Arbitrary (Core.PParams era),
    Arbitrary (State (Core.EraRule "PPUP" era)),
    EraGen era
  ) =>
  Arbitrary (NewEpochState era)
  where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (BlocksMade crypto) where
  arbitrary = BlocksMade <$> arbitrary

instance CC.Crypto crypto => Arbitrary (PoolDistr crypto) where
  arbitrary =
    PoolDistr . Map.fromList
      <$> listOf ((,) <$> arbitrary <*> genVal)
    where
      genVal = IndividualPoolStake <$> arbitrary <*> genHash

instance
  ( UsesTxOut era,
    UsesValue era,
    Mock (Crypto era),
    Arbitrary (Core.TxOut era),
    Arbitrary (Core.Value era),
    Arbitrary (Core.PParams era),
    Arbitrary (State (Core.EraRule "PPUP" era)),
    EraGen era
  ) =>
  Arbitrary (EpochState era)
  where
  arbitrary =
    EpochState
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Arbitrary RewardType where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (Reward crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (RewardUpdate crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary a => Arbitrary (StrictMaybe a) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (OBftSlot crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary ActiveSlotCoeff where
  arbitrary = mkActiveSlotCoeff <$> arbitrary

instance Arbitrary Likelihood where
  arbitrary = Likelihood <$> arbitrary

instance Arbitrary LogWeight where
  arbitrary = LogWeight <$> arbitrary

instance CC.Crypto crypto => Arbitrary (NonMyopic crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (SnapShot crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance CC.Crypto crypto => Arbitrary (SnapShots crypto) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary PerformanceEstimate where
  arbitrary = PerformanceEstimate <$> arbitrary

instance CC.Crypto crypto => Arbitrary (Stake crypto) where
  arbitrary = Stake <$> arbitrary

instance CC.Crypto crypto => Arbitrary (PoolParams crypto) where
  arbitrary =
    PoolParams
      <$> arbitrary
      <*> genHash
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Arbitrary PoolMetadata where
  arbitrary = (`PoolMetadata` BS.pack "bytestring") <$> arbitrary

instance Arbitrary Url where
  arbitrary = return . fromJust $ textToUrl "text"

instance Arbitrary a => Arbitrary (StrictSeq a) where
  arbitrary = StrictSeq.forceToStrict <$> arbitrary
  shrink = map StrictSeq.forceToStrict . shrink . StrictSeq.fromStrict

instance Arbitrary StakePoolRelay where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary Port where
  arbitrary = fromIntegral @Word8 @Port <$> arbitrary

instance Arbitrary IPv4 where
  arbitrary = pure $ toIPv4 [192, 0, 2, 1]

instance Arbitrary IPv6 where
  arbitrary = pure $ toIPv6 [0x2001, 0xDB8, 0, 0, 0, 0, 0, 1]

instance Arbitrary DnsName where
  arbitrary = pure . fromJust $ textToDns "foo.example.com"

instance Arbitrary AccountState where
  arbitrary = genericArbitraryU
  shrink = genericShrink

maxMultiSigDepth :: Int
maxMultiSigDepth = 3

maxMultiSigListLens :: Int
maxMultiSigListLens = 5

sizedMultiSig :: CC.Crypto crypto => Int -> Gen (MultiSig crypto)
sizedMultiSig 0 = RequireSignature <$> arbitrary
sizedMultiSig n =
  oneof
    [ RequireSignature <$> arbitrary,
      RequireAllOf <$> resize maxMultiSigListLens (listOf (sizedMultiSig (n -1))),
      RequireAnyOf <$> resize maxMultiSigListLens (listOf (sizedMultiSig (n -1))),
      RequireMOf <$> arbitrary <*> resize maxMultiSigListLens (listOf (sizedMultiSig (n -1)))
    ]

instance CC.Crypto crypto => Arbitrary (MultiSig crypto) where
  arbitrary = sizedMultiSig maxMultiSigDepth

-- |
-- Generate a byte string of a given size.
genByteString :: Int -> Gen BS.ByteString
genByteString size = do
  ws <- vectorOf size (chooseAny @Char)
  return $ BS.pack ws

genUTCTime :: Gen Time.UTCTime
genUTCTime = do
  year <- arbitrary
  dayOfYear <- arbitrary
  diff <- arbitrary
  pure $
    Time.UTCTime
      (Time.fromOrdinalDate year dayOfYear)
      (Time.picosecondsToDiffTime diff)

instance
  (Mock (Crypto era), EraGen era, Arbitrary (PParams era)) =>
  Arbitrary (ShelleyGenesis era)
  where
  arbitrary =
    ShelleyGenesis
      <$> genUTCTime -- sgSystemStart
      <*> arbitrary -- sgNetworkMagic
      <*> arbitrary -- sgNetworkId
      <*> arbitrary -- sgActiveSlotsCoeff
      <*> arbitrary -- sgSecurityParam
      <*> (EpochSize <$> arbitrary) -- sgEpochLength
      <*> arbitrary -- sgSlotsPerKESPeriod
      <*> arbitrary -- sgMaxKESEvolutions
      <*> (fromInteger <$> arbitrary) -- sgSlotLength
      <*> arbitrary -- sgUpdateQuorum
      <*> arbitrary -- sgMaxLovelaceSupply
      <*> arbitrary -- sgProtocolParams
      <*> arbitrary -- sgGenDelegs
      <*> arbitrary -- sgInitialFunds
      <*> (ShelleyGenesisStaking <$> arbitrary <*> arbitrary) -- sgStaking

instance
  ( UsesScript era,
    Mock (Crypto era),
    ValidateScript era,
    Arbitrary (Core.Script era)
  ) =>
  Arbitrary (WitnessSet era)
  where
  arbitrary =
    WitnessSet
      <$> arbitrary
      <*> (mscriptsToWits <$> arbitrary)
      <*> arbitrary
    where
      mscriptsToWits = Map.fromList . map (\s -> (hashScript @era s, s))

instance Era era => Arbitrary (STS.PpupPredicateFailure era) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Era era => Arbitrary (STS.PoolPredicateFailure era) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance
  ( Era era,
    Mock (Crypto era),
    Arbitrary (STS.PredicateFailure (Core.EraRule "POOL" era)),
    Arbitrary (STS.PredicateFailure (Core.EraRule "DELEG" era))
  ) =>
  Arbitrary (STS.DelplPredicateFailure era)
  where
  arbitrary = genericArbitraryU
  shrink = recursivelyShrink

instance
  (Era era, Mock (Crypto era)) =>
  Arbitrary (STS.DelegPredicateFailure era)
  where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance
  ( Era era,
    Mock (Crypto era),
    Arbitrary (STS.PredicateFailure (Core.EraRule "DELPL" era))
  ) =>
  Arbitrary (STS.DelegsPredicateFailure era)
  where
  arbitrary = genericArbitraryU
  shrink = recursivelyShrink

instance
  ( Era era,
    Arbitrary (STS.PredicateFailure (Core.EraRule "LEDGER" era))
  ) =>
  Arbitrary (STS.LedgersPredicateFailure era)
  where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance
  ( Era era,
    Arbitrary (STS.PredicateFailure (Core.EraRule "DELEGS" era)),
    Arbitrary (STS.PredicateFailure (Core.EraRule "UTXOW" era))
  ) =>
  Arbitrary (STS.LedgerPredicateFailure era)
  where
  arbitrary = genericArbitraryU
  shrink _ = []

instance
  ( Era era,
    Arbitrary (STS.PredicateFailure (Core.EraRule "UTXO" era))
  ) =>
  Arbitrary (STS.UtxowPredicateFailure era)
  where
  arbitrary = genericArbitraryU
  shrink _ = []

genTx ::
  ( Era era,
    Arbitrary (Core.TxBody era),
    Arbitrary (Core.AuxiliaryData era),
    Arbitrary (Core.Witnesses era),
    ToCBOR (Core.AuxiliaryData era), -- for Tx Pattern
    ToCBOR (Core.TxBody era), -- for Tx Pattern
    ToCBOR (Core.Witnesses era) -- for Tx Pattern
  ) =>
  Gen (Tx era)
genTx =
  Tx
    <$> arbitrary
    <*> resize maxTxWits arbitrary
    <*> arbitrary

genBlock ::
  forall era.
  ( Era era,
    ToCBORGroup (TxSeq era),
    Mock (Crypto era),
    Arbitrary (Core.Tx era)
  ) =>
  Gen (Block era)
genBlock = Block <$> arbitrary <*> (toTxSeq @era <$> arbitrary)

-- | For some purposes, a totally random block generator may not be suitable.
-- There are tests in the ouroboros-network repository, for instance, that
-- perform some integrity checks on the generated blocks.
--
-- For other purposes, such as the serialization tests in this repository,
-- 'genBlock' is more appropriate.
--
-- This generator uses 'mkBlock' provide more coherent blocks.
genCoherentBlock ::
  forall era.
  ( EraGen era,
    ToCBORGroup (TxSeq era),
    Mock (Crypto era),
    UsesTxBody era,
    Arbitrary (Core.Tx era)
  ) =>
  Gen (Block era)
genCoherentBlock = do
  let KeySpace_ {ksCoreNodes} = geKeySpace (genEnv p)
  prevHash <- arbitrary :: Gen (HashHeader (Crypto era))
  allPoolKeys <- elements (map snd ksCoreNodes)
  txs <- arbitrary
  curSlotNo <- SlotNo <$> choose (0, 10)
  curBlockNo <- BlockNo <$> choose (0, 100)
  epochNonce <- arbitrary :: Gen Nonce
  let kesPeriod = 1
      keyRegKesPeriod = 1
      ocert = mkOCert allPoolKeys 1 (KESPeriod kesPeriod)
  return $
    mkBlock
      prevHash
      allPoolKeys
      txs
      curSlotNo
      curBlockNo
      epochNonce
      kesPeriod
      keyRegKesPeriod
      ocert
  where
    p :: Proxy era
    p = Proxy

instance
  ( Era era,
    Arbitrary (Core.TxBody era),
    Arbitrary (Core.Value era),
    Arbitrary (Core.AuxiliaryData era),
    Arbitrary (Core.Script era),
    Arbitrary (Core.Witnesses era),
    ToCBOR (Core.AuxiliaryData era), -- for Tx Pattern
    ToCBOR (Core.TxBody era), -- for Tx Pattern
    ToCBOR (Core.Witnesses era) -- for Tx Pattern
  ) =>
  Arbitrary (Tx era)
  where
  arbitrary = genTx

instance
  ( UsesTxBody era,
    ToCBORGroup (TxSeq era),
    SupportsSegWit era,
    Mock (Crypto era),
    Arbitrary (Core.Tx era)
  ) =>
  Arbitrary (Block era)
  where
  arbitrary = genBlock

instance
  ( Era era,
    Arbitrary (STS.PredicateFailure (Core.EraRule "LEDGER" era))
  ) =>
  Arbitrary (ApplyTxError era)
  where
  arbitrary = ApplyTxError <$> arbitrary
  shrink (ApplyTxError xs) = [ApplyTxError xs' | xs' <- shrink xs]

instance Arbitrary Desirability where
  arbitrary = Desirability <$> arbitrary <*> arbitrary

instance
  Mock crypto =>
  Arbitrary (RewardProvenancePool crypto)
  where
  arbitrary =
    RewardProvenancePool
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance
  Mock crypto =>
  Arbitrary (RewardProvenance crypto)
  where
  arbitrary =
    RewardProvenance
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance (Mock crypto) => Arbitrary (PulsingRewUpdate crypto) where
  arbitrary =
    oneof
      [ Complete <$> arbitrary,
        Pulsing <$> arbitrary <*> arbitrary
      ]

instance
  Mock crypto =>
  Arbitrary (RewardSnapShot crypto)
  where
  arbitrary =
    RewardSnapShot
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance
  Mock crypto =>
  Arbitrary (FreeVars crypto)
  where
  arbitrary =
    FreeVars
      <$> arbitrary {- b -}
      <*> arbitrary {- delegs -}
      <*> arbitrary {- stake -}
      <*> arbitrary {- addrsRew -}
      <*> arbitrary {- totalStake -}
      <*> arbitrary {- activeStake -}
      <*> arbitrary {- asc -}
      <*> arbitrary {- totalBlocks -}
      <*> arbitrary {- r -}
      <*> (EpochSize <$> arbitrary {- slotsPerEpoch -})
      <*> arbitrary {- pp_d -}
      <*> arbitrary {- pp_a0 -}
      <*> arbitrary {- pp_nOpt -}
      <*> arbitrary {- pp_mv -}

instance
  Mock crypto =>
  Arbitrary (Pulser crypto)
  where
  arbitrary = RSLP <$> arbitrary <*> arbitrary <*> arbitrary <*> (RewardAns <$> arbitrary <*> arbitrary)
