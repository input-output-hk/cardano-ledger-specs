{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Pretty where

import Cardano.Chain.Common
  ( AddrAttributes (..),
    Address (..),
    Attributes (..),
    HDAddressPayload (..),
    NetworkMagic (..),
    UnparsedFields (..),
  )
import qualified Cardano.Crypto.Hash as Hash
import Cardano.Ledger.Address
  ( Addr (..),
    BootstrapAddress (..),
    RewardAcnt (..),
  )
import Cardano.Ledger.AuxiliaryData (AuxiliaryDataHash (..))
import Cardano.Ledger.BaseTypes
  ( ActiveSlotCoeff,
    BoundedRational (..),
    DnsName,
    FixedPoint,
    Globals (..),
    Network (..),
    Nonce (..),
    Port (..),
    StrictMaybe (..),
    UnitInterval,
    Url (..),
    activeSlotLog,
    activeSlotVal,
    dnsToText,
  )
import Cardano.Ledger.Coin (Coin (..), DeltaCoin (..))
import Cardano.Ledger.Compactible (Compactible (..))
import Cardano.Ledger.Core (PParamsDelta)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential
  ( Credential (KeyHashObj, ScriptHashObj),
    GenesisCredential (..),
    Ptr (..),
    StakeReference (..),
  )
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Era (Era)
import qualified Cardano.Ledger.Era as Era (TxSeq)
import Cardano.Ledger.Keys
  ( GKeys (..),
    GenDelegPair (..),
    GenDelegs (..),
    KeyHash (..),
    KeyPair (..),
    KeyRole (Staking),
    VKey (..),
    VerKeyKES,
  )
import Cardano.Ledger.SafeHash (SafeHash, extractHash)
import Cardano.Ledger.Slot
  ( BlockNo (..),
    Duration (..),
    EpochNo (..),
    EpochSize (..),
    SlotNo (..),
  )
import Cardano.Slotting.Slot (WithOrigin (..))
import Cardano.Slotting.Time (SystemStart (SystemStart))
import Codec.Binary.Bech32
import Control.Monad.Identity (Identity)
import Control.SetAlgebra (forwards)
import Control.State.Transition (STS (State))
import qualified Data.ByteString as Long (ByteString)
import qualified Data.ByteString.Lazy as Lazy (ByteString, toStrict)
import Data.IP (IPv4, IPv6)
import qualified Data.Map.Strict as Map (Map, toList)
import Data.MemoBytes (MemoBytes (..))
import Data.Proxy (Proxy (..))
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set, toList)
import Data.Text (Text)
import Data.Typeable (Typeable)
import Data.Word (Word16, Word32, Word64, Word8)
import GHC.Natural (Natural)
import GHC.Records
import Prettyprinter
import Prettyprinter.Internal (Doc (Empty))
import Prettyprinter.Util (putDocW)
import Shelley.Spec.Ledger.Address.Bootstrap (BootstrapWitness (..), ChainCode (..))
import Shelley.Spec.Ledger.BlockChain
  ( BHBody (..),
    BHeader (..),
    Block (..),
    HashHeader (..),
    LastAppliedBlock (..),
    PrevHash (..),
  )
import Shelley.Spec.Ledger.CompactAddr (CompactAddr (..), decompactAddr)
import Shelley.Spec.Ledger.Delegation.Certificates (IndividualPoolStake (..), PoolDistr (..))
import Shelley.Spec.Ledger.EpochBoundary
  ( BlocksMade (..),
    PulsingStakeDistr (..),
    SnapShot (..),
    SnapShots (..),
    Stake (..),
  )
import Shelley.Spec.Ledger.LedgerState
  ( AccountState (..),
    DPState (..),
    DState (..),
    EpochState (..),
    FutureGenDeleg (..),
    InstantaneousRewards (..),
    Ix,
    LedgerState (..),
    NewEpochState (..),
    PPUPState (..),
    PState (..),
    UTxOState (..),
  )
import Shelley.Spec.Ledger.Metadata (Metadata (..), Metadatum (..))
import Shelley.Spec.Ledger.OCert
  ( KESPeriod (..),
    OCert (..),
    OCertEnv (..),
    OCertSignable (..),
  )
import Shelley.Spec.Ledger.PParams
  ( PPUpdateEnv (..),
    PParams' (..),
    ProposedPPUpdates (..),
    ProtVer (..),
    Update (..),
  )
import Shelley.Spec.Ledger.RewardUpdate
  ( FreeVars (..),
    Pulser,
    PulsingRewUpdate (..),
    RewardAns (..),
    RewardPulser (..),
    RewardSnapShot (..),
    RewardUpdate (..),
  )
import Shelley.Spec.Ledger.Rewards
  ( Histogram (..),
    Likelihood (..),
    LogWeight (..),
    NonMyopic (..),
    PerformanceEstimate (..),
    Reward (..),
    RewardType (..),
    StakeShare (..),
  )
import Shelley.Spec.Ledger.STS.Chain (ChainState (..))
import Shelley.Spec.Ledger.Scripts (MultiSig (..), ScriptHash (..))
import Shelley.Spec.Ledger.Tx
  ( Tx (..),
    WitnessSetHKD,
    prettyWitnessSetParts,
  )
import Shelley.Spec.Ledger.TxBody
  ( DCert (..),
    DelegCert (..),
    Delegation (..),
    GenesisDelegCert (..),
    MIRCert (..),
    MIRPot (..),
    MIRTarget (..),
    PoolCert (..),
    PoolMetadata (..),
    PoolParams (..),
    StakeCreds (..),
    StakePoolRelay (..),
    TxBody (..),
    TxBodyRaw (..),
    TxId (..),
    TxIn (..),
    TxOut (..),
    Wdrl (..),
    WitVKey (..),
  )
import Shelley.Spec.Ledger.UTxO (UTxO (..))

-- =====================================================================================================
-- HELPER FUNCTIONS
-- =====================================================================================================

-- ======================
-- Named pretty printers for some simpe types

ppString :: String -> Doc a
ppString x = pretty x

ppDouble :: Double -> Doc a
ppDouble x = viaShow x

ppInteger :: Integer -> Doc a
ppInteger x = viaShow x

ppRational :: Rational -> Doc a
ppRational x = viaShow x

ppFloat :: Float -> Doc a
ppFloat x = viaShow x

ppNatural :: Natural -> Doc a
ppNatural x = viaShow x

ppWord64 :: Word64 -> Doc a
ppWord64 x = viaShow x

ppWord32 :: Word32 -> Doc a
ppWord32 x = viaShow x

ppWord8 :: Word8 -> Doc a
ppWord8 x = viaShow x

ppWord16 :: Word16 -> Doc a
ppWord16 x = viaShow x

ppFixedPoint :: FixedPoint -> Doc a
ppFixedPoint x = viaShow x

ppPair :: (t1 -> PDoc) -> (t2 -> PDoc) -> (t1, t2) -> PDoc
ppPair pp1 pp2 (x, y) = ppSexp' mempty [pp1 x, pp2 y]

-- ppSignedDSIGN :: SignedDSIGN a b -> Doc ann
ppSignedDSIGN :: Show a => a -> PDoc
ppSignedDSIGN x = reAnnotate (Width 5 :) (viaShow x)

ppBool :: Bool -> Doc a
ppBool x = viaShow x

ppInt :: Int -> Doc a
ppInt x = viaShow x

-- =========================
-- operations for pretty printing

isEmpty :: Doc ann -> Bool
isEmpty Empty = True
isEmpty _ = False

putDoc :: Doc ann -> IO ()
putDoc = putDocW 80

data PrettyAnn = Width Int

type Ann = [PrettyAnn]

type PDoc = Doc Ann

text :: Text -> Doc ann
text x = pretty x

-- ======================
-- Byte Strings in Bech32 format

long_bech32 :: Long.ByteString -> Text
long_bech32 x =
  case humanReadablePartFromText "*" of
    Right human ->
      case encode human (dataPartFromBytes x) of
        Right ans -> ans
        Left _ -> "bech32Error"
    Left _ -> "bech32Error"

lazy_bech32 :: Lazy.ByteString -> Text
lazy_bech32 x =
  case humanReadablePartFromText "*" of
    Right human ->
      case encode human (dataPartFromBytes (Lazy.toStrict x)) of
        Right ans -> ans
        Left _ -> "bech32Error"
    Left _ -> "bech32Error"

ppLong :: Long.ByteString -> PDoc
ppLong x = text (long_bech32 x)

ppLazy :: Lazy.ByteString -> PDoc
ppLazy x = text (lazy_bech32 x)

instance PrettyA Long.ByteString where prettyA = ppLong

instance PrettyA Lazy.ByteString where prettyA = ppLazy

-- ================================
-- Combinators for common patterns of layout

-- | x == y
equate :: Doc a -> Doc a -> Doc a
equate x y = group (flatAlt (hang 2 (sep [x <+> text "=", y])) (hsep [x, text "=", y]))

-- | x -> y
arrow :: (Doc a, Doc a) -> Doc a
arrow (x, y) = group (flatAlt (hang 2 (sep [x <+> text "->", y])) (hsep [x, text "->", y]))

-- | ppSexp x [w,y,z] --> (x w y z)
ppSexp :: Text -> [PDoc] -> PDoc
ppSexp con fields = ppSexp' (text con) fields

ppSexp' :: PDoc -> [PDoc] -> PDoc
ppSexp' con fields =
  group $
    flatAlt
      (hang 2 (encloseSep lparen rparen space docs))
      (encloseSep lparen rparen space docs)
  where
    docs = if isEmpty con then fields else (con : fields)

-- | ppRecord name [("a",x),("b",y),("c",z)] --> name { a = x, b = y, c = z }
ppRecord :: Text -> [(Text, PDoc)] -> PDoc
ppRecord con fields = ppRecord' (text con) fields

ppRecord' :: PDoc -> [(Text, PDoc)] -> PDoc
ppRecord' con fields =
  group $
    flatAlt
      (hang 1 (vcat [con, puncLeft lbrace (map (\(x, y) -> equate (text x) y) fields) comma rbrace]))
      (con <> (encloseSep (lbrace <> space) (space <> rbrace) (comma <> space) (map (\(x, y) -> equate (text x) y) fields)))

-- | Vertical layout with commas aligned on the left hand side
puncLeft :: Doc ann -> [Doc ann] -> Doc ann -> Doc ann -> Doc ann
puncLeft open [] _ close = hsep [open, close]
puncLeft open [x] _ close = hsep [open, x, close]
puncLeft open (x : xs) coma close = align (sep ((open <+> x) : help xs))
  where
    help [] = mempty
    help [y] = [hsep [coma, y, close]]
    help (y : ys) = ((coma <+> y) : help ys)

ppSet :: (x -> Doc ann) -> Set x -> Doc ann
ppSet p xs = encloseSep lbrace rbrace comma (map p (toList xs))

ppList :: (x -> Doc ann) -> [x] -> Doc ann
ppList p xs =
  group $
    flatAlt
      (puncLeft lbracket (map p xs) comma rbracket)
      (encloseSep (lbracket <> space) (space <> rbracket) (comma <> space) (map p xs))

ppStrictSeq :: (a -> Doc ann) -> StrictSeq a -> Doc ann
ppStrictSeq p xs = ppList p (foldr (:) [] xs)

ppStrictMaybe :: (x -> Doc ann) -> StrictMaybe x -> Doc ann
ppStrictMaybe _ SNothing = text "?-"
ppStrictMaybe p (SJust x) = text "?" <> p x

ppMaybe :: (x -> Doc ann) -> Maybe x -> Doc ann
ppMaybe _ Nothing = text "?-"
ppMaybe p (Just x) = text "?" <> p x

ppMap' :: PDoc -> (k -> PDoc) -> (v -> PDoc) -> Map.Map k v -> PDoc
ppMap' name kf vf m =
  let docs = fmap (\(k, v) -> arrow (kf k, vf v)) (Map.toList m)
      vertical =
        if isEmpty name
          then (hang 1 (puncLeft lbrace docs comma rbrace))
          else (hang 1 (vcat [name, puncLeft lbrace docs comma rbrace]))
   in group $
        flatAlt
          vertical
          (name <> (encloseSep (lbrace <> space) (space <> rbrace) (comma <> space) docs))

ppMap :: (k -> PDoc) -> (v -> PDoc) -> Map.Map k v -> PDoc
ppMap kf vf m = ppMap' (text "Map") kf vf m

class PrettyA t where
  prettyA :: t -> PDoc

-- =====================================================================================================
-- END HELPER FUNCTIONS
-- ================================= ====================================================================

-- ================================
-- Shelley.Spec.Ledger.STS.Chain(ChainState(..))
-- import Shelley.Spec.Ledger.BlockChain(LastAppliedBlock(..),HashHeader(..))

ppChainState :: CanPrettyPrintLedgerState era => ChainState era -> PDoc
ppChainState (ChainState nes ocert epochnonce evolvenonce prevnonce candnonce lastab) =
  ppRecord
    "ChainState"
    [ ("newepoch", ppNewEpochState nes),
      ("ocerts", ppMap ppKeyHash ppWord64 ocert),
      ("epochNonce", ppNonce epochnonce),
      ("evolvingNonce", ppNonce evolvenonce),
      ("candidateNonce", ppNonce prevnonce),
      ("prevepochNonce", ppNonce candnonce),
      ("lastApplidBlock", ppWithOrigin ppLastAppliedBlock lastab)
    ]

ppLastAppliedBlock :: LastAppliedBlock c -> PDoc
ppLastAppliedBlock (LastAppliedBlock blkNo slotNo hh) =
  ppRecord
    "LastAppliedBlock"
    [ ("blockNo", ppBlockNo blkNo),
      ("slotNo", ppSlotNo slotNo),
      ("hash", ppHashHeader hh)
    ]

ppHashHeader :: HashHeader c -> PDoc
ppHashHeader (HashHeader x) = ppHash x

ppWithOrigin :: (t -> PDoc) -> (WithOrigin t) -> PDoc
ppWithOrigin _ Origin = ppString "Origin"
ppWithOrigin pp (At t) = ppSexp "At" [pp t]

instance CanPrettyPrintLedgerState era => PrettyA (ChainState era) where prettyA = ppChainState

instance PrettyA (LastAppliedBlock c) where prettyA = ppLastAppliedBlock

instance PrettyA (HashHeader c) where prettyA = ppHashHeader

instance PrettyA t => PrettyA (WithOrigin t) where prettyA = ppWithOrigin prettyA

ppBHBody :: Crypto c => BHBody c -> PDoc
ppBHBody (BHBody bn sn prev vk vrfvk eta l size hash ocert protver) =
  ppRecord
    "BHBody"
    [ ("BlockNo", ppBlockNo bn),
      ("SlotNo", ppSlotNo sn),
      ("Prev", ppPrevHash prev),
      ("VKey", ppVKey vk),
      ("VerKeyVRF", viaShow vrfvk), -- The next 3 are type families
      ("Eta", viaShow eta),
      ("L", viaShow l),
      ("size", ppNatural size),
      ("Hash", ppHash hash),
      ("OCert", ppOCert ocert),
      ("ProtVersion", ppProtVer protver)
    ]

ppPrevHash :: PrevHash c -> PDoc
ppPrevHash GenesisHash = ppString "GenesisHash"
ppPrevHash (BlockHash x) = ppSexp "BlockHashppHashHeader" [ppHashHeader x]

ppBHeader :: Crypto c => BHeader c -> PDoc
ppBHeader (BHeader bh sig) =
  ppRecord
    "BHeader"
    [ ("Body", ppBHBody bh),
      ("Sig", viaShow sig)
    ]

ppBlock :: (Era era, PrettyA (Era.TxSeq era)) => Block era -> PDoc
ppBlock (Block' bh seqx _) =
  ppRecord
    "Block"
    [ ("Header", ppBHeader bh),
      ("TxSeq", prettyA seqx)
    ]

instance Crypto c => PrettyA (BHBody c) where prettyA = ppBHBody

instance Crypto c => PrettyA (BHeader c) where prettyA = ppBHeader

instance PrettyA (PrevHash c) where prettyA = ppPrevHash

instance (Era era, PrettyA (Era.TxSeq era)) => PrettyA (Block era) where prettyA = ppBlock

-- =================================
-- Shelley.Spec.Ledger.LedgerState.Delegation.Certificates

ppPoolDistr :: PoolDistr c -> PDoc
ppPoolDistr (PoolDistr mp) = ppSexp "PoolDistr" [ppMap ppKeyHash ppIndividualPoolStake mp]

ppIndividualPoolStake :: IndividualPoolStake c -> PDoc
ppIndividualPoolStake (IndividualPoolStake r1 h) =
  ppRecord
    "IndividualPoolStake"
    [ ("stake", ppRational r1),
      ("stakeVrf", ppHash h)
    ]

instance PrettyA (PoolDistr c) where prettyA = ppPoolDistr

instance PrettyA (IndividualPoolStake c) where prettyA = ppIndividualPoolStake

-- ================================
-- Shelley.Spec.Ledger.RewardUpdate

ppRewardUpdate :: RewardUpdate crypto -> PDoc
ppRewardUpdate (RewardUpdate dt dr rss df nonmyop) =
  ppRecord
    "RewardUpdate"
    [ ("deltaT", ppDeltaCoin dt),
      ("deltaR", ppDeltaCoin dr),
      ("rs", ppMap' mempty ppCredential (ppSet ppReward) rss),
      ("deltaF", ppDeltaCoin df),
      ("nonMyopic", ppNonMyopic nonmyop)
    ]

ppRewardSnapShot :: RewardSnapShot crypto -> PDoc
ppRewardSnapShot (RewardSnapShot go fee a0 nopt ver non deltaR1 rR deltaT1 total pot) =
  ppRecord
    "RewardSnapShot"
    [ ("GoSnapShot", ppSnapShot go),
      ("feeSnapShot", ppCoin fee),
      ("a0", ppRational $ unboundRational a0),
      ("nOpt", ppNatural nopt),
      ("version", ppProtVer ver),
      ("nonmyopic", ppNonMyopic non),
      ("deltaR1", ppCoin deltaR1),
      ("R", ppCoin rR),
      ("deltaT1", ppCoin deltaT1),
      ("totalStake", ppCoin total),
      ("rewardPot", ppCoin pot)
    ]

ppFreeVars :: FreeVars crypto -> PDoc
ppFreeVars (FreeVars b1 del stake1 addrs total active asc1 blocks r1 slots d a0 nOpt) =
  ppRecord
    "FreeVars"
    [ ("b", ppMap ppKeyHash ppNatural b1),
      ("delegs", ppMap ppCredential ppKeyHash del),
      ("stake", ppStake stake1),
      ("addrsRew", ppSet ppCredential addrs),
      ("totalStake", ppInteger total),
      ("activeStake", ppInteger active),
      ("asc", ppActiveSlotCoeff asc1),
      ("totalBlocks", ppNatural blocks),
      ("r", ppCoin r1),
      ("slotserEpoch", ppEpochSize slots),
      ("d", ppUnitInterval d),
      ("a0", ppRational $ unboundRational a0),
      ("nOpt", ppNatural nOpt)
    ]

ppAns :: RewardAns crypto -> PDoc
ppAns (RewardAns x y) =
  ppSexp'
    mempty
    [ (ppMap ppCredential (ppSet ppReward)) x,
      (ppMap ppKeyHash ppLikelihood) y
    ]

ppRewardPulser :: Pulser crypto -> PDoc
ppRewardPulser (RSLP n free items ans) =
  ppSexp
    "RewardPulser"
    [ ppInt n,
      ppFreeVars free,
      ppStrictSeq ppPoolParams items,
      ppAns ans
    ]

ppPulsingRewUpdate :: PulsingRewUpdate crypto -> PDoc
ppPulsingRewUpdate (Pulsing snap pulser) =
  ppSexp "Pulsing" [ppRewardSnapShot snap, ppRewardPulser pulser]
ppPulsingRewUpdate (Complete rewup) =
  ppSexp "Complete" [ppRewardUpdate rewup]

instance PrettyA (RewardSnapShot crypto) where prettyA = ppRewardSnapShot

instance PrettyA (FreeVars crypto) where prettyA = ppFreeVars

instance PrettyA (Pulser crypto) where prettyA = ppRewardPulser

instance PrettyA (PulsingRewUpdate crypto) where prettyA = ppPulsingRewUpdate

instance PrettyA (RewardUpdate crypto) where prettyA = ppRewardUpdate

-- =================================
-- Shelley.Spec.Ledger.LedgerState

-- | Constraints needed to ensure that the ledger state can be pretty printed.
type CanPrettyPrintLedgerState era =
  ( PrettyA (Core.TxOut era),
    PrettyA (Core.PParams era),
    PrettyA (State (Core.EraRule "PPUP" era))
  )

ppAccountState :: AccountState -> PDoc
ppAccountState (AccountState tr re) =
  ppRecord
    "AccountState"
    [ ("treasury", ppCoin tr),
      ("reserves", ppCoin re)
    ]

ppDPState :: DPState crypto -> PDoc
ppDPState (DPState d p) = ppRecord "DPState" [("dstate", ppDState d), ("pstate", ppPState p)]

ppDState :: DState crypto -> PDoc
ppDState (DState r1 ds ptrs future gen irwd) =
  ppRecord
    "DState"
    [ ("rewards", ppRewardAccounts r1),
      ("delegations", ppMap' mempty ppCredential ppKeyHash ds),
      ("ptrs", ppMap ppPtr ppCredential (forwards ptrs)),
      ("futuregendelegs", ppMap ppFutureGenDeleg ppGenDelegPair future),
      ("gendelegs", ppGenDelegs gen),
      ("instantaeousrewards", ppInstantaneousRewards irwd)
    ]

ppFutureGenDeleg :: FutureGenDeleg crypto -> PDoc
ppFutureGenDeleg (FutureGenDeleg sl kh) =
  ppRecord
    "FutureGenDeleg"
    [ ("delegSlot", ppSlotNo sl),
      ("keyhash", ppKeyHash kh)
    ]

ppInstantaneousRewards :: InstantaneousRewards crypto -> PDoc
ppInstantaneousRewards (InstantaneousRewards res treas dR dT) =
  ppRecord
    "InstantaneousRewards"
    [ ("reserves", ppMap' mempty ppCredential ppCoin res),
      ("treasury", ppMap' mempty ppCredential ppCoin treas),
      ("deltaReserves", ppDeltaCoin dR),
      ("deltaTreasury", ppDeltaCoin dT)
    ]

ppIx :: Ix -> PDoc
ppIx x = viaShow x

ppPPUPState :: PrettyA (PParamsDelta era) => PPUPState era -> PDoc
ppPPUPState (PPUPState p fp) =
  ppRecord
    "Proposed PPUPState"
    [ ("proposals", ppProposedPPUpdates p),
      ("futureProposals", ppProposedPPUpdates fp)
    ]

ppPState :: PState crypto -> PDoc
ppPState (PState par fpar ret) =
  ppRecord
    "PState"
    [ ("poolparams", ppMap' mempty ppKeyHash ppPoolParams par),
      ("futurepoolparams", ppMap' mempty ppKeyHash ppPoolParams fpar),
      ("retiring", ppMap' mempty ppKeyHash ppEpochNo ret)
    ]

ppRewardAccounts :: Map.Map (Credential 'Staking crypto) Coin -> PDoc
ppRewardAccounts m = ppMap' (text "RewardAccounts") ppCredential ppCoin m

ppRewardType :: RewardType -> PDoc
ppRewardType MemberReward = text "MemberReward"
ppRewardType LeaderReward = text "LeaderReward"

ppReward :: Reward crypto -> PDoc
ppReward (Reward rt pool amt) =
  ppRecord
    "Reward"
    [ ("rewardType", ppRewardType rt),
      ("poolId", ppKeyHash pool),
      ("rewardAmount", ppCoin amt)
    ]

ppUTxOState ::
  CanPrettyPrintLedgerState era =>
  UTxOState era ->
  PDoc
ppUTxOState (UTxOState u dep fee ppup) =
  ppRecord
    "UTxOState"
    [ ("utxo", ppUTxO u),
      ("deposited", ppCoin dep),
      ("fees", ppCoin fee),
      ("ppups", prettyA ppup)
    ]

ppEpochState :: CanPrettyPrintLedgerState era => EpochState era -> PDoc
ppEpochState (EpochState acnt snap ls prev pp non) =
  ppRecord
    "EpochState"
    [ ("accountState", ppAccountState acnt),
      ("snapShots", ppSnapShots snap),
      ("ledgerState", ppLedgerState ls),
      ("prevPParams", prettyA prev),
      ("currentPParams", prettyA pp),
      ("nonMyopic", ppNonMyopic non)
    ]

ppNewEpochState :: CanPrettyPrintLedgerState era => NewEpochState era -> PDoc
ppNewEpochState (NewEpochState enum prevB curB es rewup pool) =
  ppRecord
    "NewEpochState"
    [ ("epochnum", ppEpochNo enum),
      ("prevBlock", ppBlocksMade prevB),
      ("currBlock", ppBlocksMade curB),
      ("epochState", ppEpochState es),
      ("rewUpdate", ppStrictMaybe ppPulsingRewUpdate rewup),
      ("poolDist", ppPoolDistr pool)
    ]

ppLedgerState ::
  CanPrettyPrintLedgerState era =>
  LedgerState era ->
  PDoc
ppLedgerState (LedgerState u d) =
  ppRecord
    "LedgerState"
    [ ("utxoState", ppUTxOState u),
      ("delegationState", ppDPState d)
    ]

instance PrettyA (AccountState) where prettyA = ppAccountState

instance PrettyA (DPState crypto) where prettyA = ppDPState

instance PrettyA (DState crypto) where prettyA = ppDState

instance
  ( Era era,
    CanPrettyPrintLedgerState era
  ) =>
  PrettyA (EpochState era)
  where
  prettyA = ppEpochState

instance
  ( Era era,
    CanPrettyPrintLedgerState era
  ) =>
  PrettyA (NewEpochState era)
  where
  prettyA x = ppNewEpochState x

instance PrettyA (FutureGenDeleg crypto) where prettyA = ppFutureGenDeleg

instance PrettyA (InstantaneousRewards crypto) where prettyA = ppInstantaneousRewards

instance
  ( Era era,
    CanPrettyPrintLedgerState era
  ) =>
  PrettyA (LedgerState era)
  where
  prettyA = ppLedgerState

instance
  PrettyA (PParamsDelta era) =>
  PrettyA (PPUPState era)
  where
  prettyA = ppPPUPState

instance PrettyA (PState crypto) where prettyA = ppPState

instance
  ( Era era,
    CanPrettyPrintLedgerState era
  ) =>
  PrettyA (UTxOState era)
  where
  prettyA = ppUTxOState

-- =================================
-- Shelley.Spec.Ledger.Rewards

ppPerformanceEstimate :: PerformanceEstimate -> PDoc
ppPerformanceEstimate (PerformanceEstimate n) = ppSexp "PerformanceEstimate" [ppDouble n]

ppNonMyopic :: NonMyopic crypto -> PDoc
ppNonMyopic (NonMyopic m c) =
  ppRecord
    "NonMyopic"
    [ ("likelihood", ppMap' "" ppKeyHash ppLikelihood m),
      ("rewardPot", ppCoin c)
    ]

ppStakeShare :: StakeShare -> PDoc
ppStakeShare (StakeShare n) = ppSexp "StakeShare" [ppRational n]

ppHistogram :: Histogram -> PDoc
ppHistogram (Histogram ss) = ppSexp "Histogram" [ppStrictSeq ppLogWeight ss]

ppLogWeight :: LogWeight -> PDoc
ppLogWeight (LogWeight n) = ppSexp "LogWeight" [ppFloat n]

ppLikelihood :: Likelihood -> PDoc
ppLikelihood (Likelihood ns) = ppSexp "Likelihood" [ppStrictSeq ppLogWeight ns]

instance PrettyA PerformanceEstimate where prettyA = ppPerformanceEstimate

instance PrettyA StakeShare where prettyA = ppStakeShare

instance PrettyA Histogram where prettyA = ppHistogram

instance PrettyA LogWeight where prettyA = ppLogWeight

instance PrettyA Likelihood where prettyA = ppLikelihood

-- =================================
-- Shelley.Spec.Ledger.EpochBoundary

ppStake :: Stake crypto -> PDoc
ppStake (Stake m) = ppMap' (text "Stake") ppCredential ppCoin m

ppBlocksMade :: BlocksMade crypto -> PDoc
ppBlocksMade (BlocksMade m) = ppMap' (text "BlocksMade") ppKeyHash ppNatural m

ppSnapShot :: SnapShot crypto -> PDoc
ppSnapShot (SnapShot st deleg params) =
  ppRecord
    "SnapShot"
    [ ("stake", ppStake st),
      ("delegations", ppMap ppCredential ppKeyHash deleg),
      ("poolParams", ppMap ppKeyHash ppPoolParams params)
    ]

ppSnapShots :: SnapShots crypto -> PDoc
ppSnapShots (SnapShots mark set go fees) =
  ppRecord
    "SnapShots"
    [ ("pstakeMark", ppPulsingStakeDistr mark),
      ("pstakeSet", ppSnapShot set),
      ("pstakeGo", ppSnapShot go),
      ("fee", ppCoin fees)
    ]

ppPulsingStakeDistr :: PulsingStakeDistr era m -> PDoc
ppPulsingStakeDistr (Completed ss) = ppSnapShot ss
ppPulsingStakeDistr (StillPulsing _) = ppString "StillPulsing"

instance PrettyA (Stake crypto) where prettyA = ppStake

instance PrettyA (BlocksMade crypto) where prettyA = ppBlocksMade

instance PrettyA (SnapShot crypto) where prettyA = ppSnapShot

instance PrettyA (SnapShots crypto) where prettyA = ppSnapShots

-- ============================
-- Shelley.Spec.Ledger.UTxO

ppUTxO ::
  PrettyA (Core.TxOut era) =>
  UTxO era ->
  PDoc
ppUTxO (UTxO m) = ppMap' (text "UTxO") ppTxIn prettyA m

instance
  PrettyA (Core.TxOut era) =>
  PrettyA (UTxO era)
  where
  prettyA = ppUTxO

-- ============================
-- Sheley.Spec.Ledger.Metadata

ppMetadatum :: Metadatum -> PDoc
ppMetadatum (Map m) =
  let pairs = fmap (\(k, v) -> arrow (ppMetadatum k, ppMetadatum v)) m
   in ppSexp
        "Map"
        [ group $
            flatAlt
              (hang 1 (puncLeft lbrace pairs comma rbrace))
              (encloseSep (lbrace <> space) (space <> rbrace) (comma <> space) pairs)
        ]
ppMetadatum (List ds) = ppSexp "List" [ppList ppMetadatum ds]
ppMetadatum (I n) = ppSexp "I" [ppInteger n]
ppMetadatum (B bs) = ppSexp "B" [ppLong bs]
ppMetadatum (S txt) = ppSexp "S" [text txt]

ppMetadata :: Metadata era -> PDoc
ppMetadata (Metadata m) = ppMap' (text "Metadata") ppWord64 ppMetadatum m

instance PrettyA Metadatum where prettyA = ppMetadatum

instance PrettyA (Metadata era) where prettyA = ppMetadata

-- ============================
-- Shelley.Spec.Ledger.Tx

ppTx ::
  ( PrettyA (Core.TxBody era),
    PrettyA (Core.AuxiliaryData era),
    PrettyA (Core.Witnesses era)
  ) =>
  Tx era ->
  PDoc
ppTx tx =
  ppRecord
    "Tx"
    [ ("body", prettyA $ getField @"body" tx),
      ("witnessSet", prettyA $ getField @"wits" tx),
      ("metadata", ppStrictMaybe prettyA $ getField @"auxiliaryData" tx)
    ]

ppBootstrapWitness :: Crypto crypto => BootstrapWitness crypto -> PDoc
ppBootstrapWitness (BootstrapWitness key sig (ChainCode code) attr) =
  ppRecord
    "BootstrapWitness"
    [ ("key", ppVKey key),
      ("signature", ppSignedDSIGN sig),
      ("chaincode", ppLong code),
      ("attributes", ppLong attr)
    ]

ppWitnessSetHKD :: (Era era, PrettyA (Core.Script era)) => WitnessSetHKD Identity era -> PDoc
ppWitnessSetHKD x =
  let (addr, scr, boot) = prettyWitnessSetParts x
   in ppRecord
        "WitnessSet"
        [ ("addrWits", ppSet ppWitVKey addr),
          ("scriptWits", ppMap ppScriptHash prettyA scr),
          ("bootWits", ppSet ppBootstrapWitness boot)
        ]

instance
  ( PrettyA (Core.TxBody era),
    PrettyA (Core.AuxiliaryData era),
    PrettyA (Core.Witnesses era),
    Era era
  ) =>
  PrettyA (Tx era)
  where
  prettyA = ppTx

instance Crypto crypto => PrettyA (BootstrapWitness crypto) where prettyA = ppBootstrapWitness

instance (Era era, PrettyA (Core.Script era)) => PrettyA (WitnessSetHKD Identity era) where prettyA = ppWitnessSetHKD

-- ============================
--  Cardano.Ledger.AuxiliaryData

ppSafeHash :: SafeHash crypto index -> PDoc
ppSafeHash x = ppHash (extractHash x)

ppAuxiliaryDataHash :: AuxiliaryDataHash c -> PDoc
ppAuxiliaryDataHash (AuxiliaryDataHash h) = ppSexp "AuxiliaryDataHash" [ppSafeHash h]

instance PrettyA (AuxiliaryDataHash c) where prettyA = ppAuxiliaryDataHash

instance PrettyA (SafeHash c i) where prettyA = ppSafeHash

-- ============================
--  Cardano.Ledger.Compactible

ppCompactForm :: (Compactible a) => (a -> PDoc) -> CompactForm a -> PDoc
ppCompactForm cf x = cf (fromCompact x)

instance (Compactible a, PrettyA a) => PrettyA (CompactForm a) where prettyA = ppCompactForm prettyA

-- ============================
-- Shelley.Spec.Ledger.TxBody

ppDelegation :: Delegation c -> PDoc
ppDelegation (Delegation orx ee) = ppRecord "Delegation" [("delegator", ppCredential orx), ("delegatee", ppKeyHash ee)]

ppPoolMetadata :: PoolMetadata -> PDoc
ppPoolMetadata (PoolMetadata url hsh) =
  ppRecord
    "PoolMetadata"
    [ ("url", ppUrl url),
      ("hash", (text "#" <> reAnnotate (Width 5 :) (ppLong hsh)))
    ]

ppStakePoolRelay :: StakePoolRelay -> PDoc
ppStakePoolRelay (SingleHostAddr port ip4 ip6) = ppSexp "SingleHostAddr" [ppStrictMaybe ppPort port, ppStrictMaybe ppIPv4 ip4, ppStrictMaybe ppIPv6 ip6]
ppStakePoolRelay (SingleHostName port dns) = ppSexp "SingleHostName" [ppStrictMaybe ppPort port, ppDnsName dns]
ppStakePoolRelay (MultiHostName dns) = ppSexp "MultiHostName" [ppDnsName dns]

ppPoolParams :: PoolParams c -> PDoc
ppPoolParams (PoolParams idx vrf pledge cost margin acnt owners relays md) =
  ppRecord
    "PoolParams"
    [ ("Id", ppKeyHash idx),
      ("Vrf", ppHash vrf),
      ("Pledge", ppCoin pledge),
      ("Cost", ppCoin cost),
      ("Margin", ppUnitInterval margin),
      ("RAcnt", ppRewardAcnt acnt),
      ("Owners", ppSet ppKeyHash owners),
      ("Relays", ppStrictSeq ppStakePoolRelay relays),
      ("Metadata", ppStrictMaybe ppPoolMetadata md)
    ]

ppWdrl :: Wdrl c -> PDoc
ppWdrl (Wdrl m) = ppSexp "" [ppMap' (text "Wdr") ppRewardAcnt ppCoin m]

ppTxId :: TxId c -> PDoc
ppTxId (TxId x) = ppSexp "TxId" [ppSafeHash x]

ppTxIn :: TxIn c -> PDoc
ppTxIn (TxInCompact txid word) = ppSexp "TxIn" [ppTxId txid, ppWord64 word]

ppTxOut :: (Era era, PrettyA (Core.Value era)) => TxOut era -> PDoc
ppTxOut (TxOutCompact caddr cval) = ppSexp "TxOut" [ppCompactAddr caddr, ppCompactForm prettyA cval]

ppDelegCert :: DelegCert c -> PDoc
ppDelegCert (RegKey x) = ppSexp "RegKey" [ppCredential x]
ppDelegCert (DeRegKey x) = ppSexp "DeRegKey" [ppCredential x]
ppDelegCert (Delegate x) = ppSexp "Delegate" [ppDelegation x]

ppPoolCert :: PoolCert c -> PDoc
ppPoolCert (RegPool x) = ppSexp "RegPool" [ppPoolParams x]
ppPoolCert (RetirePool x y) = ppSexp "RetirePool" [ppKeyHash x, ppEpochNo y]

ppGenesisDelegCert :: GenesisDelegCert c -> PDoc
ppGenesisDelegCert (GenesisDelegCert a b1 c) = ppSexp "GenesisDelgCert" [ppKeyHash a, ppKeyHash b1, ppHash c]

ppMIRPot :: MIRPot -> PDoc
ppMIRPot ReservesMIR = text "Reserves"
ppMIRPot TreasuryMIR = text "Treasury"

ppMIRTarget :: MIRTarget c -> PDoc
ppMIRTarget (StakeAddressesMIR rews) = ppMap ppCredential ppDeltaCoin rews
ppMIRTarget (SendToOppositePotMIR c) = ppCoin c

ppMIRCert :: MIRCert c -> PDoc
ppMIRCert (MIRCert pot vs) = ppSexp "MirCert" [ppMIRPot pot, ppMIRTarget vs]

ppDCert :: DCert c -> PDoc
ppDCert (DCertDeleg x) = ppSexp "DCertDeleg" [ppDelegCert x]
ppDCert (DCertPool x) = ppSexp "DCertPool" [ppPoolCert x]
ppDCert (DCertGenesis x) = ppSexp "DCertGenesis" [ppGenesisDelegCert x]
ppDCert (DCertMir x) = ppSexp "DCertMir" [ppMIRCert x]

ppTxBody ::
  PrettyA (Core.TxOut era) =>
  PrettyA (PParamsDelta era) =>
  TxBody era ->
  PDoc
ppTxBody (TxBodyConstr (Memo (TxBodyRaw ins outs cs wdrls fee ttl upd mdh) _)) =
  ppRecord
    "TxBody"
    [ ("inputs", ppSet ppTxIn ins),
      ("outputs", ppStrictSeq prettyA outs),
      ("cert", ppStrictSeq ppDCert cs),
      ("wdrls", ppWdrl wdrls),
      ("fee", ppCoin fee),
      ("timetolive", ppSlotNo ttl),
      ("update", ppStrictMaybe ppUpdate upd),
      ("metadatahash", ppStrictMaybe ppAuxiliaryDataHash mdh)
    ]

ppWitVKey :: (Typeable kr, Crypto c) => WitVKey kr c -> PDoc
ppWitVKey (WitVKey key sig) = ppRecord "WitVKey" [("key", ppVKey key), ("signature", ppSignedDSIGN sig)]

ppStakeCreds :: StakeCreds c -> PDoc
ppStakeCreds (StakeCreds m) = ppSexp "" [ppMap' (text "StakeCreds") ppCredential ppSlotNo m]

instance PrettyA (Delegation c) where prettyA = ppDelegation

instance PrettyA PoolMetadata where prettyA = ppPoolMetadata

instance PrettyA StakePoolRelay where prettyA = ppStakePoolRelay

instance PrettyA (PoolParams c) where prettyA = ppPoolParams

instance PrettyA (Wdrl c) where prettyA = ppWdrl

instance PrettyA (TxId c) where prettyA = ppTxId

instance PrettyA (TxIn c) where prettyA = ppTxIn

instance (Era era, PrettyA (Core.Value era)) => PrettyA (TxOut era) where prettyA = ppTxOut

instance PrettyA (DelegCert c) where prettyA = ppDelegCert

instance PrettyA (PoolCert c) where prettyA = ppPoolCert

instance PrettyA (GenesisDelegCert c) where prettyA = ppGenesisDelegCert

instance PrettyA MIRPot where prettyA = ppMIRPot

instance PrettyA (MIRCert c) where prettyA = ppMIRCert

instance PrettyA (DCert c) where prettyA = ppDCert

instance
  (PrettyA (Core.TxOut era), PrettyA (PParamsDelta era)) =>
  PrettyA (TxBody era)
  where
  prettyA = ppTxBody

instance (Typeable kr, Crypto c) => PrettyA (WitVKey kr c) where prettyA = ppWitVKey

instance Crypto c => PrettyA (StakeCreds c) where prettyA = ppStakeCreds

-- ===========================================
-- Data.IP
ppIPv4 :: IPv4 -> PDoc
ppIPv4 x = viaShow x

ppIPv6 :: IPv6 -> PDoc
ppIPv6 x = viaShow x

instance PrettyA IPv4 where prettyA = ppIPv4

instance PrettyA IPv6 where prettyA = ppIPv6

-- ====================================================
-- Shelley.Spec.Ledger.CompactAddr

ppCompactAddr :: Crypto c => CompactAddr c -> PDoc
ppCompactAddr x = ppAddr (decompactAddr x)

instance Crypto c => PrettyA (CompactAddr c) where prettyA = ppCompactAddr

-- ================================================
-- Shelley.Spec.Ledger.PParams

ppProtVer :: ProtVer -> PDoc
ppProtVer (ProtVer maj mi) = ppRecord "Version" [("major", ppNatural maj), ("minor", ppNatural mi)]

ppPParams :: PParams' Identity era -> PDoc
ppPParams (PParams feeA feeB mbb mtx mbh kd pd em no a0 rho tau d ex pv mutxo mpool) =
  ppRecord
    "PParams"
    [ ("minfeeA", ppNatural feeA),
      ("minfeeB", ppNatural feeB),
      ("maxBBSize", ppNatural mbb),
      ("maxTxSize", ppNatural mtx),
      ("maxBHSize", ppNatural mbh),
      ("keyDeposit", ppCoin kd),
      ("poolDeposit", ppCoin pd),
      ("eMax", ppEpochNo em),
      ("nOpt", ppNatural no),
      ("a0", ppRational $ unboundRational a0),
      ("rho", ppUnitInterval rho),
      ("tau", ppUnitInterval tau),
      ("d", ppUnitInterval d),
      ("extraEntropy", ppNonce ex),
      ("protocolVersion", ppProtVer pv),
      ("minUTxOValue", ppCoin mutxo),
      ("minPoolCost", ppCoin mpool)
    ]

ppPParamsUpdate :: PParams' StrictMaybe era -> PDoc
ppPParamsUpdate (PParams feeA feeB mbb mtx mbh kd pd em no a0 rho tau d ex pv mutxo mpool) =
  ppRecord
    "PParams"
    [ ("minfeeA", lift ppNatural feeA),
      ("minfeeB", lift ppNatural feeB),
      ("maxBBSize", lift ppNatural mbb),
      ("maxTxSize", lift ppNatural mtx),
      ("maxBHSize", lift ppNatural mbh),
      ("keyDeposit", lift ppCoin kd),
      ("poolDeposit", lift ppCoin pd),
      ("eMax", lift ppEpochNo em),
      ("nOpt", lift ppNatural no),
      ("a0", lift (ppRational . unboundRational) a0),
      ("rho", lift ppUnitInterval rho),
      ("tau", lift ppUnitInterval tau),
      ("d", lift ppUnitInterval d),
      ("extraEntropy", lift ppNonce ex),
      ("protocolVersion", lift ppProtVer pv),
      ("minUTxOValue", lift ppCoin mutxo),
      ("minPoolCost", lift ppCoin mpool)
    ]
  where
    lift pp x = ppStrictMaybe pp x

ppUpdate :: PrettyA (PParamsDelta era) => Update era -> PDoc
ppUpdate (Update prop epn) = ppSexp "Update" [ppProposedPPUpdates prop, ppEpochNo epn]

ppProposedPPUpdates :: PrettyA (PParamsDelta era) => ProposedPPUpdates era -> PDoc
ppProposedPPUpdates (ProposedPPUpdates m) = ppMap ppKeyHash prettyA m

ppPPUpdateEnv :: PPUpdateEnv c -> PDoc
ppPPUpdateEnv (PPUpdateEnv slot gd) =
  ppSexp
    "PPUpdateEnv"
    [ppSlotNo slot, ppGenDelegs gd]

instance PrettyA (PPUpdateEnv c) where prettyA = ppPPUpdateEnv

instance
  PrettyA (PParamsDelta e) =>
  PrettyA (ProposedPPUpdates e)
  where
  prettyA = ppProposedPPUpdates

instance PrettyA (PParamsDelta e) => PrettyA (Update e) where prettyA = ppUpdate

instance PrettyA (PParams' StrictMaybe e) where prettyA = ppPParamsUpdate

instance PrettyA (PParams' Identity e) where prettyA = ppPParams

instance PrettyA ProtVer where prettyA = ppProtVer

-- ============================================
-- Cardano.Ledger.Coin
ppCoin :: Coin -> PDoc
ppCoin (Coin n) = ppSexp "Coin" [pretty n]

ppDeltaCoin :: DeltaCoin -> PDoc
ppDeltaCoin (DeltaCoin n) = ppSexp "DeltaCoin" [pretty n]

instance PrettyA Coin where prettyA = ppCoin

-- ===========================================
-- Cardano.Chain.Common

ppBootstrapAddress :: BootstrapAddress c -> PDoc
ppBootstrapAddress (BootstrapAddress (Address root (Attributes (AddrAttributes path magic) y) typ)) =
  ppRecord
    "BootstrapAddress"
    [ ("root", viaShow root), -- Cardano.Crypto.Hashing.AbstractHash
      ("derivationpath", ppMaybe ppHDAddressPayload path),
      ("networkmagic", ppNetworkMagic magic),
      ("remain", ppUnparsedFields y),
      ("type", viaShow typ) -- Cardano.Chain.Common.AddrSpendingData.AddrType
    ]

ppNetworkMagic :: NetworkMagic -> PDoc
ppNetworkMagic NetworkMainOrStage = text "MainOrStage"
ppNetworkMagic (NetworkTestnet n) = text "Testnet" <+> ppWord32 n

ppUnparsedFields :: UnparsedFields -> PDoc
ppUnparsedFields (UnparsedFields m) = ppMap' mempty ppWord8 ppLazy m

instance PrettyA NetworkMagic where prettyA = ppNetworkMagic

instance PrettyA (BootstrapAddress c) where prettyA = ppBootstrapAddress

instance PrettyA UnparsedFields where prettyA = ppUnparsedFields

-- ===========================================
-- Shelley.Spec.Ledger.Address

ppAddr :: Addr c -> PDoc
ppAddr (Addr net cred ref) = ppSexp "Addr" [ppNetwork net, ppCredential cred, ppStakeReference ref]
ppAddr (AddrBootstrap x) = ppSexp' mempty [ppBootstrapAddress x]

ppHDAddressPayload :: HDAddressPayload -> PDoc
ppHDAddressPayload (HDAddressPayload x) = ppLong x

ppRewardAcnt :: RewardAcnt c -> PDoc
ppRewardAcnt (RewardAcnt net cred) = ppRecord "RewardAcnt" [("network", ppNetwork net), ("credential", ppCredential cred)]

instance PrettyA (Addr c) where prettyA = ppAddr

instance PrettyA (RewardAcnt c) where prettyA = ppRewardAcnt

-- ===========================================
-- Shelley.Spec.Ledger.Credential

ppCredential :: Credential keyrole c -> PDoc
ppCredential (ScriptHashObj (ScriptHash x)) = ppSexp "ScriptCred" [ppHash x]
ppCredential (KeyHashObj (KeyHash x)) = ppSexp "KeyCred" [ppHash x]

ppPtr :: Ptr -> PDoc
ppPtr (Ptr slot n m) = ppSexp "Ptr" [ppSlotNo slot, pretty n, pretty m]

ppStakeReference :: StakeReference c -> PDoc
ppStakeReference (StakeRefBase x) = ppSexp "BaseRef" [ppCredential x]
ppStakeReference (StakeRefPtr x) = ppSexp "PtrRef" [ppPtr x]
ppStakeReference (StakeRefNull) = text "NullRef"

ppGenesisCredential :: GenesisCredential c -> PDoc
ppGenesisCredential (GenesisCredential (KeyHash x)) = ppSexp "GenesisCredential" [ppHash x]

instance PrettyA (Credential r c) where prettyA = ppCredential

instance PrettyA (StakeReference c) where prettyA = ppStakeReference

instance PrettyA (GenesisCredential c) where prettyA = ppGenesisCredential

instance PrettyA Ptr where prettyA = ppPtr

-- ===========================================
-- Shelley.Spec.Ledger.Scripts

ppMultiSig :: Crypto crypto => MultiSig crypto -> PDoc
ppMultiSig (RequireSignature hk) = ppSexp "Require" [ppKeyHash hk]
ppMultiSig (RequireAllOf ps) = ppSexp "AllOf" (map ppMultiSig ps)
ppMultiSig (RequireAnyOf ps) = ppSexp "AnyOf" (map ppMultiSig ps)
ppMultiSig (RequireMOf m ps) = ppSexp "MOf" (pretty m : map ppMultiSig ps)

ppScriptHash :: ScriptHash crypto -> PDoc
ppScriptHash (ScriptHash h) = ppSexp "ScriptHash" [ppHash h]

instance PrettyA (ScriptHash c) where prettyA = ppScriptHash

instance Crypto c => PrettyA (MultiSig c) where prettyA = ppMultiSig

-- ====================================================
-- Shelley.Spec.Ledger.Slot

ppSlotNo :: SlotNo -> Doc ann
ppSlotNo (SlotNo x) = text "SlotNo" <+> pretty x

ppDuration :: Duration -> Doc ann
ppDuration (Duration x) = text "Duration" <+> pretty x

ppEpochNo :: EpochNo -> Doc ann
ppEpochNo (EpochNo x) = text "EpochNo" <+> pretty x

ppEpochSize :: EpochSize -> Doc ann
ppEpochSize (EpochSize x) = text "EpochSize" <+> pretty x

ppBlockNo :: BlockNo -> Doc ann
ppBlockNo (BlockNo x) = text "BlockNo" <+> pretty x

instance PrettyA SlotNo where prettyA = ppSlotNo

instance PrettyA Duration where prettyA = ppDuration

instance PrettyA EpochNo where prettyA = ppEpochNo

instance PrettyA EpochSize where prettyA = ppEpochSize

instance PrettyA BlockNo where prettyA = ppBlockNo

-- ===================================================
-- Shelley.Spec.Ledger.OCert

ppKESPeriod :: KESPeriod -> PDoc
ppKESPeriod (KESPeriod x) = text "KESPeriod" <+> pretty x

ppOCertEnv :: OCertEnv crypto -> PDoc
ppOCertEnv (OCertEnv ps ds) =
  ppRecord
    "OCertEnv"
    [ ("ocertEnvStPools", ppSet ppKeyHash ps),
      ("ocertEnvGenDelegs", ppSet ppKeyHash ds)
    ]

ppOCert :: forall crypto. Crypto crypto => OCert crypto -> PDoc
ppOCert (OCert vk n per sig) =
  ppRecord
    "OCert"
    [ ("ocertVkKot", ppVerKeyKES (Proxy @crypto) vk),
      ("ocertN", pretty n),
      ("ocertKESPeriod", ppKESPeriod per),
      ("ocertSigma", ppSignedDSIGN sig)
    ]

ppOCertSignable :: forall crypto. Crypto crypto => OCertSignable crypto -> PDoc
ppOCertSignable (OCertSignable verkes w per) = ppSexp "OCertSignable" [ppVerKeyKES (Proxy @crypto) verkes, pretty w, ppKESPeriod per]

instance PrettyA KESPeriod where prettyA = ppKESPeriod

instance PrettyA (OCertEnv c) where prettyA = ppOCertEnv

instance Crypto c => PrettyA (OCert c) where prettyA = ppOCert

instance Crypto c => PrettyA (OCertSignable c) where prettyA = ppOCertSignable

-- ==========================================
--  Cardano.Crypto.Hash

ppHash :: Hash.Hash a b -> PDoc
ppHash x = text "#" <> reAnnotate (Width 5 :) (viaShow x)

instance PrettyA (Hash.Hash a b) where prettyA = ppHash

-- ==========================================
-- Shelley.Spec.Ledger.BaseTypes

ppUnitInterval :: UnitInterval -> PDoc
ppUnitInterval z = viaShow z

ppNonce :: Nonce -> PDoc
ppNonce (Nonce h) = text "Nonce" <+> ppHash h
ppNonce (NeutralNonce) = text "NeutralNonce"

ppActiveSlotCoeff :: ActiveSlotCoeff -> PDoc
ppActiveSlotCoeff x =
  ppRecord
    "ActiveSlotCoeff"
    [ ("activeSlotVal", viaShow (activeSlotVal x)),
      ("ActiveSlotLog", ppFixedPoint (activeSlotLog x))
    ]

ppGlobals :: Globals -> PDoc
ppGlobals
  ( Globals
      _e
      slot
      stab
      ran
      sec
      maxkes
      quor
      maxmaj
      maxlove
      active
      net
      start
    ) =
    ppRecord
      "Globals"
      [ ("epochInfo", text "?"),
        ("slotsPerKESPeriod", pretty slot),
        ("stabilityWindow", pretty stab),
        ("randomnessStabilisationWindow", pretty ran),
        ("securityParameter", pretty sec),
        ("maxKESEvo", pretty maxkes),
        ("quorum", pretty quor),
        ("maxMajorPV", pretty maxmaj),
        ("maxLovelaceSupply", pretty maxlove),
        ("activeSlotCoeff", ppActiveSlotCoeff active),
        ("networkId", ppNetwork net),
        ("systemStart", ppSystemStart start)
      ]

ppNetwork :: Network -> PDoc
ppNetwork Testnet = text "Testnet"
ppNetwork Mainnet = text "Mainnet"

ppSystemStart :: SystemStart -> PDoc
ppSystemStart (SystemStart time) = viaShow time

ppUrl :: Url -> PDoc
ppUrl x = text (urlToText x)

ppPort :: Port -> PDoc
ppPort (Port n) = ppSexp "Port" [ppWord16 n]

ppDnsName :: DnsName -> PDoc
ppDnsName x = ppSexp "DnsName" [text (dnsToText x)]

instance PrettyA Url where prettyA = ppUrl

instance PrettyA Network where prettyA = ppNetwork

instance PrettyA Globals where prettyA = ppGlobals

instance PrettyA ActiveSlotCoeff where prettyA = ppActiveSlotCoeff

instance PrettyA Nonce where prettyA = ppNonce

instance PrettyA UnitInterval where prettyA = ppUnitInterval

instance PrettyA Port where prettyA = ppPort

instance PrettyA DnsName where prettyA = ppDnsName

-- ===========================================
-- Shelley.Spec.Ledger.Keys

ppVKey :: Crypto c => (VKey r c) -> PDoc
ppVKey (VKey x) = reAnnotate (Width 5 :) (viaShow x)

ppKeyPair :: Crypto c => (KeyPair r c) -> PDoc
ppKeyPair (KeyPair x y) =
  ppRecord "KeyPair" [("vKey", ppVKey x), ("sKey", reAnnotate (Width 5 :) (viaShow y))]

ppKeyHash :: KeyHash x c -> PDoc
ppKeyHash (KeyHash x) = ppSexp "KeyHash" [ppHash x]

ppGenDelegPair :: GenDelegPair c -> PDoc
ppGenDelegPair (GenDelegPair (KeyHash x) y) =
  ppRecord "GenDelegPair" [("KeyHash", ppHash x), ("VrfHash", ppHash y)]

ppGKeys :: Crypto c => GKeys c -> PDoc
ppGKeys (GKeys x) = ppSexp "GKeys" [ppSet ppVKey x]

ppVerKeyKES :: forall crypto. Crypto crypto => Proxy crypto -> VerKeyKES crypto -> PDoc
ppVerKeyKES Proxy x = reAnnotate (Width 5 :) (viaShow x)

ppGenDelegs :: GenDelegs c -> PDoc
ppGenDelegs (GenDelegs m) = ppSexp "GenDelegs" [ppMap ppKeyHash ppGenDelegPair m]

instance Crypto c => PrettyA (VKey r c) where prettyA = ppVKey

instance Crypto c => PrettyA (KeyPair r c) where prettyA = ppKeyPair

instance PrettyA (KeyHash x c) where prettyA = ppKeyHash

instance Crypto c => PrettyA (GKeys c) where prettyA = ppGKeys

instance PrettyA (GenDelegPair c) where prettyA = ppGenDelegPair

instance PrettyA (GenDelegs c) where prettyA = ppGenDelegs

-- ======================================================

-- | Used to test pretty printing things with different widths
--   for example: testwidth 120 ls ppLedgerState
--   prints LedgerState, ls, with a max width of 120 columns
--   one can use this to observe the how "pretty" a printer is at different widths
atWidth :: Int -> a -> (a -> PDoc) -> IO ()
atWidth n a pp = do
  let doc = pp a
  putDocW n doc
  putStrLn ""

-- =========================================================

-- | Wrap a type: t (that has a PrettyA instance) with a newtype
--   cnstructor, so that the prettyA instance is used to Show (Nice t).
--   Can also be used as a DerivingVia helper.
newtype Nice t = Nice {unNice :: t}

instance PrettyA t => Show (Nice t) where
  show (Nice x) = show (prettyA x)
  showList xs more = show (ppList (prettyA . unNice) xs) ++ more

instance Eq t => Eq (Nice t) where
  (Nice x) == (Nice y) = x == y

instance PrettyA String where prettyA = ppString

instance PrettyA Double where prettyA = ppDouble

instance PrettyA Integer where prettyA = ppInteger

instance PrettyA Float where prettyA = ppFloat

instance PrettyA Natural where prettyA = ppNatural

instance PrettyA Word64 where prettyA = ppWord64

instance PrettyA Word32 where prettyA = ppWord32

instance PrettyA Word16 where prettyA = ppWord16

instance PrettyA Word8 where prettyA = ppWord8

instance PrettyA FixedPoint where prettyA = ppFixedPoint

instance PrettyA Bool where prettyA = ppBool

instance PrettyA Int where prettyA = ppInt
