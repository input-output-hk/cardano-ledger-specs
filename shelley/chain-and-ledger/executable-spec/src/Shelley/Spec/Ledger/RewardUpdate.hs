{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | How to compute the reward update compuation. Also, how to spread the
--     compuation over many blocks, once the chain reaches a stability point.
module Shelley.Spec.Ledger.RewardUpdate where

import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    encodeListLen,
  )
import Cardano.Ledger.BaseTypes
  ( ActiveSlotCoeff,
    NonNegativeInterval,
    ShelleyBase,
    UnitInterval,
    boundedRationalFromCBOR,
    boundedRationalToCBOR,
  )
import Cardano.Ledger.Coin (Coin (..), DeltaCoin (..))
import Cardano.Ledger.Credential (Credential (..))
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Serialization (decodeRecordNamed)
import Cardano.Slotting.Slot (EpochSize (..))
import Control.DeepSeq (NFData (..))
import Control.Provenance (ProvM, liftProv)
import Data.Coders
  ( Decode (..),
    Encode (..),
    decode,
    decodeStrictSeq,
    encode,
    encodeFoldable,
    mapDecode,
    mapEncode,
    setDecode,
    setEncode,
    (!>),
    (<!),
  )
import Data.Default.Class (def)
import Data.Foldable (fold)
import Data.Group (invert)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Pulse (Pulsable (..), completeM, foldlM')
import Data.Ratio ((%))
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import NoThunks.Class (NoThunks (..), allNoThunks)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.EpochBoundary
  ( SnapShots (..),
    Stake (..),
    poolStake,
  )
import Shelley.Spec.Ledger.PParams (ProtVer (..))
import Shelley.Spec.Ledger.RewardProvenance (RewardProvenancePool (..))
import qualified Shelley.Spec.Ledger.RewardProvenance as RP
import Shelley.Spec.Ledger.Rewards
  ( Likelihood,
    NonMyopic,
    Reward (..),
    leaderProbability,
    likelihood,
    rewardOnePool,
  )
import Shelley.Spec.Ledger.TxBody (PoolParams (..))

-- ===============================================================

-- | The result of reward calculation is a pair of aggregate Maps.
data RewardAns c
  = RewardAns
      !(Map (Credential 'Staking c) (Set (Reward c)))
      !(Map (KeyHash 'StakePool c) Likelihood)
  deriving (Show, Eq, Generic)
  deriving (NFData)

instance NoThunks (RewardAns crypto)

instance CC.Crypto c => ToCBOR (RewardAns c) where
  toCBOR (RewardAns x y) = toCBOR (x, y)

instance CC.Crypto c => FromCBOR (RewardAns c) where
  fromCBOR = (\(x, y) -> RewardAns x y) <$> fromCBOR

-- | The provenance we collect
type KeyHashPoolProvenance c = Map (KeyHash 'StakePool c) (RewardProvenancePool c)

-- | The type of RewardPulser we pulse on.
type Pulser c = RewardPulser c (ProvM (KeyHashPoolProvenance c) ShelleyBase) (RewardAns c)

-- =====================================

-- | The ultiate goal of a reward update computation.
--     Aggregating rewards for each staking credential.
data RewardUpdate crypto = RewardUpdate
  { deltaT :: !DeltaCoin,
    deltaR :: !DeltaCoin,
    rs :: !(Map (Credential 'Staking crypto) (Set (Reward crypto))),
    deltaF :: !DeltaCoin,
    nonMyopic :: !(NonMyopic crypto)
  }
  deriving (Show, Eq, Generic)

instance NoThunks (RewardUpdate crypto)

instance NFData (RewardUpdate crypto)

instance
  CC.Crypto crypto =>
  ToCBOR (RewardUpdate crypto)
  where
  toCBOR (RewardUpdate dt dr rw df nm) =
    encodeListLen 5
      <> toCBOR dt
      <> toCBOR (invert dr) -- TODO change Coin serialization to use integers?
      <> toCBOR rw
      <> toCBOR (invert df) -- TODO change Coin serialization to use integers?
      <> toCBOR nm

instance
  CC.Crypto crypto =>
  FromCBOR (RewardUpdate crypto)
  where
  fromCBOR = do
    decodeRecordNamed "RewardUpdate" (const 5) $ do
      dt <- fromCBOR
      dr <- fromCBOR -- TODO change Coin serialization to use integers?
      rw <- fromCBOR
      df <- fromCBOR -- TODO change Coin serialization to use integers?
      nm <- fromCBOR
      pure $ RewardUpdate dt (invert dr) rw (invert df) nm

emptyRewardUpdate :: RewardUpdate crypto
emptyRewardUpdate =
  RewardUpdate (DeltaCoin 0) (DeltaCoin 0) Map.empty (DeltaCoin 0) def

-- ===================================================

-- | To pulse the reward update, we need a snap shot of the EpochState particular to this computation
data RewardSnapShot crypto = RewardSnapShot
  { rewSnapshots :: !(SnapShots crypto),
    rewa0 :: !NonNegativeInterval,
    rewnOpt :: !Natural,
    rewprotocolVersion :: !ProtVer,
    rewNonMyopic :: !(NonMyopic crypto),
    rewDeltaR1 :: !Coin, -- deltaR1
    rewR :: !Coin, -- r
    rewDeltaT1 :: !Coin, -- deltaT1
    rewTotalStake :: !Coin, -- totalStake
    rewRPot :: !Coin -- rPot
  }
  deriving (Show, Eq, Generic)

instance NoThunks (RewardSnapShot crypto)

instance NFData (RewardSnapShot crypto)

instance CC.Crypto crypto => ToCBOR (RewardSnapShot crypto) where
  toCBOR (RewardSnapShot ss a0 nopt ver nm dr1 r dt1 tot pot) =
    encode
      ( Rec RewardSnapShot !> To ss !> E boundedRationalToCBOR a0 !> To nopt !> To ver !> To nm !> To dr1
          !> To r
          !> To dt1
          !> To tot
          !> To pot
      )

instance CC.Crypto crypto => FromCBOR (RewardSnapShot crypto) where
  fromCBOR = decode (RecD RewardSnapShot <! From <! D boundedRationalFromCBOR <! From <! From <! From <! From <! From <! From <! From <! From)

-- Some functions that only need a subset of the PParams can be
-- passed a RewardSnapShot, as it copies of some values from PParams

-- | RewardSnapShot can act as a Proxy for PParams where "_a0" is "Pool influence"
instance HasField "_a0" (RewardSnapShot crypto) NonNegativeInterval where
  getField x = rewa0 x

-- | RewardSnapShot can act as a Proxy for PParams where "_nOpt" is "Desired number of pools"
instance HasField "_nOpt" (RewardSnapShot crypto) Natural where
  getField x = rewnOpt x

-- | RewardSnapShot can act as a Proxy for PParams where "_protocolVersion" is " Protocol version"
instance HasField "_protocolVersion" (RewardSnapShot crypto) ProtVer where
  getField x = rewprotocolVersion x

-- ========================================================
-- FreeVars is the set of variables needed to compute
-- rewardStakePool, so that it can be made into a serializable
-- Pulsable function.

data FreeVars crypto = FreeVars
  { b :: !(Map (KeyHash 'StakePool crypto) Natural),
    delegs :: !(Map (Credential 'Staking crypto) (KeyHash 'StakePool crypto)),
    stake :: !(Stake crypto),
    addrsRew :: !(Set (Credential 'Staking crypto)),
    totalStake :: !Integer,
    activeStake :: !Integer,
    asc :: !ActiveSlotCoeff,
    totalBlocks :: !Natural, --
    r :: !Coin,
    slotsPerEpoch :: !EpochSize,
    pp_d :: !UnitInterval, -- The last three fields come from some version of PParams
    pp_a0 :: !NonNegativeInterval,
    pp_nOpt :: !Natural,
    pp_mv :: !Natural
  }
  deriving (Eq, Show, Generic)
  deriving (NoThunks)

instance NFData (FreeVars crypto)

instance (CC.Crypto crypto) => ToCBOR (FreeVars crypto) where
  toCBOR
    ( FreeVars
        { b,
          delegs,
          stake,
          addrsRew,
          totalStake,
          activeStake,
          asc,
          totalBlocks,
          r,
          slotsPerEpoch,
          pp_d,
          pp_a0,
          pp_nOpt,
          pp_mv
        }
      ) =
      encode
        ( Rec FreeVars !> mapEncode b !> mapEncode delegs !> To stake !> setEncode addrsRew
            !> To totalStake
            !> To activeStake
            !> To asc
            !> To totalBlocks
            !> To r
            !> To slotsPerEpoch
            !> To pp_d
            !> E boundedRationalToCBOR pp_a0
            !> To pp_nOpt
            !> To pp_mv
        )

instance (CC.Crypto crypto) => FromCBOR (FreeVars crypto) where
  fromCBOR =
    decode
      ( RecD FreeVars <! mapDecode {- b -} <! mapDecode {- delegs -} <! From {- stake -} <! setDecode {- addrsRew -}
          <! From {- totalStake -}
          <! From {- activeStake -}
          <! From {- asc -}
          <! From {- totalBlocks -}
          <! From {- r -}
          <! From {- slotsPerEpoch -}
          <! From {- pp_d -}
          <! D boundedRationalFromCBOR {- pp_a0 -}
          <! From {- pp_nOpt -}
          <! From {- pp_mv -}
      )

-- =====================================================================

-- | The function to call on each reward update pulse. Called by the pulser.
rewardStakePool ::
  Monad m =>
  FreeVars c ->
  RewardAns c ->
  PoolParams c ->
  ProvM (KeyHashPoolProvenance c) m (RewardAns c)
rewardStakePool
  ( FreeVars
      { b,
        delegs,
        stake,
        addrsRew,
        totalStake,
        activeStake,
        asc,
        totalBlocks,
        r,
        slotsPerEpoch,
        pp_d,
        pp_a0,
        pp_nOpt,
        pp_mv
      }
    )
  (RewardAns m1 m2)
  pparams = do
    let hk = _poolId pparams
        blocksProduced = Map.lookup hk b
        actgr@(Stake s) = poolStake hk delegs stake
        Coin pstake = fold s
        sigma = if totalStake == 0 then 0 else fromIntegral pstake % fromIntegral totalStake
        sigmaA = if activeStake == 0 then 0 else fromIntegral pstake % fromIntegral activeStake
        ls =
          likelihood
            (fromMaybe 0 blocksProduced)
            (leaderProbability asc sigma pp_d)
            slotsPerEpoch
    case blocksProduced of
      Nothing -> pure $ RewardAns m1 (Map.insert hk ls m2)
      Just n -> do
        m <- rewardOnePool (pp_d, pp_a0, pp_nOpt, pp_mv) r n totalBlocks pparams actgr sigma sigmaA (Coin totalStake) addrsRew
        pure $ RewardAns (Map.unionWith Set.union m m1) (Map.insert hk ls m2)

-- ================================================================

-- | The type of a Pulser which uses 'rewardStakePool' as its underlying function.
--     'rewardStakePool' will be partially applied to the component of type
--     (FreeVars c) when pulsing. Note that we use two type equality (~) constraints
--     to fix both the monad 'm' and the 'ans' type, to the context where we will use
--     the type as a Pulser. The type must have 'm' and 'ans' as its last two
--     parameters so we can make a Pulsable instance.
--     RSPL = Reward Serializable Listbased Pulser
data RewardPulser c (m :: Type -> Type) ans where
  RSLP ::
    (ans ~ RewardAns c, m ~ ProvM (KeyHashPoolProvenance c) ShelleyBase) =>
    !Int ->
    !(FreeVars c) ->
    !(StrictSeq (PoolParams c)) ->
    !ans ->
    RewardPulser c m ans

-- Because of the constraints on the Constructor RSLP, there is really only one inhabited
-- type:  (RewardPulser c (ProvM (KeyHashPoolProvenance c) ShelleyBase) (RewardAns c))
-- All of the instances are at that type. Though only the CBOR instances need make that explicit.

instance Pulsable (RewardPulser crypto) where
  done (RSLP _n _free zs _ans) = null zs
  current (RSLP _ _ _ ans) = ans
  pulseM ll@(RSLP _ _ StrictSeq.Empty _) = pure ll
  pulseM (RSLP n free balance ans) = do
    let !(steps, !balance') = StrictSeq.splitAt n balance
    ans' <- foldlM' (rewardStakePool free) ans steps
    pure (RSLP n free balance' ans')
  completeM (RSLP _ free balance ans) = foldlM' (rewardStakePool free) ans balance

deriving instance Eq ans => Eq (RewardPulser c m ans)

deriving instance Show ans => Show (RewardPulser c m ans)

instance NoThunks (Pulser c) where
  showTypeOf _ = "RewardPulser"
  wNoThunks ctxt (RSLP n free balance ans) =
    allNoThunks
      [ noThunks ctxt n,
        noThunks ctxt free,
        noThunks ctxt balance,
        noThunks ctxt ans
      ]

instance NFData (Pulser c) where
  rnf (RSLP n1 c1 b1 a1) = seq (rnf n1) (seq (rnf c1) (seq (rnf b1) (rnf a1)))

instance (CC.Crypto c) => ToCBOR (Pulser c) where
  toCBOR (RSLP n free balance ans) =
    encode (Rec RSLP !> To n !> To free !> E encodeFoldable balance !> To ans)

instance (CC.Crypto c) => FromCBOR (Pulser c) where
  fromCBOR =
    decode
      ( RecD RSLP <! From <! From <! D (decodeStrictSeq fromCBOR) <! From
      )

-- =========================================================================

-- | The state used in the STS rules
data PulsingRewUpdate crypto
  = Pulsing !(RewardSnapShot crypto) !(Pulser crypto) -- Pulsing work still to do
  | Complete !(RewardUpdate crypto) -- Pulsing work completed, ultimate goal reached
  deriving (Eq, Show, Generic, NoThunks)

instance (CC.Crypto crypto) => ToCBOR (PulsingRewUpdate crypto) where
  toCBOR (Pulsing s p) = encode (Sum Pulsing 0 !> To s !> To p)
  toCBOR (Complete r) = encode (Sum Complete 1 !> To r)

instance (CC.Crypto crypto) => FromCBOR (PulsingRewUpdate crypto) where
  fromCBOR = decode (Summands "PulsingRewUpdate" decPS)
    where
      decPS 0 = (SumD Pulsing <! From <! From)
      decPS 1 = (SumD Complete <! From)
      decPS n = Invalid n

instance NFData (PulsingRewUpdate crypto)

-- ====================================================================
-- Some generic lifting functions to lift one provenance computation
-- into another, and one to lift a Pulser from one provenance type to
-- another.  Then a specialisation on the Provenance types we use here.

-- | Lift a Pulser in the ProvM monad, from one type of provenance (s1) to another (s2)
pulseProvM ::
  (Monad m, Pulsable pulse) =>
  s1 ->
  (s1 -> s2 -> s2) ->
  pulse (ProvM s1 m) ans ->
  ProvM s2 m (pulse (ProvM s1 m) ans)
pulseProvM initial combine tma = liftProv (pulseM tma) initial (\_ s1 s2 -> combine s1 s2)

-- | lift a pulseM function from (KeyHashPoolProvenance (Crypto era))
--   provenance to (RewardProvenance (Crypto er)) provenance
pulseOther :: Pulser crypto -> ProvM (RP.RewardProvenance crypto) ShelleyBase (Pulser crypto)
pulseOther tma = pulseProvM Map.empty incrementProvenance tma

-- | How to merge KeyHashPoolProvenance into RewardProvenance
incrementProvenance :: (KeyHashPoolProvenance crypto) -> RP.RewardProvenance crypto -> RP.RewardProvenance crypto
incrementProvenance provpools (prov@(RP.RewardProvenance {RP.pools = old})) = prov {RP.pools = Map.union provpools old}
