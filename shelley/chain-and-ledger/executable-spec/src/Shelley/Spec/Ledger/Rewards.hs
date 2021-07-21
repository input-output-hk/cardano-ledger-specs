{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.Rewards
  ( desirability,
    PerformanceEstimate (..),
    NonMyopic (..),
    getTopRankedPools,
    StakeShare (..),
    mkApparentPerformance,
    RewardType (..),
    Reward (..),
    nonMyopicStake,
    nonMyopicMemberRew,
    percentile',
    Histogram (..),
    LogWeight (..),
    likelihood,
    applyDecay,
    Likelihood (..),
    leaderProbability,
    leaderRew,
    memberRew,
    aggregateRewards,
    sumRewards,
    rewardOnePool,
  )
where

import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    decodeDouble,
    decodeWord,
    encodeDouble,
    encodeListLen,
    encodeWord,
  )
import Cardano.Ledger.BaseTypes
  ( ActiveSlotCoeff,
    BoundedRational (..),
    NonNegativeInterval,
    UnitInterval,
    activeSlotVal,
    invalidKey,
  )
import Cardano.Ledger.Coin
  ( Coin (..),
    coinToRational,
    rationalToCoinViaFloor,
  )
import Cardano.Ledger.Credential (Credential (..))
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Serialization
  ( decodeRecordNamed,
    decodeSeq,
    encodeFoldable,
  )
import Cardano.Ledger.Val ((<->))
import Cardano.Slotting.Slot (EpochSize (..))
import Control.DeepSeq (NFData)
import Control.Provenance (ProvM, modifyM)
import Data.Coders (Decode (..), Encode (..), decode, encode, (!>), (<!))
import Data.Default.Class (Default, def)
import Data.Foldable (find, fold)
import Data.Function (on)
import Data.List (sortBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))
import qualified Data.Sequence as Seq
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import GHC.Records (HasField (getField))
import NoThunks.Class (NoThunks (..))
import Numeric.Natural (Natural)
import Quiet
import Shelley.Spec.Ledger.Delegation.PoolParams (poolSpec)
import Shelley.Spec.Ledger.EpochBoundary
  ( Stake (..),
    maxPool,
    maxPool',
  )
import qualified Shelley.Spec.Ledger.HardForks as HardForks
import Shelley.Spec.Ledger.PParams (ProtVer)
import Shelley.Spec.Ledger.RewardProvenance (RewardProvenancePool (..))
import Shelley.Spec.Ledger.TxBody (PoolParams (..), getRwdCred)

newtype LogWeight = LogWeight {unLogWeight :: Float}
  deriving (Eq, Generic, Ord, Num, NFData, NoThunks, ToCBOR, FromCBOR)
  deriving (Show) via Quiet LogWeight

toLogWeight :: Double -> LogWeight
toLogWeight d = LogWeight (realToFrac $ log d)

fromLogWeight :: LogWeight -> Double
fromLogWeight (LogWeight l) = exp (realToFrac l)

newtype Histogram = Histogram {unHistogram :: StrictSeq LogWeight}
  deriving (Eq, Show, Generic)

newtype Likelihood = Likelihood {unLikelihood :: StrictSeq LogWeight}
  -- TODO: replace with small data structure
  deriving (Show, Generic, NFData)

instance NoThunks Likelihood

instance Eq Likelihood where
  (==) = (==) `on` unLikelihood . normalizeLikelihood

instance Semigroup Likelihood where
  (Likelihood x) <> (Likelihood y) =
    normalizeLikelihood $ Likelihood (StrictSeq.zipWith (+) x y)

instance Monoid Likelihood where
  mempty = Likelihood $ StrictSeq.forceToStrict $ Seq.replicate (length samplePositions) (LogWeight 0)

normalizeLikelihood :: Likelihood -> Likelihood
normalizeLikelihood (Likelihood xs) = Likelihood $ (\x -> x - m) <$> xs
  where
    m = minimum xs

instance ToCBOR Likelihood where
  toCBOR (Likelihood logweights) = encodeFoldable logweights

instance FromCBOR Likelihood where
  fromCBOR = Likelihood . StrictSeq.forceToStrict <$> decodeSeq fromCBOR

leaderProbability :: ActiveSlotCoeff -> Rational -> UnitInterval -> Double
leaderProbability activeSlotCoeff relativeStake decentralizationParameter =
  (1 - (1 - asc) ** s) * (1 - d')
  where
    d' = realToFrac . unboundRational $ decentralizationParameter
    asc = realToFrac . unboundRational . activeSlotVal $ activeSlotCoeff
    s = realToFrac relativeStake

samplePositions :: StrictSeq Double
samplePositions = (\x -> (x + 0.5) / 100.0) <$> StrictSeq.fromList [0.0 .. 99.0]

likelihood ::
  Natural -> -- number of blocks produced this epoch
  Double -> -- chance we're allowed to produce a block in this slot
  EpochSize ->
  Likelihood
likelihood blocks t slotsPerEpoch =
  Likelihood $
    sample <$> samplePositions
  where
    -- The likelihood function L(x) is the probability of observing the data we got
    -- under the assumption that the underlying pool performance is equal to x.
    -- L(x) = C(n,m) * (tx)^n * (1-tx)^m
    -- where
    -- t is the chance we're allowed to produce a block
    -- n is the number of slots in which a block was produced
    -- m is the number of slots in which a block was not produced
    --      (slots per epoch minus n)
    -- C(n,m) is a coefficient that will be irrelevant
    -- Since the likelihood function only matters up to a scalar multiple, we will
    -- will divide out C(n,m) t^n and use the following instead:
    -- L(x) = x^n * (1-tx)^m
    -- We represent this function using 100 sample points, but to avoid very
    -- large exponents, we store the log of the value instead of the value itself.
    -- log(L(x)) = log [ x^n * (1-tx)^m ]
    --           = n * log(x) + m * log(1 - tx)
    -- TODO: worry more about loss of floating point precision
    --
    -- example:
    -- a pool has relative stake of 1 / 1,000,000 (~ 30k ada of 35b ada)
    -- f = active slot coefficient = 1/20
    -- t = 1 - (1-f)^(1/1,000,000)
    n = fromIntegral blocks
    m = fromIntegral $ slotsPerEpoch - fromIntegral blocks
    l :: Double -> Double
    l x = n * log x + m * log (1 - t * x)
    sample position = LogWeight (realToFrac $ l position)

-- | Decay previous likelihood
applyDecay :: Float -> Likelihood -> Likelihood
applyDecay decay (Likelihood logWeights) = Likelihood $ mul decay <$> logWeights
  where
    mul x (LogWeight f) = LogWeight (x * f)

posteriorDistribution :: Histogram -> Likelihood -> Histogram
posteriorDistribution (Histogram points) (Likelihood likelihoods) =
  normalize $
    Histogram $ StrictSeq.zipWith (+) points likelihoods

-- | Normalize the histogram so that the total area is 1
normalize :: Histogram -> Histogram
normalize (Histogram values) = Histogram $ (\x -> x - logArea) <$> values'
  where
    m = maximum values
    values' = (\x -> x - m) <$> values
    logArea = toLogWeight area
    area = reimannSum 0.01 (fromLogWeight <$> values')

-- | Calculate the k percentile for this distribution.
-- k is a value between 0 and 1. The 0 percentile is 0 and the 1 percentile is 1
percentile :: Double -> Histogram -> Likelihood -> PerformanceEstimate
percentile p prior likelihoods =
  PerformanceEstimate . fst $
    fromMaybe (1, 1) $
      find (\(_x, fx) -> fx > p) cdf
  where
    (Histogram values) = posteriorDistribution prior likelihoods
    cdf =
      Seq.zip
        (StrictSeq.fromStrict samplePositions)
        (StrictSeq.fromStrict (StrictSeq.scanl (+) 0 (fromLogWeight <$> values)))

percentile' :: Likelihood -> PerformanceEstimate
percentile' = percentile 0.5 h
  where
    h = normalize . Histogram $ logBeta 40 1 <$> samplePositions
    -- Beta(n,m)(x) = C * x^(n-1)*(1-x)^(m-1)
    -- log( Beta(n,m)(x) ) = (n-1) * log x + (m-1) * log (1-x)
    logBeta n m x = LogWeight . realToFrac $ (n -1) * log x + (m -1) * log (1 - x)

reimannSum :: (Functor f, Foldable f) => Double -> f Double -> Double
reimannSum width heights = sum $ fmap (width *) heights

-- | This is a estimate of the proportion of allowed blocks a pool will
-- make in the future. It is used for ranking pools in delegation.
newtype PerformanceEstimate = PerformanceEstimate {unPerformanceEstimate :: Double}
  deriving (Show, Eq, Generic, NoThunks)

instance ToCBOR PerformanceEstimate where
  toCBOR = encodeDouble . unPerformanceEstimate

instance FromCBOR PerformanceEstimate where
  fromCBOR = PerformanceEstimate <$> decodeDouble

data NonMyopic crypto = NonMyopic
  { likelihoodsNM :: !(Map (KeyHash 'StakePool crypto) Likelihood),
    rewardPotNM :: !Coin
  }
  deriving (Show, Eq, Generic)

instance Default (NonMyopic crypto) where
  def = NonMyopic Map.empty (Coin 0)

instance NoThunks (NonMyopic crypto)

instance NFData (NonMyopic crypto)

instance CC.Crypto crypto => ToCBOR (NonMyopic crypto) where
  toCBOR
    NonMyopic
      { likelihoodsNM = aps,
        rewardPotNM = rp
      } =
      encodeListLen 3
        <> toCBOR aps
        <> toCBOR rp

instance CC.Crypto crypto => FromCBOR (NonMyopic crypto) where
  fromCBOR = do
    decodeRecordNamed "NonMyopic" (const 3) $ do
      aps <- fromCBOR
      rp <- fromCBOR
      pure $
        NonMyopic
          { likelihoodsNM = aps,
            rewardPotNM = rp
          }

-- | Desirability calculation for non-myopic utility,
-- corresponding to f^~ in section 5.6.1 of
-- "Design Specification for Delegation and Incentives in Cardano"
desirability ::
  (NonNegativeInterval, Natural) ->
  Coin ->
  PoolParams c ->
  PerformanceEstimate ->
  Coin ->
  Double
desirability (a0, nOpt) r pool (PerformanceEstimate p) (Coin totalStake) =
  if fTilde <= cost
    then 0
    else (fTilde - cost) * (1 - margin)
  where
    fTilde = fTildeNumer / fTildeDenom
    fTildeNumer = p * fromRational (coinToRational r * (z0 + min s z0 * unboundRational a0))
    fTildeDenom = fromRational $ 1 + unboundRational a0
    cost = (fromRational . coinToRational . _poolCost) pool
    margin = (fromRational . unboundRational . _poolMargin) pool
    tot = max 1 (fromIntegral totalStake)
    Coin pledge = _poolPledge pool
    s = fromIntegral pledge % tot
    z0 = 1 % max 1 (fromIntegral nOpt)

-- | Computes the top ranked stake pools
-- corresponding to section 5.6.1 of
-- "Design Specification for Delegation and Incentives in Cardano"
getTopRankedPools ::
  (HasField "_a0" pp NonNegativeInterval, HasField "_nOpt" pp Natural) =>
  Coin ->
  Coin ->
  pp ->
  Map (KeyHash 'StakePool crypto) (PoolParams crypto) ->
  Map (KeyHash 'StakePool crypto) PerformanceEstimate ->
  Set (KeyHash 'StakePool crypto)
getTopRankedPools rPot totalStake pp poolParams aps =
  Set.fromList $
    fst
      <$> take (fromIntegral $ getField @"_nOpt" pp) (sortBy (flip compare `on` snd) rankings)
  where
    pdata = Map.toList $ Map.intersectionWith (,) poolParams aps
    rankings =
      [ ( hk,
          desirability (getField @"_a0" pp, getField @"_nOpt" pp) rPot pool ap totalStake
        )
        | (hk, (pool, ap)) <- pdata
      ]

-- | StakeShare type
newtype StakeShare = StakeShare {unStakeShare :: Rational}
  deriving (Generic, Ord, Eq, NoThunks)
  deriving (Show) via Quiet StakeShare

-- | Calculate pool reward
mkApparentPerformance ::
  UnitInterval ->
  Rational ->
  Natural ->
  Natural ->
  Rational
mkApparentPerformance d_ sigma blocksN blocksTotal
  | sigma == 0 = 0
  | unboundRational d_ < 0.8 = beta / sigma
  | otherwise = 1
  where
    beta = fromIntegral blocksN / fromIntegral (max 1 blocksTotal)

-- | Calculate pool leader reward
leaderRew ::
  Coin ->
  PoolParams crypto ->
  StakeShare ->
  StakeShare ->
  Coin
leaderRew f pool (StakeShare s) (StakeShare sigma)
  | f <= c = f
  | otherwise =
    c
      <> rationalToCoinViaFloor
        (coinToRational (f <-> c) * (m' + (1 - m') * s / sigma))
  where
    (c, m, _) = poolSpec pool
    m' = unboundRational m

-- | Calculate pool member reward
memberRew ::
  Coin ->
  PoolParams crypto ->
  StakeShare ->
  StakeShare ->
  Coin
memberRew (Coin f') pool (StakeShare t) (StakeShare sigma)
  | f' <= c = mempty
  | otherwise =
    rationalToCoinViaFloor $
      fromIntegral (f' - c) * (1 - m') * t / sigma
  where
    (Coin c, m, _) = poolSpec pool
    m' = unboundRational m

data RewardType = MemberReward | LeaderReward
  deriving (Eq, Show, Ord, Generic)

instance NoThunks RewardType

instance NFData RewardType

instance ToCBOR RewardType where
  toCBOR MemberReward = encodeWord 0
  toCBOR LeaderReward = encodeWord 1

instance FromCBOR RewardType where
  fromCBOR =
    decodeWord >>= \case
      0 -> pure MemberReward
      1 -> pure LeaderReward
      n -> invalidKey n

data Reward crypto = Reward
  { rewardType :: RewardType,
    rewardPool :: KeyHash 'StakePool crypto,
    rewardAmount :: Coin
  }
  deriving (Eq, Show, Generic)

-- | Note that this Ord instance is chosen to align precisely
--  with the Allegra reward aggregation, as given by the
--  function 'aggregateRewards' so that 'Set.findMax' returns
--  the expected value.
instance Ord (Reward crypto) where
  compare (Reward MemberReward _ _) (Reward LeaderReward _ _) = GT
  compare (Reward LeaderReward _ _) (Reward MemberReward _ _) = LT
  compare (Reward _ pool1 _) (Reward _ pool2 _) = compare pool1 pool2

instance NoThunks (Reward crypto)

instance NFData (Reward crypto)

instance CC.Crypto crypto => ToCBOR (Reward crypto) where
  toCBOR (Reward rt pool c) =
    encode $ Rec Reward !> To rt !> To pool !> To c

instance CC.Crypto crypto => FromCBOR (Reward crypto) where
  fromCBOR =
    decode $ RecD Reward <! From <! From <! From

sumRewards ::
  forall crypto pp.
  (HasField "_protocolVersion" pp ProtVer) =>
  pp ->
  Map (Credential 'Staking crypto) (Set (Reward crypto)) ->
  Coin
sumRewards protocolVersion rs = fold $ aggregateRewards protocolVersion rs

aggregateRewards ::
  forall crypto pp.
  (HasField "_protocolVersion" pp ProtVer) =>
  pp ->
  Map (Credential 'Staking crypto) (Set (Reward crypto)) ->
  Map (Credential 'Staking crypto) Coin
aggregateRewards pp rewards =
  if HardForks.aggregatedRewards pp
    then Map.map (Set.foldr addRewardToCoin mempty) rewards
    else Map.map lastByOrd rewards
  where
    addRewardToCoin r = (<>) (rewardAmount r)
    -- s should never be null, but we are being cautious
    lastByOrd s = if Set.null s then mempty else (rewardAmount . Set.findMin) s

-- | Reward one pool. The first argument (the triple (pp_d, pp_a0, pp_nOpt))
--     is a subset of the fields of PParams
--     { _d :: !(HKD f UnitInterval) --  Decentralization parameter
--     , _a0 :: !(HKD f NonNegativeInterval),   -- Pool influence
--     , _nOpt :: !(HKD f Natural)   -- Desired number of pools
--     }
rewardOnePool ::
  forall c m.
  Monad m =>
  (UnitInterval, NonNegativeInterval, Natural, Natural) ->
  Coin ->
  Natural ->
  Natural ->
  PoolParams c ->
  Stake c ->
  Rational ->
  Rational ->
  Coin ->
  Set (Credential 'Staking c) ->
  ProvM
    (Map (KeyHash 'StakePool c) (RewardProvenancePool c))
    m
    (Map (Credential 'Staking c) (Set (Reward c)))
rewardOnePool
  (pp_d, pp_a0, pp_nOpt, pp_mv)
  -- (Decentralization parameter, Pool influence, Desired number of pools, major version)
  r
  blocksN
  blocksTotal
  pool
  (Stake stake)
  sigma
  sigmaA
  (Coin totalStake)
  addrsRew = modifyM (Map.insert key provPool) >> pure rewards'
    where
      Coin ostake =
        Set.foldl'
          (\c o -> c <> (fromMaybe mempty $ Map.lookup (KeyHashObj o) stake))
          mempty
          (_poolOwners pool)
      Coin pledge = _poolPledge pool
      pr = fromIntegral pledge % fromIntegral totalStake
      (Coin maxP) =
        if pledge <= ostake
          then maxPool' pp_a0 pp_nOpt r sigma pr
          else mempty
      appPerf = mkApparentPerformance pp_d sigmaA blocksN blocksTotal
      poolR = rationalToCoinViaFloor (appPerf * fromIntegral maxP)
      tot = fromIntegral totalStake
      mRewards =
        Map.fromList
          [ ( hk,
              Set.singleton $
                Reward
                  MemberReward
                  (_poolId pool)
                  ( memberRew
                      poolR
                      pool
                      (StakeShare (fromIntegral c % tot))
                      (StakeShare sigma)
                  )
            )
            | (hk, Coin c) <- Map.toList stake,
              notPoolOwner hk,
              hk `Set.member` addrsRew
          ]
      notPoolOwner (KeyHashObj hk) = hk `Set.notMember` _poolOwners pool
      notPoolOwner (ScriptHashObj _) = HardForks.allowScriptStakeCredsToEarnRewards pp_mv
      lReward =
        leaderRew
          poolR
          pool
          (StakeShare $ fromIntegral ostake % tot)
          (StakeShare sigma)
      poolRA = getRwdCred $ _poolRAcnt pool
      potentialRewards =
        if poolRA `Set.member` addrsRew
          then
            Map.insertWith
              Set.union
              poolRA
              (Set.singleton (Reward LeaderReward (_poolId pool) lReward))
              mRewards
          else mRewards
      removeDegenerate rwds =
        let notZeroMember (Reward MemberReward _ c) = c /= Coin 0
            notZeroMember (Reward LeaderReward _ _) = True
            -- We do not filter out zero valued Leader rewards since
            -- prior to protocol version 3 the zero values can serve
            -- as evidence that a member reward was overridden.
            withoutZeros = Set.filter notZeroMember rwds
         in if Set.null withoutZeros
              then Nothing
              else Just withoutZeros
      rewards' = Map.mapMaybe removeDegenerate potentialRewards
      key = _poolId pool
      provPool =
        RewardProvenancePool
          { poolBlocksP = blocksN,
            sigmaP = sigma,
            sigmaAP = sigmaA,
            ownerStakeP = Coin ostake,
            poolParamsP = pool,
            pledgeRatioP = pr,
            maxPP = Coin maxP,
            appPerfP = appPerf,
            poolRP = poolR,
            lRewardP = lReward
          }

-- | Compute the Non-Myopic Pool Stake
--
--   This function implements non-myopic stake calculation in section 5.6.2
--   of "Design Specification for Delegation and Incentives in Cardano".
--   Note that the protocol parameters are implicit in the design document.
--   Additionally, instead of passing a rank r to compare with k,
--   we pass the top k desirable pools and check for membership.
nonMyopicStake ::
  HasField "_nOpt" pp Natural =>
  pp ->
  StakeShare ->
  StakeShare ->
  StakeShare ->
  KeyHash 'StakePool c ->
  Set (KeyHash 'StakePool c) ->
  StakeShare
nonMyopicStake pp (StakeShare s) (StakeShare sigma) (StakeShare t) kh topPools =
  let z0 = 1 % max 1 (fromIntegral (getField @"_nOpt" pp))
   in if kh `Set.member` topPools
        then StakeShare (max (sigma + t) z0)
        else StakeShare (s + t)

-- | Compute the Non-Myopic Pool Member Reward
--
--   This function implements equation (3) in section 5.6.4
--   of "Design Specification for Delegation and Incentives in Cardano".
--   Note that the protocol parameters and the reward pot are implicit
--   in the design document. Additionally, instead of passing a rank
--   r to compare with k, we pass the top k desirable pools and
--   check for membership.
nonMyopicMemberRew ::
  ( HasField "_a0" pp NonNegativeInterval,
    HasField "_nOpt" pp Natural
  ) =>
  pp ->
  Coin ->
  PoolParams c ->
  StakeShare ->
  StakeShare ->
  StakeShare ->
  Set (KeyHash 'StakePool c) ->
  PerformanceEstimate ->
  Coin
nonMyopicMemberRew
  pp
  rPot
  pool
  s
  sigma
  t
  topPools
  (PerformanceEstimate p) =
    let nm = nonMyopicStake pp s sigma t (_poolId pool) topPools
        f = maxPool pp rPot (unStakeShare nm) (unStakeShare s)
        fHat = floor (p * (fromRational . coinToRational) f)
     in memberRew (Coin fHat) pool t nm
