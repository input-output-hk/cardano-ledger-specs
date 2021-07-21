{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | Currently this uses the trace mechansim to check that computing rewards has
-- a required set of properties. It works only in the Shelley Era. It could be
-- generalized, and then moved to the Generator/Trace/ directory which computes
-- property tests in all eras.
module Test.Shelley.Spec.Ledger.Rewards (rewardTests, C, defaultMain, newEpochProp) where

import Cardano.Binary (toCBOR)
import qualified Cardano.Crypto.DSIGN as Crypto
import Cardano.Crypto.Hash (MD5, hashToBytes)
import Cardano.Crypto.Seed (mkSeedFromBytes)
import qualified Cardano.Crypto.VRF as Crypto
import Cardano.Ledger.BaseTypes
  ( ActiveSlotCoeff,
    BoundedRational (..),
    Globals (..),
    Network (..),
    NonNegativeInterval,
    ShelleyBase,
    StrictMaybe (..),
    UnitInterval,
    activeSlotVal,
    epochInfo,
    mkActiveSlotCoeff,
  )
import Cardano.Ledger.Coin (Coin (..), DeltaCoin (..), rationalToCoinViaFloor, toDeltaCoin)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential (Credential (..))
import Cardano.Ledger.Crypto (VRF)
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Keys
  ( KeyHash,
    KeyPair (..),
    KeyRole (..),
    VKey (..),
    hashKey,
    hashWithSerialiser,
    vKey,
  )
-- (TestTree, defaultMain, testGroup)

import Cardano.Ledger.Pretty (PrettyA (..))
import Cardano.Ledger.Slot (epochInfoSize)
import Cardano.Ledger.Val (invert, (<+>), (<->))
import Cardano.Slotting.Slot (EpochSize (..))
import Control.Iterate.SetAlgebra (eval, (◁))
import Control.Monad (replicateM)
import Control.Monad.Trans.Reader (asks, runReader)
import Control.Provenance (ProvM, preservesJust, preservesNothing, runProvM, runWithProvM)
import Control.State.Transition.Trace (SourceSignalTarget (..), sourceSignalTargets)
import Data.Default.Class (Default (def))
import Data.Foldable (fold)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Proxy
import Data.Pulse (Pulsable (..))
import Data.Ratio ((%))
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word (Word64)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.API.Wallet (getRewardInfo)
import Shelley.Spec.Ledger.EpochBoundary
  ( BlocksMade (..),
    SnapShot (..),
    SnapShots (..),
    Stake (..),
    maxPool,
    poolStake,
  )
import qualified Shelley.Spec.Ledger.EpochBoundary as EB
import qualified Shelley.Spec.Ledger.HardForks as HardForks
import Shelley.Spec.Ledger.LedgerState
  ( AccountState (..),
    DPState (..),
    DState (..),
    EpochState (..),
    LedgerState (..),
    NewEpochState (..),
    RewardUpdate (..),
    circulation,
    createRUpd,
    updateNonMyopic,
  )
import Shelley.Spec.Ledger.PParams
  ( PParams,
    PParams' (..),
    ProtVer (..),
    emptyPParams,
  )
import Shelley.Spec.Ledger.RewardUpdate
  ( FreeVars (..),
    KeyHashPoolProvenance,
    Pulser,
    RewardAns (..),
    RewardPulser (RSLP),
  )
import Shelley.Spec.Ledger.Rewards
  ( Likelihood,
    NonMyopic,
    StakeShare (..),
    aggregateRewards,
    leaderProbability,
    leaderRew,
    likelihood,
    memberRew,
    mkApparentPerformance,
    sumRewards,
  )
import Shelley.Spec.Ledger.STS.Chain (ChainState (..))
import Shelley.Spec.Ledger.TxBody (PoolParams (..), RewardAcnt (..))
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C)
import Test.Shelley.Spec.Ledger.Generator.Core (genCoin, genNatural)
import Test.Shelley.Spec.Ledger.Generator.ShelleyEraGen ()
import Test.Shelley.Spec.Ledger.Rules.TestChain (forAllChainTrace)
import Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators ()
import Test.Shelley.Spec.Ledger.Serialisation.Generators ()
import Test.Shelley.Spec.Ledger.Utils
  ( runShelleyBase,
    testGlobals,
    unsafeBoundRational,
  )
import Test.Tasty
import Test.Tasty.HUnit (testCaseInfo)
import Test.Tasty.QuickCheck
  ( Gen,
    Property,
    arbitrary,
    choose,
    counterexample,
    elements,
    generate,
    property,
    testProperty,
    withMaxSuccess,
    (===),
  )

-- ========================================================================
-- Bounds and Constants --

maxNumPools :: Int
maxNumPools = 100

maxNumMembers :: Int
maxNumMembers = 100

maxMemberLovelace :: Integer
maxMemberLovelace = 100000

maxOwnerLovelaceAbovePledge :: Integer
maxOwnerLovelaceAbovePledge = 100000

maxPoolPledeg :: Integer
maxPoolPledeg = 1000000

maxPoolCost :: Integer
maxPoolCost = 1000000

maxPoolBlocks :: Natural
maxPoolBlocks = 1000000

numberOfTests :: Int
numberOfTests = 500

decentralizationRange :: [Rational]
decentralizationRange = [0, 0.1 .. 1]

tauRange :: [Rational]
tauRange = [0, 0.05 .. 0.3]

rhoRange :: [Rational]
rhoRange = [0, 0.05 .. 0.3]

-- Helpers --

keyPair :: CC.Crypto crypto => Int -> KeyPair r crypto
keyPair seed = KeyPair vk sk
  where
    vk = VKey (Crypto.deriveVerKeyDSIGN sk)
    sk =
      Crypto.genKeyDSIGN $
        mkSeedFromBytes . hashToBytes $
          hashWithSerialiser @MD5 toCBOR seed

vrfKeyPair :: forall v. Crypto.VRFAlgorithm v => Int -> (Crypto.SignKeyVRF v, Crypto.VerKeyVRF v)
vrfKeyPair seed = (sk, vk)
  where
    vk = Crypto.deriveVerKeyVRF sk
    sk =
      Crypto.genKeyVRF $
        mkSeedFromBytes . hashToBytes $
          hashWithSerialiser @MD5 toCBOR seed

data PoolSetUpArgs crypto f = PoolSetUpArgs
  { poolPledge :: f Coin,
    poolCost :: f Coin,
    poolMargin :: f UnitInterval,
    poolMembers :: f (Map (Credential 'Staking crypto) Coin)
  }

emptySetupArgs :: PoolSetUpArgs crypto Maybe
emptySetupArgs =
  PoolSetUpArgs
    { poolPledge = Nothing,
      poolCost = Nothing,
      poolMargin = Nothing,
      poolMembers = Nothing
    }

data PoolInfo crypto = PoolInfo
  { params :: PoolParams crypto,
    coldKey :: KeyPair 'StakePool crypto,
    ownerKey :: KeyPair 'Staking crypto,
    ownerStake :: Coin,
    rewardKey :: KeyPair 'Staking crypto,
    members :: Map (Credential 'Staking crypto) Coin
  }

-- Generators --

genNonOwnerMembers :: CC.Crypto crypto => Gen (Map (Credential 'Staking crypto) Coin)
genNonOwnerMembers = do
  numMembers <- choose (0, maxNumMembers)
  fmap Map.fromList . replicateM numMembers $ do
    credential <- KeyHashObj . hashKey . vKey . keyPair <$> arbitrary
    coins <- genCoin 0 maxMemberLovelace
    pure (credential, coins)

getOrGen :: Maybe a -> Gen a -> Gen a
getOrGen (Just x) _ = pure x
getOrGen Nothing g = g

genMargin :: Gen UnitInterval
genMargin = do
  let denom = 10
  numer <- choose (0, denom)
  pure $ unsafeBoundRational (numer % denom)

genPoolInfo :: forall crypto. CC.Crypto crypto => PoolSetUpArgs crypto Maybe -> Gen (PoolInfo crypto)
genPoolInfo PoolSetUpArgs {poolPledge, poolCost, poolMargin, poolMembers} = do
  pledge <- getOrGen poolPledge $ genCoin 0 maxPoolPledeg
  cost <- getOrGen poolCost $ genCoin 0 maxPoolCost
  margin <- getOrGen poolMargin genMargin
  vrfKey <- vrfKeyPair @(VRF crypto) <$> arbitrary
  coldKey <- keyPair <$> arbitrary
  ownerKey <- keyPair <$> arbitrary
  rewardKey <- keyPair <$> arbitrary
  members' <- getOrGen poolMembers genNonOwnerMembers
  ownerStake <- (pledge <>) <$> genCoin 0 maxOwnerLovelaceAbovePledge
  -- here we are forcing the pool to meet the pledeg, later we may want flexibility
  let members = Map.insert (KeyHashObj . hashKey . vKey $ ownerKey) ownerStake members'
      params =
        PoolParams
          { _poolId = hashKey . vKey $ coldKey,
            _poolVrf = Crypto.hashVerKeyVRF . snd $ vrfKey,
            _poolPledge = pledge,
            _poolCost = cost,
            _poolMargin = margin,
            _poolRAcnt = RewardAcnt Testnet . KeyHashObj . hashKey . vKey $ rewardKey,
            _poolOwners = Set.fromList [hashKey $ vKey ownerKey],
            _poolRelays = StrictSeq.empty,
            _poolMD = SNothing
          }
  pure $ PoolInfo {params, coldKey, ownerKey, ownerStake, rewardKey, members}

genRewardPPs :: Gen (PParams era)
genRewardPPs = do
  d <- g decentralizationRange
  t <- g tauRange
  r <- g rhoRange
  pure $ emptyPParams {_d = d, _tau = t, _rho = r}
  where
    g xs = unsafeBoundRational <$> elements xs

genBlocksMade :: [PoolParams crypto] -> Gen (BlocksMade crypto)
genBlocksMade pools = BlocksMade . Map.fromList <$> mapM f pools
  where
    f p = (_poolId p,) <$> genNatural 0 maxPoolBlocks

-- Properties --

rewardsBoundedByPot :: forall era. Era era => Proxy era -> Property
rewardsBoundedByPot _ = property $ do
  numPools <- choose (0, maxNumPools)
  pools <- sequence $ genPoolInfo @(Crypto era) <$> replicate numPools emptySetupArgs
  pp <- genRewardPPs
  rewardPot <- genCoin 0 (fromIntegral $ maxLovelaceSupply testGlobals)
  undelegatedLovelace <- genCoin 0 (fromIntegral $ maxLovelaceSupply testGlobals)
  asc <- mkActiveSlotCoeff . unsafeBoundRational <$> elements [0.1, 0.2, 0.3]
  bs@(BlocksMade blocks) <- genBlocksMade (fmap params pools)
  let totalBlocks = sum blocks
  silentSlots <- genNatural 0 (3 * totalBlocks) -- the '3 * sum blocks' is pretty arbitrary
  let stake = fold (members <$> pools)
      delegs = fold $
        flip fmap pools $
          \PoolInfo {params, members} ->
            Map.fromList $ (,_poolId params) <$> Map.keys members
      rewardAcnts = Set.fromList $ Map.keys delegs
      poolParams =
        Map.fromList $
          fmap
            ( \PoolInfo {params} ->
                (_poolId params, params)
            )
            pools
      totalLovelace = undelegatedLovelace <> fold stake
      slotsPerEpoch = EpochSize . fromIntegral $ totalBlocks + silentSlots
      (RewardAns rs _) =
        runShelleyBase $
          runProvM $
            reward
              (_d pp, _a0 pp, _nOpt pp, pvMajor (_protocolVersion pp))
              bs
              rewardPot
              rewardAcnts
              poolParams
              (Stake stake)
              delegs
              totalLovelace
              asc
              slotsPerEpoch
  pure $
    counterexample
      ( mconcat
          [ "pp\n",
            show pp,
            "\nrewardPot\n",
            show rewardPot,
            "\nrewardAcnts\n",
            show rewardAcnts,
            "\npoolParams\n",
            show poolParams,
            "\nstake\n",
            show stake,
            "\ndelegs\n",
            show delegs,
            "\ntotalLovelace\n",
            show totalLovelace,
            "\nasc\n",
            show asc,
            "\nslotsPerEpoch\n",
            show slotsPerEpoch
          ]
      )
      (sumRewards pp rs < rewardPot)

-- =================================================
-- tests when running rewards with provenance

rewardsProvenance :: forall era. Era era => Proxy era -> IO String
rewardsProvenance _ = generate $ do
  numPools <- choose (0, maxNumPools)
  pools <- sequence $ genPoolInfo @(Crypto era) <$> replicate numPools emptySetupArgs
  pp <- genRewardPPs
  rewardPot <- genCoin 0 (fromIntegral $ maxLovelaceSupply testGlobals)
  undelegatedLovelace <- genCoin 0 (fromIntegral $ maxLovelaceSupply testGlobals)
  asc <- mkActiveSlotCoeff . unsafeBoundRational <$> elements [0.1, 0.2, 0.3]
  bs@(BlocksMade blocks) <- genBlocksMade (fmap params pools)
  let totalBlocks = sum blocks
  silentSlots <- genNatural 0 (3 * totalBlocks) -- the '3 * sum blocks' is pretty arbitrary
  let stake = fold (members <$> pools)
      delegs = fold $
        flip fmap pools $
          \PoolInfo {params, members} ->
            Map.fromList $ (,_poolId params) <$> Map.keys members
      rewardAcnts = Set.fromList $ Map.keys delegs
      poolParams =
        Map.fromList $
          fmap
            ( \PoolInfo {params} ->
                (_poolId params, params)
            )
            pools
      totalLovelace = undelegatedLovelace <> fold stake
      slotsPerEpoch = EpochSize . fromIntegral $ totalBlocks + silentSlots
      (_, prov) =
        runShelleyBase $
          runWithProvM def $
            reward
              (_d pp, _a0 pp, _nOpt pp, pvMajor (_protocolVersion pp))
              bs
              rewardPot
              rewardAcnts
              poolParams
              (Stake stake)
              delegs
              totalLovelace
              asc
              slotsPerEpoch
  pure (show (snd (Map.findMin prov)))

-- Analog to getRewardInfo, but does not produce Provenance
justRewardInfo ::
  forall era.
  (Core.PParams era ~ PParams era) =>
  Globals ->
  NewEpochState era ->
  RewardUpdate (Crypto era)
justRewardInfo globals newepochstate =
  runReader
    (runProvM $ createRUpd slotsPerEpoch blocksmade epochstate maxsupply asc k)
    globals
  where
    epochstate = nesEs newepochstate
    maxsupply :: Coin
    maxsupply = Coin (fromIntegral (maxLovelaceSupply globals))
    blocksmade :: EB.BlocksMade (Crypto era)
    blocksmade = nesBprev newepochstate
    epochnumber = nesEL newepochstate
    slotsPerEpoch :: EpochSize
    slotsPerEpoch = runReader (epochInfoSize (epochInfo globals) epochnumber) globals
    asc = activeSlotCoeff globals
    k = securityParameter testGlobals

sameWithOrWithoutProvenance ::
  forall era.
  (Core.PParams era ~ PParams era) =>
  Globals ->
  NewEpochState era ->
  Property
sameWithOrWithoutProvenance globals newepochstate = with === without
  where
    (with, _) = getRewardInfo globals newepochstate
    without = justRewardInfo globals newepochstate

nothingInNothingOut ::
  forall era.
  (Core.PParams era ~ PParams era) =>
  NewEpochState era ->
  Property
nothingInNothingOut newepochstate =
  counterexample "nothingInNothingOut fails" $
    runReader
      (preservesNothing $ createRUpd slotsPerEpoch blocksmade epochstate maxsupply asc k)
      globals
  where
    globals = testGlobals
    epochstate = nesEs newepochstate
    maxsupply :: Coin
    maxsupply = Coin (fromIntegral (maxLovelaceSupply globals))
    blocksmade :: EB.BlocksMade (Crypto era)
    blocksmade = nesBprev newepochstate
    epochnumber = nesEL newepochstate
    slotsPerEpoch :: EpochSize
    slotsPerEpoch = runReader (epochInfoSize (epochInfo globals) epochnumber) globals
    asc = activeSlotCoeff globals
    k = securityParameter testGlobals

justInJustOut ::
  forall era.
  (Core.PParams era ~ PParams era) =>
  NewEpochState era ->
  Property
justInJustOut newepochstate =
  counterexample "justInJustOut fails" $
    runReader
      (preservesJust def $ createRUpd slotsPerEpoch blocksmade epochstate maxsupply asc k)
      globals
  where
    globals = testGlobals
    epochstate = nesEs newepochstate
    maxsupply :: Coin
    maxsupply = Coin (fromIntegral (maxLovelaceSupply globals))
    blocksmade :: EB.BlocksMade (Crypto era)
    blocksmade = nesBprev newepochstate
    epochnumber = nesEL newepochstate
    slotsPerEpoch :: EpochSize
    slotsPerEpoch = runReader (epochInfoSize (epochInfo globals) epochnumber) globals
    asc = activeSlotCoeff globals
    k = securityParameter testGlobals

-- ====================================================================================
-- To demonstrate that the code we wrote that enables provenance collection does not
-- change the result of reward calculation. we reproduce the old style functions here.

rewardOnePool ::
  PParams era ->
  Coin ->
  Natural ->
  Natural ->
  PoolParams (Crypto era) ->
  Stake (Crypto era) ->
  Rational ->
  Rational ->
  Coin ->
  Set.Set (Credential 'Staking (Crypto era)) ->
  Map (Credential 'Staking (Crypto era)) Coin
rewardOnePool
  pp
  r
  blocksN
  blocksTotal
  pool
  (Stake stake)
  sigma
  sigmaA
  (Coin totalStake)
  addrsRew =
    rewards'
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
          then maxPool pp r sigma pr
          else mempty
      appPerf = mkApparentPerformance (_d pp) sigmaA blocksN blocksTotal
      poolR = rationalToCoinViaFloor (appPerf * fromIntegral maxP)
      tot = fromIntegral totalStake
      mRewards =
        Map.fromList
          [ ( hk,
              memberRew
                poolR
                pool
                (StakeShare (fromIntegral c % tot))
                (StakeShare sigma)
            )
            | (hk, Coin c) <- Map.toList stake,
              notPoolOwner hk
          ]
      notPoolOwner (KeyHashObj hk) = hk `Set.notMember` _poolOwners pool
      notPoolOwner (ScriptHashObj _) = False
      lReward =
        leaderRew
          poolR
          pool
          (StakeShare $ fromIntegral ostake % tot)
          (StakeShare sigma)
      f =
        if HardForks.aggregatedRewards pp
          then Map.insertWith (<>)
          else Map.insert
      potentialRewards =
        f (getRwdCred $ _poolRAcnt pool) lReward mRewards
      rewards' = Map.filter (/= Coin 0) $ (eval (addrsRew ◁ potentialRewards))

rewardOld ::
  forall era.
  PParams era ->
  BlocksMade (Crypto era) ->
  Coin ->
  Set.Set (Credential 'Staking (Crypto era)) ->
  Map (KeyHash 'StakePool (Crypto era)) (PoolParams (Crypto era)) ->
  Stake (Crypto era) ->
  Map (Credential 'Staking (Crypto era)) (KeyHash 'StakePool (Crypto era)) ->
  Coin ->
  ActiveSlotCoeff ->
  EpochSize ->
  ( Map
      (Credential 'Staking (Crypto era))
      Coin,
    Map (KeyHash 'StakePool (Crypto era)) Likelihood
  )
rewardOld
  pp
  (BlocksMade b)
  r
  addrsRew
  poolParams
  stake
  delegs
  (Coin totalStake)
  asc
  slotsPerEpoch = (rewards', hs)
    where
      totalBlocks = sum b
      Coin activeStake = fold . unStake $ stake
      results :: [(KeyHash 'StakePool (Crypto era), Maybe (Map (Credential 'Staking (Crypto era)) Coin), Likelihood)]
      results = do
        (hk, pparams) <- Map.toList poolParams
        let sigma = if totalStake == 0 then 0 else fromIntegral pstake % fromIntegral totalStake
            sigmaA = if activeStake == 0 then 0 else fromIntegral pstake % fromIntegral activeStake
            blocksProduced = Map.lookup hk b
            actgr@(Stake s) = poolStake hk delegs stake
            Coin pstake = fold s
            rewardMap = case blocksProduced of
              Nothing -> Nothing -- This is equivalent to calling rewarOnePool with n = 0
              Just n ->
                Just $
                  rewardOnePool
                    pp
                    r
                    n
                    totalBlocks
                    pparams
                    actgr
                    sigma
                    sigmaA
                    (Coin totalStake)
                    addrsRew
            ls =
              likelihood
                (fromMaybe 0 blocksProduced)
                (leaderProbability asc sigma (_d pp))
                slotsPerEpoch
        pure (hk, rewardMap, ls)
      f =
        if HardForks.aggregatedRewards pp
          then Map.unionsWith (<>)
          else Map.unions
      rewards' = f . catMaybes $ fmap (\(_, x, _) -> x) results
      hs = Map.fromList $ fmap (\(hk, _, l) -> (hk, l)) results

data RewardUpdateOld crypto = RewardUpdateOld
  { deltaTOld :: !DeltaCoin,
    deltaROld :: !DeltaCoin,
    rsOld :: !(Map (Credential 'Staking crypto) Coin),
    deltaFOld :: !DeltaCoin,
    nonMyopicOld :: !(NonMyopic crypto)
  }
  deriving (Show, Eq)

createRUpdOld ::
  forall era.
  (Core.PParams era ~ PParams era) =>
  EpochSize ->
  BlocksMade (Crypto era) ->
  EpochState era ->
  Coin ->
  ShelleyBase (RewardUpdateOld (Crypto era))
createRUpdOld slotsPerEpoch b@(BlocksMade b') es@(EpochState acnt ss ls pr _ nm) maxSupply = do
  asc <- asks activeSlotCoeff
  let SnapShot stake' delegs' poolParams = _pstakeGo ss
      Coin reserves = _reserves acnt
      ds = _dstate $ _delegationState ls
      -- reserves and rewards change
      deltaR1 =
        ( rationalToCoinViaFloor $
            min 1 eta
              * unboundRational (_rho pr)
              * fromIntegral reserves
        )
      d = unboundRational (_d pr)
      expectedBlocks =
        floor $
          (1 - d) * unboundRational (activeSlotVal asc) * fromIntegral slotsPerEpoch
      -- TODO asc is a global constant, and slotsPerEpoch should not change often at all,
      -- it would be nice to not have to compute expectedBlocks every epoch
      eta
        | unboundRational (_d pr) >= 0.8 = 1
        | otherwise = blocksMade % expectedBlocks
      Coin rPot = _feeSS ss <> deltaR1
      deltaT1 = floor $ unboundRational (_tau pr) * fromIntegral rPot
      _R = Coin $ rPot - deltaT1
      totalStake = circulation es maxSupply
      (rs_, newLikelihoods) =
        rewardOld
          pr
          b
          _R
          (Map.keysSet $ _rewards ds)
          poolParams
          stake'
          delegs'
          totalStake
          asc
          slotsPerEpoch
      deltaR2 = _R <-> (Map.foldr (<+>) mempty rs_)
      blocksMade = fromIntegral $ Map.foldr (+) 0 b' :: Integer
  pure $
    RewardUpdateOld
      { deltaTOld = (DeltaCoin deltaT1),
        deltaROld = ((invert $ toDeltaCoin deltaR1) <> toDeltaCoin deltaR2),
        rsOld = rs_,
        deltaFOld = (invert (toDeltaCoin $ _feeSS ss)),
        nonMyopicOld = (updateNonMyopic nm _R newLikelihoods)
      }

oldEqualsNew ::
  forall era.
  ( era ~ C,
    Core.PParams era ~ PParams era
  ) =>
  NewEpochState era ->
  Property
oldEqualsNew newepochstate = counterexample (show (prettyA newepochstate) ++ "\n new = " ++ show new ++ "\n old = " ++ show old) (old === new)
  where
    globals = testGlobals
    epochstate = nesEs newepochstate
    maxsupply :: Coin
    maxsupply = Coin (fromIntegral (maxLovelaceSupply globals))
    blocksmade :: EB.BlocksMade (Crypto era)
    blocksmade = nesBprev newepochstate
    epochnumber = nesEL newepochstate
    slotsPerEpoch :: EpochSize
    slotsPerEpoch = runReader (epochInfoSize (epochInfo globals) epochnumber) globals
    unAggregated = runReader (runProvM $ createRUpd slotsPerEpoch blocksmade epochstate maxsupply asc k) globals
    old :: Map (Credential 'Staking (Crypto era)) Coin
    old = rsOld $ runReader (createRUpdOld slotsPerEpoch blocksmade epochstate maxsupply) globals
    new_with_zeros = aggregateRewards @(Crypto era) (emptyPParams {_protocolVersion = ProtVer 2 0}) (rs unAggregated)
    new = Map.filter (/= Coin 0) new_with_zeros
    asc = activeSlotCoeff globals
    k = securityParameter testGlobals

oldEqualsNewOn :: forall era. (Core.PParams era ~ PParams era) => NewEpochState era -> Property
oldEqualsNewOn newepochstate = old === new
  where
    globals = testGlobals
    epochstate = nesEs newepochstate
    maxsupply :: Coin
    maxsupply = Coin (fromIntegral (maxLovelaceSupply globals))
    blocksmade :: EB.BlocksMade (Crypto era)
    blocksmade = nesBprev newepochstate
    epochnumber = nesEL newepochstate
    slotsPerEpoch :: EpochSize
    slotsPerEpoch = runReader (epochInfoSize (epochInfo globals) epochnumber) globals
    (unAggregated, _) = runReader (runWithProvM def $ createRUpd slotsPerEpoch blocksmade epochstate maxsupply asc k) globals
    old :: Map (Credential 'Staking (Crypto era)) Coin
    old = rsOld $ runReader (createRUpdOld slotsPerEpoch blocksmade epochstate maxsupply) globals
    new_with_zeros = aggregateRewards @(Crypto era) (emptyPParams {_protocolVersion = ProtVer 2 0}) (rs unAggregated)
    new = Map.filter (/= Coin 0) new_with_zeros
    asc = activeSlotCoeff globals
    k = securityParameter testGlobals

lastElem :: [a] -> Maybe a
lastElem [a] = Just a
lastElem [] = Nothing
lastElem (_ : xs) = lastElem xs

-- | Provide a legitimate NewEpochState to make an test Property
newEpochProp :: Word64 -> (NewEpochState C -> Property) -> Property
newEpochProp tracelen propf = withMaxSuccess 100 $
  forAllChainTrace @C tracelen $ \tr ->
    case (lastElem (sourceSignalTargets tr)) of
      Just (SourceSignalTarget {target}) -> propf (chainNes target)
      _ -> True === True

-- ================================================================

reward ::
  forall crypto.
  (UnitInterval, NonNegativeInterval, Natural, Natural) ->
  BlocksMade crypto ->
  Coin ->
  Set (Credential 'Staking crypto) ->
  Map (KeyHash 'StakePool crypto) (PoolParams crypto) ->
  Stake crypto ->
  Map (Credential 'Staking crypto) (KeyHash 'StakePool crypto) ->
  Coin ->
  ActiveSlotCoeff ->
  EpochSize ->
  ProvM (KeyHashPoolProvenance crypto) ShelleyBase (RewardAns crypto)
reward pp bm r addrsRew poolParams stake delegs tot asc slotsPerEpoch =
  completeM (rewardPulser pp bm r addrsRew poolParams stake delegs tot asc slotsPerEpoch)

rewardPulser ::
  forall c.
  (UnitInterval, NonNegativeInterval, Natural, Natural) ->
  BlocksMade c ->
  Coin ->
  Set (Credential 'Staking c) ->
  Map (KeyHash 'StakePool c) (PoolParams c) ->
  Stake c ->
  Map (Credential 'Staking c) (KeyHash 'StakePool c) ->
  Coin ->
  ActiveSlotCoeff ->
  EpochSize ->
  Pulser c
rewardPulser
  (pp_d, pp_a0, pp_nOpt, pp_mv)
  (BlocksMade b)
  r
  addrsRew
  poolParams
  stake
  delegs
  (Coin totalStake)
  asc
  slotsPerEpoch = pulser
    where
      totalBlocks = sum b
      Coin activeStake = fold . unStake $ stake
      free = (FreeVars b delegs stake addrsRew totalStake activeStake asc totalBlocks r slotsPerEpoch pp_d pp_a0 pp_nOpt pp_mv)
      pulser :: Pulser c
      pulser = RSLP 2 free (StrictSeq.fromList $ Map.elems poolParams) (RewardAns Map.empty Map.empty)

-- ==================================================================

chainlen :: Word64
chainlen = 20 -- 50 -- 43 -- 37 -- 25 -- 50 -- 100

rewardTests :: TestTree
rewardTests =
  testGroup
    "Reward Tests"
    [ testProperty "Sum of rewards is bounded by reward pot" (withMaxSuccess numberOfTests (rewardsBoundedByPot (Proxy @C))),
      testProperty "provenance does not affect result" (newEpochProp 100 (sameWithOrWithoutProvenance @C testGlobals)),
      testProperty "ProvM preserves Nothing" (newEpochProp 100 (nothingInNothingOut @C)),
      testProperty "ProvM preserves Just" (newEpochProp 100 (justInJustOut @C)),
      testProperty "oldstyle (aggregate immediately) matches newstyle (late aggregation) with provenance off style" (newEpochProp chainlen (oldEqualsNew @C)),
      testProperty "oldstyle (aggregate immediately) matches newstyle (late aggregation) with provenance on style" (newEpochProp chainlen (oldEqualsNewOn @C)),
      testCaseInfo "Reward Provenance works" (rewardsProvenance (Proxy @C))
    ]
