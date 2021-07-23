{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.API.Wallet
  ( getNonMyopicMemberRewards,
    getUTxO,
    getUTxOSubset,
    getFilteredUTxO,
    getLeaderSchedule,
    getPools,
    getPoolParameters,
    getTotalStake,
    poolsByTotalStakeFraction,
    getRewardInfo,
    CLI (..),
    addShelleyKeyWitnesses,
  )
where

import Cardano.Binary (ToCBOR (..), decodeFull, decodeFullDecoder, serialize)
import Cardano.Crypto.DSIGN.Class (decodeSignedDSIGN, sizeSigDSIGN, sizeVerKeyDSIGN)
import qualified Cardano.Crypto.VRF as VRF
import Cardano.Ledger.Address (Addr (..))
import Cardano.Ledger.BaseTypes (Globals (..), NonNegativeInterval, Seed, UnitInterval, epochInfo)
import Cardano.Ledger.Coin (Coin (..))
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential (Credential (..))
import Cardano.Ledger.Crypto (DSIGN, VRF)
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Keys (KeyHash, KeyRole (..), SignKeyVRF)
import Cardano.Ledger.Shelley (ShelleyEra)
import Cardano.Ledger.Shelley.Constraints (UsesValue)
import Cardano.Ledger.Slot (epochInfoSize)
import Cardano.Ledger.Val ((<->))
import Cardano.Slotting.EpochInfo (epochInfoRange)
import Cardano.Slotting.Slot (EpochSize, SlotNo)
import Control.Monad.Trans.Reader (runReader)
import Control.Provenance (runWithProvM)
import qualified Data.ByteString.Lazy as LBS
import Data.Default.Class (Default (..))
import Data.Either (fromRight)
import Data.Foldable (fold)
import Data.Functor.Identity (runIdentity)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Ratio ((%))
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Records (HasField (..), getField)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.API.Protocol (ChainDepState (..))
import Shelley.Spec.Ledger.BlockChain (checkLeaderValue, mkSeed, seedL)
import Shelley.Spec.Ledger.CompactAddr (CompactAddr, compactAddr)
import Shelley.Spec.Ledger.Delegation.Certificates
  ( IndividualPoolStake (..),
    PoolDistr (..),
  )
import qualified Shelley.Spec.Ledger.EpochBoundary as EB
import Shelley.Spec.Ledger.LedgerState
  ( DPState (..),
    EpochState (..),
    LedgerState (..),
    NewEpochState (..),
    PState (..),
    RewardUpdate,
    UTxOState (..),
    circulation,
    consumed,
    createRUpd,
    minfee,
    produced,
    stakeDistr,
  )
import Shelley.Spec.Ledger.OverlaySchedule (isOverlaySlot)
import Shelley.Spec.Ledger.PParams (PParams, PParams' (..), ProtVer)
import Shelley.Spec.Ledger.RewardProvenance (RewardProvenance)
import Shelley.Spec.Ledger.Rewards
  ( NonMyopic (..),
    StakeShare (..),
    getTopRankedPools,
    nonMyopicMemberRew,
    percentile',
  )
import Shelley.Spec.Ledger.STS.NewEpoch (calculatePoolDistr)
import Shelley.Spec.Ledger.STS.Tickn (TicknState (..))
import Shelley.Spec.Ledger.Tx (Tx (..), WitnessSet, WitnessSetHKD (..))
import Shelley.Spec.Ledger.TxBody (DCert, PoolParams (..), TxIn (..), WitVKey (..))
import Shelley.Spec.Ledger.UTxO (UTxO (..))

-- | Get pool sizes, but in terms of total stake
--
-- The stake distribution uses active stake (so that the leader schedule is not
-- affected by undelegated stake), but the wallet wants to display pool
-- saturation for rewards purposes. For that, it needs the fraction of total
-- stake.
--
-- This is not based on any snapshot, but uses the current ledger state.
poolsByTotalStakeFraction ::
  forall era.
  UsesValue era =>
  Globals ->
  NewEpochState era ->
  PoolDistr (Crypto era)
poolsByTotalStakeFraction globals ss =
  PoolDistr poolsByTotalStake
  where
    snap@(EB.SnapShot stake _ _) = currentSnapshot ss
    Coin totalStake = getTotalStake globals ss
    Coin activeStake = fold . EB.unStake $ stake
    stakeRatio = activeStake % totalStake
    PoolDistr poolsByActiveStake = calculatePoolDistr snap
    poolsByTotalStake = Map.map toTotalStakeFrac poolsByActiveStake
    toTotalStakeFrac ::
      IndividualPoolStake (Crypto era) ->
      IndividualPoolStake (Crypto era)
    toTotalStakeFrac (IndividualPoolStake s vrf) =
      IndividualPoolStake (s * stakeRatio) vrf

-- | Calculate the current total stake.
getTotalStake :: Globals -> NewEpochState era -> Coin
getTotalStake globals ss =
  let supply = Coin . fromIntegral $ maxLovelaceSupply globals
      es = nesEs ss
   in circulation es supply

-- | Calculate the Non-Myopic Pool Member Rewards for a set of credentials.
-- For each given credential, this function returns a map from each stake
-- pool (identified by the key hash of the pool operator) to the
-- non-myopic pool member reward for that stake pool.
--
-- This is not based on any snapshot, but uses the current ledger state.
getNonMyopicMemberRewards ::
  ( UsesValue era,
    HasField "_a0" (Core.PParams era) NonNegativeInterval,
    HasField "_nOpt" (Core.PParams era) Natural
  ) =>
  Globals ->
  NewEpochState era ->
  Set (Either Coin (Credential 'Staking (Crypto era))) ->
  Map
    (Either Coin (Credential 'Staking (Crypto era)))
    (Map (KeyHash 'StakePool (Crypto era)) Coin)
getNonMyopicMemberRewards globals ss creds =
  Map.fromList $
    fmap
      (\cred -> (cred, Map.map (mkNMMRewards $ memShare cred) poolData))
      (Set.toList creds)
  where
    maxSupply = Coin . fromIntegral $ maxLovelaceSupply globals
    Coin totalStake = circulation es maxSupply
    toShare (Coin x) = StakeShare (x % totalStake)
    memShare (Right cred) =
      toShare $
        Map.findWithDefault (Coin 0) cred (EB.unStake stake)
    memShare (Left coin) = toShare coin
    es = nesEs ss
    pp = esPp es
    NonMyopic
      { likelihoodsNM = ls,
        rewardPotNM = rPot
      } = esNonMyopic es
    EB.SnapShot stake delegs poolParams = currentSnapshot ss
    poolData =
      Map.mapWithKey
        ( \k p ->
            ( percentile' (histLookup k),
              p,
              toShare . fold
                . EB.unStake
                $ EB.poolStake k delegs stake
            )
        )
        poolParams
    histLookup k = fromMaybe mempty (Map.lookup k ls)
    topPools =
      getTopRankedPools
        rPot
        (Coin totalStake)
        pp
        poolParams
        (fmap percentile' ls)
    mkNMMRewards t (hitRateEst, poolp, sigma) =
      if checkPledge poolp
        then nonMyopicMemberRew pp rPot poolp s sigma t topPools hitRateEst
        else mempty
      where
        s = (toShare . _poolPledge) poolp
        checkPledge pool =
          let ostake =
                Set.foldl'
                  ( \c o ->
                      c
                        <> fromMaybe
                          mempty
                          ( Map.lookup (KeyHashObj o) (EB.unStake stake)
                          )
                  )
                  mempty
                  (_poolOwners pool)
           in _poolPledge poolp <= ostake

-- | Create a current snapshot of the ledger state.
--
-- When ranking pools, and reporting their saturation level, in the wallet, we
-- do not want to use one of the regular snapshots, but rather the most recent
-- ledger state.
currentSnapshot ::
  UsesValue era =>
  NewEpochState era ->
  EB.SnapShot (Crypto era)
currentSnapshot ss =
  stakeDistr utxo dstate pstate
  where
    es = nesEs ss
    utxo = _utxo . _utxoState . esLState $ es
    dstate = _dstate . _delegationState . esLState $ es
    pstate = _pstate . _delegationState . esLState $ es

-- | Get the full UTxO.
getUTxO ::
  NewEpochState era ->
  UTxO era
getUTxO = _utxo . _utxoState . esLState . nesEs

-- | Get the UTxO filtered by address.
getFilteredUTxO ::
  HasField "compactAddress" (Core.TxOut era) (CompactAddr (Crypto era)) =>
  NewEpochState era ->
  Set (Addr (Crypto era)) ->
  UTxO era
getFilteredUTxO ss addrs =
  UTxO $
    Map.filter
      (\out -> getField @"compactAddress" out `Set.member` addrSBSs)
      fullUTxO
  where
    UTxO fullUTxO = getUTxO ss
    -- Instead of decompacting each address in the huge UTxO, compact each
    -- address in the small set of address.
    addrSBSs = Set.map compactAddr addrs

getUTxOSubset ::
  NewEpochState era ->
  Set (TxIn (Crypto era)) ->
  UTxO era
getUTxOSubset ss txins =
  UTxO $
    fullUTxO `Map.restrictKeys` txins
  where
    UTxO fullUTxO = getUTxO ss

-- | Get the (private) leader schedule for this epoch.
--
--   Given a private VRF key, returns the set of slots in which this node is
--   eligible to lead.
getLeaderSchedule ::
  ( Era era,
    VRF.Signable
      (VRF (Crypto era))
      Seed
  ) =>
  Globals ->
  NewEpochState era ->
  ChainDepState (Crypto era) ->
  KeyHash 'StakePool (Crypto era) ->
  SignKeyVRF (Crypto era) ->
  PParams era ->
  Set SlotNo
getLeaderSchedule globals ss cds poolHash key pp = Set.filter isLeader epochSlots
  where
    isLeader slotNo =
      let y = VRF.evalCertified () (mkSeed seedL slotNo epochNonce) key
       in not (isOverlaySlot a (_d pp) slotNo)
            && checkLeaderValue (VRF.certifiedOutput y) stake f
    stake = maybe 0 individualPoolStake $ Map.lookup poolHash poolDistr
    poolDistr = unPoolDistr $ nesPd ss
    TicknState epochNonce _ = csTickn cds
    currentEpoch = nesEL ss
    ei = epochInfo globals
    f = activeSlotCoeff globals
    epochSlots = Set.fromList [a .. b]
    (a, b) = runIdentity $ epochInfoRange ei currentEpoch

-- | Get the /current/ registered stake pool parameters for a given set of
-- stake pools. The result map will contain entries for all the given stake
-- pools that are currently registered.
getPools ::
  NewEpochState era ->
  Set (KeyHash 'StakePool (Crypto era))
getPools = Map.keysSet . f
  where
    f = _pParams . _pstate . _delegationState . esLState . nesEs

-- | Get the /current/ registered stake pool parameters for a given set of
-- stake pools. The result map will contain entries for all the given stake
-- pools that are currently registered.
getPoolParameters ::
  NewEpochState era ->
  Set (KeyHash 'StakePool (Crypto era)) ->
  Map (KeyHash 'StakePool (Crypto era)) (PoolParams (Crypto era))
getPoolParameters = Map.restrictKeys . f
  where
    f = _pParams . _pstate . _delegationState . esLState . nesEs

getRewardInfo ::
  forall era.
  ( HasField "_a0" (Core.PParams era) NonNegativeInterval,
    HasField "_d" (Core.PParams era) UnitInterval,
    HasField "_nOpt" (Core.PParams era) Natural,
    HasField "_protocolVersion" (Core.PParams era) ProtVer,
    HasField "_rho" (Core.PParams era) UnitInterval,
    HasField "_tau" (Core.PParams era) UnitInterval
  ) =>
  Globals ->
  NewEpochState era ->
  (RewardUpdate (Crypto era), RewardProvenance (Crypto era))
getRewardInfo globals newepochstate =
  runReader
    ( runWithProvM def $
        createRUpd slotsPerEpoch blocksmade epochstate maxsupply asc secparam
    )
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
    secparam = securityParameter globals

-- | A collection of functons to help construction transactions
--  from the cardano-cli.
class
  ( Era era,
    HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era)))
  ) =>
  CLI era
  where
  -- | The minimum fee calculation.
  -- Used for the default implentation of 'evaluateTransactionFee'.
  evaluateMinFee :: Core.PParams era -> Core.Tx era -> Coin

  -- | The consumed calculation.
  -- Used for the default implentation of 'evaluateTransactionBalance'.
  evaluateConsumed :: Core.PParams era -> UTxO era -> Core.TxBody era -> Core.Value era

  addKeyWitnesses :: Core.Tx era -> Set (WitVKey 'Witness (Crypto era)) -> Core.Tx era

  -- | Evaluate the difference between the value currently being consumed by
  -- a transaction and the number of lovelace being produced.
  -- This value will be zero for a valid transaction.
  evaluateTransactionBalance ::
    -- | The current protocol parameters.
    Core.PParams era ->
    -- | The UTxO relevant to the transaction.
    UTxO era ->
    -- | A predicate that a stake pool ID is new (i.e. unregistered).
    -- Typically this will be:
    --
    -- @
    --   (`Map.notMember` stakepools)
    -- @
    (KeyHash 'StakePool (Crypto era) -> Bool) ->
    -- | The transaction being evaluated for balance.
    Core.TxBody era ->
    -- | The difference between what the transaction consumes and what it produces.
    Core.Value era
  evaluateTransactionBalance pp u isNewPool txb =
    evaluateConsumed pp u txb <-> produced @era pp isNewPool txb

  -- | Evaluate the fee for a given transaction.
  evaluateTransactionFee ::
    -- | The current protocol parameters.
    Core.PParams era ->
    -- | The transaction.
    Core.Tx era ->
    -- | The number of key witnesses still be be added to the transaction.
    Word ->
    -- | The required fee.
    Coin
  evaluateTransactionFee pp tx numKeyWits =
    evaluateMinFee @era pp tx'
    where
      sigSize = fromIntegral $ sizeSigDSIGN (Proxy @(DSIGN (Crypto era)))
      dummySig =
        fromRight
          (error "corrupt dummy signature")
          (decodeFullDecoder "dummy signature" decodeSignedDSIGN (serialize $ LBS.replicate sigSize 0))
      vkeySize = fromIntegral $ sizeVerKeyDSIGN (Proxy @(DSIGN (Crypto era)))
      dummyVKey w =
        let padding = LBS.replicate paddingSize 0
            paddingSize = vkeySize - LBS.length sw
            sw = serialize w
            keyBytes = serialize $ padding <> sw
         in fromRight (error "corrupt dummy vkey") (decodeFull keyBytes)
      dummyKeyWits = Set.fromList $
        flip map [1 .. numKeyWits] $
          \x -> WitVKey (dummyVKey x) dummySig

      tx' = addKeyWitnesses @era tx dummyKeyWits

  -- | Evaluate the minimum lovelace that a given transaciton output must contain.
  evaluateMinLovelaceOutput :: Core.PParams era -> Core.TxOut era -> Coin

--------------------------------------------------------------------------------
-- Shelley specifics
--------------------------------------------------------------------------------

addShelleyKeyWitnesses ::
  ( Era era,
    Core.Witnesses era ~ WitnessSet era,
    Core.AnnotatedData (Core.Script era),
    ToCBOR (Core.AuxiliaryData era),
    ToCBOR (Core.TxBody era)
  ) =>
  Tx era ->
  Set (WitVKey 'Witness (Crypto era)) ->
  Tx era
addShelleyKeyWitnesses (Tx b ws aux) newWits = Tx b ws' aux
  where
    ws' = ws {addrWits = Set.union newWits (addrWits ws)}

instance CC.Crypto c => CLI (ShelleyEra c) where
  evaluateMinFee = minfee

  evaluateConsumed = consumed

  addKeyWitnesses = addShelleyKeyWitnesses

  evaluateMinLovelaceOutput pp _out = _minUTxOValue pp
