{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : LedgerState
-- Description : Operational Rules
--
-- This module implements the operation rules for treating UTxO transactions ('Tx')
-- as state transformations on a ledger state ('LedgerState'),
-- as specified in /A Simplified Formal Specification of a UTxO Ledger/.
module Shelley.Spec.Ledger.LedgerState
  ( AccountState (..),
    DPState (..),
    DState (..),
    EpochState (..),
    UpecState (..),
    PulsingRewUpdate (..),
    FutureGenDeleg (..),
    InstantaneousRewards (..),
    Ix,
    KeyPairs,
    LedgerState (..),
    PPUPState (..),
    PState (..),
    RewardAccounts,
    RewardUpdate (..),
    RewardSnapShot (..),
    UTxOState (..),
    depositPoolChange,
    emptyRewardUpdate,
    pvCanFollow,
    reapRewards,
    availableAfterMIR,

    -- * Genesis State
    genesisState,

    -- * Validation
    WitHashes (..),
    nullWitHashes,
    diffWitHashes,
    minfee,
    txsizeBound,
    produced,
    consumed,
    verifiedWits,
    witsVKeyNeeded,
    witsFromTxWitnesses,
    propWits,

    -- * DelegationState
    keyRefunds,

    -- * Epoch boundary
    stakeDistr,
    makePulsingStakeDistr,
    applyRUpd,
    createRUpd,
    completeRupd,
    startStep,
    pulseStep,
    completeStep,
    pulseOther,
    --
    NewEpochState (..),
    getGKeys,
    updateNES,
    circulation,

    -- * Decay
    decayFactor,

    -- * Remove Bootstrap Redeem Addresses
    returnRedeemAddrsToReserves,
    updateNonMyopic,

    -- *
    TransUTxOState,
    TransLedgerState,
  )
where

import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    encodeListLen,
  )
import Cardano.Ledger.Address (Addr (..), bootstrapKeyHash, isBootstrapRedeemer)
import Cardano.Ledger.BaseTypes
  ( ActiveSlotCoeff,
    BoundedRational (..),
    NonNegativeInterval,
    ShelleyBase,
    StrictMaybe (..),
    UnitInterval,
    activeSlotVal,
    strictMaybeToMaybe,
  )
import Cardano.Ledger.Coin
  ( Coin (..),
    DeltaCoin (..),
    addDeltaCoin,
    rationalToCoinViaFloor,
    toDeltaCoin,
  )
import Cardano.Ledger.Compactible
import Cardano.Ledger.Core (PParamsDelta)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential (Credential (..))
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Keys
  ( DSignable,
    GenDelegPair (..),
    GenDelegs (..),
    Hash,
    KeyHash (..),
    KeyPair,
    KeyRole (..),
    VKey,
    asWitness,
  )
import Cardano.Ledger.SafeHash (HashAnnotated, extractHash, hashAnnotated)
import Cardano.Ledger.Serialization (mapFromCBOR, mapToCBOR)
import Cardano.Ledger.Shelley.Constraints (TransValue)
import Cardano.Ledger.Slot
  ( EpochNo (..),
    EpochSize (..),
    SlotNo (..),
  )
import Cardano.Ledger.Val ((<+>), (<->), (<×>))
import qualified Cardano.Ledger.Val as Val
import Control.DeepSeq (NFData)
import Control.Provenance (ProvM, liftProv)
import Control.SetAlgebra (Bimap, biMapEmpty, dom, eval, forwards, (∈), (∪+), (▷), (◁))
import Control.State.Transition (STS (State))
import Data.Coders
  ( Decode (From, RecD),
    decode,
    decodeRecordNamed,
    (<!),
  )
import Data.Constraint (Constraint)
import Data.Default.Class (Default, def)
import Data.Foldable (fold, toList)
import Data.Group (invert)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Pulse (Pulsable (..), completeM)
import Data.Ratio ((%))
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import Data.Word (Word64)
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import NoThunks.Class (NoThunks (..))
import Numeric.Natural (Natural)
import Quiet
import Shelley.Spec.Ledger.Address.Bootstrap
  ( BootstrapWitness (..),
    bootstrapWitKeyHash,
    verifyBootstrapWit,
  )
import Shelley.Spec.Ledger.Delegation.Certificates
  ( DCert (..),
    PoolDistr (..),
    delegCWitness,
    genesisCWitness,
    isDeRegKey,
    poolCWitness,
    requiresVKeyWitness,
  )
import Shelley.Spec.Ledger.EpochBoundary
  ( BlocksMade (..),
    PulsingStakeDistr (..),
    SnapShot (..),
    SnapShots (..),
    Stake (..),
    StakeDistrPulser (..),
    aggregateUtxoCoinByCredential,
  )
import Shelley.Spec.Ledger.PParams
  ( PParams,
    PParams' (..),
    ProposedPPUpdates (..),
    ProtVer (..),
    Update (..),
    emptyPPPUpdates,
  )
import Shelley.Spec.Ledger.RewardProvenance (Desirability (..), RewardProvenance (..))
import Shelley.Spec.Ledger.RewardUpdate
  ( FreeVars (..),
    Pulser,
    PulsingRewUpdate (..),
    RewardAns (..),
    RewardPulser (..),
    RewardSnapShot (..),
    RewardUpdate (..),
    emptyRewardUpdate,
    pulseOther,
  )
import Shelley.Spec.Ledger.Rewards
  ( Likelihood (..),
    NonMyopic (..),
    PerformanceEstimate (..),
    aggregateRewards,
    applyDecay,
    desirability,
    percentile',
    sumRewards,
  )
import Shelley.Spec.Ledger.Tx
  ( Tx (..),
    extractKeyHashWitnessSet,
  )
import Shelley.Spec.Ledger.TxBody
  ( EraIndependentTxBody,
    Ix,
    MIRPot (..),
    PoolCert (..),
    PoolParams (..),
    Ptr (..),
    RewardAcnt (..),
    TransTxId,
    TxIn (..),
    Wdrl (..),
    WitVKey (..),
    getRwdCred,
    witKeyHash,
  )
import Shelley.Spec.Ledger.UTxO
  ( UTxO (..),
    balance,
    totalDeposits,
    txinLookup,
    txins,
    txouts,
    verifyWitVKey,
  )

-- | Representation of a list of pairs of key pairs, e.g., pay and stake keys
type KeyPairs crypto = [(KeyPair 'Payment crypto, KeyPair 'Staking crypto)]

type RewardAccounts crypto =
  Map (Credential 'Staking crypto) Coin

data FutureGenDeleg crypto = FutureGenDeleg
  { fGenDelegSlot :: !SlotNo,
    fGenDelegGenKeyHash :: !(KeyHash 'Genesis crypto)
  }
  deriving (Show, Eq, Ord, Generic)

instance NoThunks (FutureGenDeleg crypto)

instance NFData (FutureGenDeleg crypto)

instance CC.Crypto crypto => ToCBOR (FutureGenDeleg crypto) where
  toCBOR (FutureGenDeleg a b) =
    encodeListLen 2 <> toCBOR a <> toCBOR b

instance CC.Crypto crypto => FromCBOR (FutureGenDeleg crypto) where
  fromCBOR = do
    decodeRecordNamed "FutureGenDeleg" (const 2) $ do
      a <- fromCBOR
      b <- fromCBOR
      pure $ FutureGenDeleg a b

-- | InstantaneousRewards captures the pending changes to the ledger
-- state caused by MIR certificates. It consists of two mappings,
-- the rewards which will be paid out from the reserves and the rewards
-- which will be paid out from the treasury. It also consists of
-- two coin values which represent the transfer of coins from
-- one pot the the other pot.
-- NOTE that the following property should always hold:
--   deltaReserves + deltaTreasury = 0
data InstantaneousRewards crypto = InstantaneousRewards
  { iRReserves :: !(Map (Credential 'Staking crypto) Coin),
    iRTreasury :: !(Map (Credential 'Staking crypto) Coin),
    deltaReserves :: DeltaCoin,
    deltaTreasury :: DeltaCoin
  }
  deriving (Show, Eq, Generic)

-- | This function returns the coin balance of a given pot, either the
-- reserves or the treasury, after the instantaneous rewards and pot
-- transfers are accounted for.
availableAfterMIR :: MIRPot -> AccountState -> InstantaneousRewards crypto -> Coin
availableAfterMIR ReservesMIR as ir =
  _reserves as `addDeltaCoin` (deltaReserves ir) <-> (fold $ iRReserves ir)
availableAfterMIR TreasuryMIR as ir =
  _treasury as `addDeltaCoin` (deltaTreasury ir) <-> (fold $ iRTreasury ir)

instance NoThunks (InstantaneousRewards crypto)

instance NFData (InstantaneousRewards crypto)

instance
  CC.Crypto crypto =>
  ToCBOR (InstantaneousRewards crypto)
  where
  toCBOR (InstantaneousRewards irR irT dR dT) =
    encodeListLen 4 <> mapToCBOR irR <> mapToCBOR irT <> toCBOR dR <> toCBOR dT

instance
  CC.Crypto crypto =>
  FromCBOR (InstantaneousRewards crypto)
  where
  fromCBOR = do
    decodeRecordNamed "InstantaneousRewards" (const 4) $ do
      irR <- mapFromCBOR
      irT <- mapFromCBOR
      dR <- fromCBOR
      dT <- fromCBOR
      pure $ InstantaneousRewards irR irT dR dT

-- | State of staking pool delegations and rewards
data DState crypto = DState
  { -- | The active reward accounts.
    _rewards :: !(RewardAccounts crypto),
    -- | The current delegations.
    _delegations :: !(Map (Credential 'Staking crypto) (KeyHash 'StakePool crypto)),
    -- | The pointed to hash keys.
    _ptrs :: !(Bimap Ptr (Credential 'Staking crypto)),
    -- | future genesis key delegations
    _fGenDelegs :: !(Map (FutureGenDeleg crypto) (GenDelegPair crypto)),
    -- | Genesis key delegations
    _genDelegs :: !(GenDelegs crypto),
    -- | Instantaneous Rewards
    _irwd :: !(InstantaneousRewards crypto)
  }
  deriving (Show, Eq, Generic)

instance NoThunks (DState crypto)

instance NFData (DState crypto)

instance
  CC.Crypto crypto =>
  ToCBOR (DState crypto)
  where
  toCBOR (DState rw dlg p fgs gs ir) =
    encodeListLen 6
      <> toCBOR rw
      <> toCBOR dlg
      <> toCBOR p
      <> toCBOR fgs
      <> toCBOR gs
      <> toCBOR ir

instance
  CC.Crypto crypto =>
  FromCBOR (DState crypto)
  where
  fromCBOR = do
    decodeRecordNamed "DState" (const 6) $ do
      rw <- fromCBOR
      dlg <- fromCBOR
      p <- fromCBOR
      fgs <- fromCBOR
      gs <- fromCBOR
      ir <- fromCBOR
      pure $ DState rw dlg p fgs gs ir

-- | Current state of staking pools and their certificate counters.
data PState crypto = PState
  { -- | The pool parameters.
    _pParams :: !(Map (KeyHash 'StakePool crypto) (PoolParams crypto)),
    -- | The future pool parameters.
    _fPParams :: !(Map (KeyHash 'StakePool crypto) (PoolParams crypto)),
    -- | A map of retiring stake pools to the epoch when they retire.
    _retiring :: !(Map (KeyHash 'StakePool crypto) EpochNo)
  }
  deriving (Show, Eq, Generic)

instance NoThunks (PState crypto)

instance NFData (PState crypto)

instance CC.Crypto crypto => ToCBOR (PState crypto) where
  toCBOR (PState a b c) =
    encodeListLen 3 <> toCBOR a <> toCBOR b <> toCBOR c

instance CC.Crypto crypto => FromCBOR (PState crypto) where
  fromCBOR = do
    decodeRecordNamed "PState" (const 3) $ do
      a <- fromCBOR
      b <- fromCBOR
      c <- fromCBOR
      pure $ PState a b c

-- | The state associated with the current stake delegation.
data DPState crypto = DPState
  { _dstate :: !(DState crypto),
    _pstate :: !(PState crypto)
  }
  deriving (Show, Eq, Generic)

instance NoThunks (DPState crypto)

instance NFData (DPState crypto)

instance
  CC.Crypto crypto =>
  ToCBOR (DPState crypto)
  where
  toCBOR (DPState ds ps) =
    encodeListLen 2 <> toCBOR ds <> toCBOR ps

instance
  CC.Crypto crypto =>
  FromCBOR (DPState crypto)
  where
  fromCBOR = do
    decodeRecordNamed "DPState" (const 2) $ do
      ds <- fromCBOR
      ps <- fromCBOR
      pure $ DPState ds ps

data AccountState = AccountState
  { _treasury :: !Coin,
    _reserves :: !Coin
  }
  deriving (Show, Eq, Generic)

instance ToCBOR AccountState where
  toCBOR (AccountState t r) =
    encodeListLen 2 <> toCBOR t <> toCBOR r

instance FromCBOR AccountState where
  fromCBOR = do
    decodeRecordNamed "AccountState" (const 2) $ do
      t <- fromCBOR
      r <- fromCBOR
      pure $ AccountState t r

instance NoThunks AccountState

instance NFData AccountState

data EpochState era = EpochState
  { esAccountState :: !AccountState,
    esSnapshots :: !(SnapShots era),
    esLState :: !(LedgerState era),
    esPrevPp :: !(Core.PParams era),
    esPp :: !(Core.PParams era),
    -- | This field, esNonMyopic, does not appear in the formal spec
    -- and is not a part of the protocol. It is only used for providing
    -- data to the stake pool ranking calculation @getNonMyopicMemberRewards@.
    -- See https://hydra.iohk.io/job/Cardano/cardano-ledger-specs/specs.pool-ranking/latest/download-by-type/doc-pdf/pool-ranking
    esNonMyopic :: !(NonMyopic (Crypto era))
  }
  deriving (Generic)

type TransEpoch (c :: Type -> Constraint) era =
  ( TransLedgerState c era,
    c (Core.PParams era)
  )

deriving instance (TransEpoch Show era, Show (UTxO era)) => Show (EpochState era)

deriving stock instance
  TransEpoch Eq era =>
  Eq (EpochState era)

instance (Era era, TransEpoch NoThunks era) => NoThunks (EpochState era)

instance (Era era, TransEpoch NFData era) => NFData (EpochState era)

instance (TransEpoch ToCBOR era) => ToCBOR (EpochState era) where
  toCBOR (EpochState a s l r p n) =
    encodeListLen 6 <> toCBOR a <> toCBOR s <> toCBOR l <> toCBOR r <> toCBOR p <> toCBOR n

instance
  ( FromCBOR (Core.PParams era),
    TransValue FromCBOR era,
    HashAnnotated (Core.TxBody era) EraIndependentTxBody (Crypto era),
    FromCBOR (Core.TxOut era),
    FromCBOR (State (Core.EraRule "PPUP" era)),
    Era era
  ) =>
  FromCBOR (EpochState era)
  where
  fromCBOR =
    decode $
      RecD EpochState
        <! From
        <! From
        <! From
        <! From
        <! From
        <! From

data UpecState era = UpecState
  { -- | Current protocol parameters.
    currentPp :: !(Core.PParams era),
    -- | State of the protocol update transition system.
    ppupState :: !(State (Core.EraRule "PPUP" era))
  }

deriving stock instance
  ( Show (State (Core.EraRule "PPUP" era)),
    Show (Core.PParams era)
  ) =>
  Show (UpecState era)

data PPUPState era = PPUPState
  { proposals :: !(ProposedPPUpdates era),
    futureProposals :: !(ProposedPPUpdates era)
  }
  deriving (Generic)

deriving instance Show (PParamsDelta era) => Show (PPUPState era)

deriving instance Eq (PParamsDelta era) => Eq (PPUPState era)

deriving instance NFData (PParamsDelta era) => NFData (PPUPState era)

instance NoThunks (PParamsDelta era) => NoThunks (PPUPState era)

instance (Era era, ToCBOR (PParamsDelta era)) => ToCBOR (PPUPState era) where
  toCBOR (PPUPState ppup fppup) =
    encodeListLen 2 <> toCBOR ppup <> toCBOR fppup

instance
  (Era era, FromCBOR (PParamsDelta era)) =>
  FromCBOR (PPUPState era)
  where
  fromCBOR =
    decode $
      RecD PPUPState
        <! From
        <! From

pvCanFollow :: ProtVer -> StrictMaybe ProtVer -> Bool
pvCanFollow _ SNothing = True
pvCanFollow (ProtVer m n) (SJust (ProtVer m' n')) =
  (m + 1, 0) == (m', n') || (m, n + 1) == (m', n')

data UTxOState era = UTxOState
  { _utxo :: !(UTxO era),
    _deposited :: !Coin,
    _fees :: !Coin,
    _ppups :: !(State (Core.EraRule "PPUP" era))
  }
  deriving (Generic)

-- | Constraints needed to derive different typeclasses instances (e.g. 'Show'
-- or 'Eq) for some STS states. Here @c@ is the typeclass we are deriving the
-- instance for.
type TransUTxOState (c :: Type -> Constraint) era =
  ( Era era,
    TransTxId c era,
    TransValue c era,
    c (Core.TxOut era),
    c (Core.PParams era),
    c (State (Core.EraRule "PPUP" era)),
    Compactible (Core.Value era)
  )

instance TransUTxOState NFData era => NFData (UTxOState era)

deriving stock instance
  TransUTxOState Show era =>
  Show (UTxOState era)

deriving stock instance
  TransUTxOState Eq era =>
  Eq (UTxOState era)

instance TransUTxOState NoThunks era => NoThunks (UTxOState era)

instance
  TransUTxOState ToCBOR era =>
  ToCBOR (UTxOState era)
  where
  toCBOR (UTxOState ut dp fs us) =
    encodeListLen 4 <> toCBOR ut <> toCBOR dp <> toCBOR fs <> toCBOR us

instance
  ( TransValue FromCBOR era,
    FromCBOR (State (Core.EraRule "PPUP" era)),
    FromCBOR (Core.TxOut era),
    HashAnnotated (Core.TxBody era) EraIndependentTxBody (Crypto era)
  ) =>
  FromCBOR (UTxOState era)
  where
  fromCBOR =
    decode $
      RecD UTxOState
        <! From
        <! From
        <! From
        <! From

-- | New Epoch state and environment
data NewEpochState era = NewEpochState
  { -- | Last epoch
    nesEL :: !EpochNo,
    -- | Blocks made before current epoch
    nesBprev :: !(BlocksMade (Crypto era)),
    -- | Blocks made in current epoch
    nesBcur :: !(BlocksMade (Crypto era)),
    -- | Epoch state before current
    nesEs :: !(EpochState era),
    -- | Possible reward update
    nesRu :: !(StrictMaybe (PulsingRewUpdate (Crypto era))),
    -- | Stake distribution within the stake pool
    nesPd :: !(PoolDistr (Crypto era))
  }
  deriving (Generic)

deriving stock instance
  (TransEpoch Show era) =>
  Show (NewEpochState era)

deriving stock instance
  TransEpoch Eq era =>
  Eq (NewEpochState era)

instance (Era era, TransEpoch NFData era) => NFData (NewEpochState era)

instance (Era era, TransEpoch NoThunks era) => NoThunks (NewEpochState era)

instance
  ( Typeable era,
    TransEpoch ToCBOR era
  ) =>
  ToCBOR (NewEpochState era)
  where
  toCBOR (NewEpochState e bp bc es ru pd) =
    encodeListLen 6 <> toCBOR e <> toCBOR bp <> toCBOR bc <> toCBOR es
      <> toCBOR ru
      <> toCBOR pd

instance
  ( Era era,
    FromCBOR (Core.PParams era),
    FromCBOR (Core.TxOut era),
    FromCBOR (Core.Value era),
    FromCBOR (State (Core.EraRule "PPUP" era))
  ) =>
  FromCBOR (NewEpochState era)
  where
  fromCBOR = do
    decode $
      RecD NewEpochState
        <! From
        <! From
        <! From
        <! From
        <! From
        <! From

getGKeys ::
  NewEpochState era ->
  Set (KeyHash 'Genesis (Crypto era))
getGKeys nes = Map.keysSet genDelegs
  where
    NewEpochState _ _ _ es _ _ = nes
    EpochState _ _ ls _ _ _ = es
    LedgerState _ (DPState (DState _ _ _ _ (GenDelegs genDelegs) _) _) = ls

-- | The state associated with a 'Ledger'.
data LedgerState era = LedgerState
  { -- | The current unspent transaction outputs.
    _utxoState :: !(UTxOState era),
    -- | The current delegation state
    _delegationState :: !(DPState (Crypto era))
  }
  deriving (Generic)

type TransLedgerState (c :: Type -> Constraint) era = TransUTxOState c era

deriving stock instance
  TransLedgerState Show era =>
  Show (LedgerState era)

deriving stock instance
  TransLedgerState Eq era =>
  Eq (LedgerState era)

instance (Era era, TransLedgerState NoThunks era) => NoThunks (LedgerState era)

instance (Era era, TransLedgerState NFData era) => NFData (LedgerState era)

instance
  (Era era, TransLedgerState ToCBOR era) =>
  ToCBOR (LedgerState era)
  where
  toCBOR (LedgerState u dp) =
    encodeListLen 2 <> toCBOR u <> toCBOR dp

instance
  ( Era era,
    HashAnnotated (Core.TxBody era) EraIndependentTxBody (Crypto era),
    FromCBOR (Core.TxOut era),
    FromCBOR (Core.Value era),
    FromCBOR (State (Core.EraRule "PPUP" era))
  ) =>
  FromCBOR (LedgerState era)
  where
  fromCBOR =
    decode $
      RecD LedgerState
        <! From
        <! From

-- | Creates the ledger state for an empty ledger which
--  contains the specified transaction outputs.
genesisState ::
  Default (State (Core.EraRule "PPUP" era)) =>
  Map (KeyHash 'Genesis (Crypto era)) (GenDelegPair (Crypto era)) ->
  UTxO era ->
  LedgerState era
genesisState genDelegs0 utxo0 =
  LedgerState
    ( UTxOState
        utxo0
        (Coin 0)
        (Coin 0)
        def
    )
    (DPState dState def)
  where
    dState = def {_genDelegs = GenDelegs genDelegs0}

-- | Convenience Function to bound the txsize function.
-- | It can be helpful for coin selection.
txsizeBound ::
  forall era out tx.
  ( HasField "outputs" (Core.TxBody era) (StrictSeq out),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "body" tx (Core.TxBody era),
    HasField "txsize" tx Integer
  ) =>
  Proxy era ->
  tx ->
  Integer
txsizeBound Proxy tx = numInputs * inputSize + numOutputs * outputSize + rest
  where
    uint = 5
    smallArray = 1
    hashLen = 32
    hashObj = 2 + hashLen
    addrHashLen = 28
    addrHeader = 1
    address = 2 + addrHeader + 2 * addrHashLen
    txbody = getField @"body" tx
    numInputs = toInteger . length . getField @"inputs" $ txbody
    inputSize = smallArray + uint + hashObj
    numOutputs = toInteger . length . getField @"outputs" $ txbody
    outputSize = smallArray + uint + address
    rest = getField @"txsize" tx

-- | Minimum fee calculation
minfee ::
  ( HasField "_minfeeA" pp Natural,
    HasField "_minfeeB" pp Natural
  ) =>
  pp ->
  Tx era ->
  Coin
minfee pp tx =
  Coin $
    fromIntegral (getField @"_minfeeA" pp)
      * getField @"txsize" tx + fromIntegral (getField @"_minfeeB" pp)

-- | Compute the lovelace which are created by the transaction
produced ::
  forall era pp.
  ( Era era,
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "_keyDeposit" pp Coin,
    HasField "_poolDeposit" pp Coin
  ) =>
  pp ->
  (KeyHash 'StakePool (Crypto era) -> Bool) ->
  Core.TxBody era ->
  Core.Value era
produced pp isNewPool tx =
  balance (txouts @era tx)
    <+> Val.inject
      ( getField @"txfee" tx
          <+> totalDeposits pp isNewPool (toList $ getField @"certs" tx)
      )

-- | Compute the key deregistration refunds in a transaction
keyRefunds ::
  ( HasField "certs" txb (StrictSeq (DCert crypto)),
    HasField "_keyDeposit" pp Coin
  ) =>
  pp ->
  txb ->
  Coin
keyRefunds pp tx = length deregistrations <×> getField @"_keyDeposit" pp
  where
    deregistrations = filter isDeRegKey (toList $ getField @"certs" tx)

-- | Compute the lovelace which are destroyed by the transaction
consumed ::
  forall era pp.
  ( Era era,
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "_keyDeposit" pp Coin
  ) =>
  pp ->
  UTxO era ->
  Core.TxBody era ->
  Core.Value era
consumed pp u tx =
  balance @era (eval (txins @era tx ◁ u)) <> (Val.inject $ refunds <+> withdrawals)
  where
    refunds = keyRefunds pp tx
    withdrawals = fold . unWdrl $ getField @"wdrls" tx

newtype WitHashes crypto = WitHashes
  {unWitHashes :: Set (KeyHash 'Witness crypto)}
  deriving (Eq, Generic)
  deriving (Show) via Quiet (WitHashes crypto)

instance NoThunks (WitHashes crypto)

-- | Check if a set of witness hashes is empty.
nullWitHashes :: WitHashes crypto -> Bool
nullWitHashes (WitHashes a) = Set.null a

-- | Extract the difference between two sets of witness hashes.
diffWitHashes :: WitHashes crypto -> WitHashes crypto -> WitHashes crypto
diffWitHashes (WitHashes x) (WitHashes x') =
  WitHashes (x `Set.difference` x')

-- | Extract the witness hashes from the Transaction.
witsFromTxWitnesses ::
  ( Era era,
    HasField "addrWits" tx (Set (WitVKey 'Witness (Crypto era))),
    HasField "bootWits" tx (Set (BootstrapWitness (Crypto era)))
  ) =>
  tx ->
  WitHashes (Crypto era)
witsFromTxWitnesses coreTx =
  WitHashes $
    Set.map witKeyHash addWits
      `Set.union` Set.map bootstrapWitKeyHash bsWits
  where
    bsWits = getField @"bootWits" coreTx
    addWits = getField @"addrWits" coreTx

-- | Collect the set of hashes of keys that needs to sign a
--  given transaction. This set consists of the txin owners,
--  certificate authors, and withdrawal reward accounts.
witsVKeyNeeded ::
  forall era tx.
  ( Era era,
    HasField "body" tx (Core.TxBody era),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era))
  ) =>
  UTxO era ->
  tx ->
  GenDelegs (Crypto era) ->
  WitHashes (Crypto era)
witsVKeyNeeded utxo' tx genDelegs =
  WitHashes $
    certAuthors
      `Set.union` inputAuthors
      `Set.union` owners
      `Set.union` wdrlAuthors
      `Set.union` updateKeys
  where
    txbody = getField @"body" tx
    inputAuthors :: Set (KeyHash 'Witness (Crypto era))
    inputAuthors = foldr accum Set.empty (getField @"inputs" txbody)
      where
        accum txin ans =
          case txinLookup txin utxo' of
            Just out ->
              case getField @"address" out of
                Addr _ (KeyHashObj pay) _ -> Set.insert (asWitness pay) ans
                AddrBootstrap bootAddr ->
                  Set.insert (asWitness (bootstrapKeyHash bootAddr)) ans
                _ -> ans
            Nothing -> ans

    wdrlAuthors :: Set (KeyHash 'Witness (Crypto era))
    wdrlAuthors = Map.foldrWithKey accum Set.empty (unWdrl (getField @"wdrls" txbody))
      where
        accum key _ ans = Set.union (extractKeyHashWitnessSet [getRwdCred key]) ans
    owners :: Set (KeyHash 'Witness (Crypto era))
    owners = foldr accum Set.empty (getField @"certs" txbody)
      where
        accum (DCertPool (RegPool pool)) ans =
          Set.union
            (Set.map asWitness (_poolOwners pool))
            ans
        accum _cert ans = ans
    cwitness (DCertDeleg dc) = extractKeyHashWitnessSet [delegCWitness dc]
    cwitness (DCertPool pc) = extractKeyHashWitnessSet [poolCWitness pc]
    cwitness (DCertGenesis gc) = Set.singleton (asWitness $ genesisCWitness gc)
    cwitness c = error $ show c ++ " does not have a witness"
    -- key reg requires no witness but this is already filtered outby requiresVKeyWitness
    -- before the call to `cwitness`, so this error should never be reached.

    certAuthors :: Set (KeyHash 'Witness (Crypto era))
    certAuthors = foldr accum Set.empty (getField @"certs" txbody)
      where
        accum cert ans | requiresVKeyWitness cert = Set.union (cwitness cert) ans
        accum _cert ans = ans
    updateKeys :: Set (KeyHash 'Witness (Crypto era))
    updateKeys =
      asWitness
        `Set.map` propWits
          ( strictMaybeToMaybe $
              getField @"update" txbody
          )
          genDelegs

-- | Given a ledger state, determine if the UTxO witnesses in a given
--  transaction are correct.
verifiedWits ::
  forall era tx.
  ( Era era,
    HasField "addrWits" tx (Set (WitVKey 'Witness (Crypto era))),
    HasField "bootWits" tx (Set (BootstrapWitness (Crypto era))),
    HasField "body" tx (Core.TxBody era),
    DSignable (Crypto era) (Hash (Crypto era) EraIndependentTxBody)
  ) =>
  tx ->
  Either [VKey 'Witness (Crypto era)] ()
verifiedWits tx =
  case failed <> failedBootstrap of
    [] -> Right ()
    nonEmpty -> Left nonEmpty
  where
    txbody = getField @"body" tx
    wvkKey (WitVKey k _) = k
    failed =
      wvkKey
        <$> filter
          (not . verifyWitVKey (extractHash (hashAnnotated @(Crypto era) txbody)))
          (Set.toList $ getField @"addrWits" tx)
    failedBootstrap =
      bwKey
        <$> filter
          (not . verifyBootstrapWit (extractHash (hashAnnotated @(Crypto era) txbody)))
          (Set.toList $ getField @"bootWits" tx)

-- | Calculate the set of hash keys of the required witnesses for update
-- proposals.
propWits ::
  Maybe (Update era) ->
  GenDelegs (Crypto era) ->
  Set (KeyHash 'Witness (Crypto era))
propWits Nothing _ = Set.empty
propWits (Just (Update (ProposedPPUpdates pup) _)) (GenDelegs genDelegs) =
  Set.map asWitness . Set.fromList $ Map.elems updateKeys
  where
    updateKeys' = eval (Map.keysSet pup ◁ genDelegs)
    updateKeys = Map.map genDelegKeyHash updateKeys'

-- Functions for stake delegation model

-- | Calculate the change to the deposit pool for a given transaction.
depositPoolChange ::
  ( HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era)))
  ) =>
  LedgerState era ->
  PParams era ->
  Core.TxBody era ->
  Coin
depositPoolChange ls pp tx = (currentPool <+> txDeposits) <-> txRefunds
  where
    -- Note that while (currentPool + txDeposits) >= txRefunds,
    -- it could be that txDeposits < txRefunds. We keep the parenthesis above
    -- to emphasize this point.

    currentPool = (_deposited . _utxoState) ls
    pools = _pParams . _pstate . _delegationState $ ls
    txDeposits =
      totalDeposits pp (`Map.notMember` pools) (toList $ getField @"certs" tx)
    txRefunds = keyRefunds pp tx

reapRewards ::
  RewardAccounts crypto ->
  RewardAccounts crypto ->
  RewardAccounts crypto
reapRewards dStateRewards withdrawals =
  Map.mapWithKey removeRewards dStateRewards
  where
    removeRewards k v = if k `Map.member` withdrawals then Coin 0 else v

---------------------------------
-- epoch boundary calculations --
---------------------------------

stakeDistr ::
  forall era.
  Era era =>
  UTxO era ->
  DState (Crypto era) ->
  PState (Crypto era) ->
  SnapShot (Crypto era)
stakeDistr u ds ps =
  SnapShot
    (Stake $ eval (dom activeDelegs ◁ stakeRelation))
    delegs
    poolParams
  where
    DState rewards' delegs ptrs' _ _ _ = ds
    PState poolParams _ _ = ps
    stakeRelation :: Map (Credential 'Staking (Crypto era)) Coin
    stakeRelation = aggregateUtxoCoinByCredential (forwards ptrs') u rewards'
    activeDelegs :: Map (Credential 'Staking (Crypto era)) (KeyHash 'StakePool (Crypto era))
    activeDelegs = eval ((dom rewards' ◁ delegs) ▷ dom poolParams)

-- | Like the function 'stakeDistr', this can be run at the Epoch boundary to create  PulsingStakeDistr.
--   This can be thought of as a lazy SnapShot, that is run in small increments, using the methods of the Pulsable class.
makePulsingStakeDistr ::
  forall era m.
  Int ->
  UTxO era ->
  DState (Crypto era) ->
  PState (Crypto era) ->
  PulsingStakeDistr era m
makePulsingStakeDistr n u ds ps = StillPulsing (SDP n u (forwards ptrs') activeDelegs (SnapShot (Stake initialDistr) delegs poolParams))
  where
    DState rewards' delegs ptrs' _ _ _ = ds
    PState poolParams _ _ = ps
    activeDelegs :: Map.Map (Credential 'Staking (Crypto era)) (KeyHash 'StakePool (Crypto era))
    activeDelegs = eval ((dom rewards' ◁ delegs) ▷ dom poolParams)
    initialDistr = eval (dom activeDelegs ◁ rewards')

-- | Apply a reward update
applyRUpd ::
  ( HasField "_protocolVersion" (Core.PParams era) ProtVer
  ) =>
  RewardUpdate (Crypto era) ->
  EpochState era ->
  EpochState era
applyRUpd
  ru
  (EpochState as ss ls pr pp _nm) = EpochState as' ss ls' pr pp nm'
    where
      utxoState_ = _utxoState ls
      delegState = _delegationState ls
      dState = _dstate delegState
      (regRU, unregRU) =
        Map.partitionWithKey
          (\k _ -> eval (k ∈ dom (_rewards dState)))
          (aggregateRewards pr $ rs ru)
      as' =
        as
          { _treasury = (addDeltaCoin (_treasury as) (deltaT ru)) <> fold unregRU,
            _reserves = addDeltaCoin (_reserves as) (deltaR ru)
          }
      ls' =
        ls
          { _utxoState =
              utxoState_ {_fees = _fees utxoState_ `addDeltaCoin` deltaF ru},
            _delegationState =
              delegState
                { _dstate =
                    dState
                      { _rewards = eval (_rewards dState ∪+ regRU)
                      }
                }
          }
      nm' = nonMyopic ru

decayFactor :: Float
decayFactor = 0.9

updateNonMyopic ::
  NonMyopic crypto ->
  Coin ->
  Map (KeyHash 'StakePool crypto) Likelihood ->
  NonMyopic crypto
updateNonMyopic nm rPot newLikelihoods =
  nm
    { likelihoodsNM = updatedLikelihoods,
      rewardPotNM = rPot
    }
  where
    history = likelihoodsNM nm
    performance kh newPerf =
      fromMaybe
        mempty
        (applyDecay decayFactor <$> Map.lookup kh history)
        <> newPerf
    updatedLikelihoods = Map.mapWithKey performance newLikelihoods

-- =============================
-- To prevent a huge pause, at the stability point, we spread out the
-- Calculation of rewards over many blocks. We do this in 3 phases. Phase 1
-- of a reward upate is a pure computation, computing some parameters which
-- become fixed at the time when we reach the stability point. One of these
-- parameters is a Pulser, i.e. a computation that when pulseM'ed computes
-- a portion of what is required, so that the whole compuation can be spread out in time.

-- | The EpochState has a field which is (Core.PParams era). We need these
--     fields, a subset of the fields in PParams, in: startStep and createRUpd.
type UsesPP era =
  ( HasField "_d" (Core.PParams era) UnitInterval,
    HasField "_tau" (Core.PParams era) UnitInterval,
    HasField "_a0" (Core.PParams era) NonNegativeInterval,
    HasField "_rho" (Core.PParams era) UnitInterval,
    HasField "_nOpt" (Core.PParams era) Natural,
    HasField "_protocolVersion" (Core.PParams era) ProtVer
  )

-- | Assemble the components for, and then create, a Pulser.
startStep ::
  forall era.
  UsesPP era =>
  EpochSize ->
  BlocksMade (Crypto era) ->
  EpochState era ->
  Coin ->
  ActiveSlotCoeff ->
  Word64 ->
  (PulsingRewUpdate (Crypto era))
startStep slotsPerEpoch b@(BlocksMade b') es@(EpochState acnt ss ls pr _ nm) maxSupply asc secparam =
  let SnapShot stake' delegs' poolParams = _pstakeGo ss
      f, numPools, k :: Rational
      numPools = fromIntegral (Map.size poolParams)
      k = fromIntegral secparam
      f = unboundRational (activeSlotVal asc)
      pulseSize = max 1 (ceiling ((numPools * f) / (6 * k)))
      Coin reserves = _reserves acnt
      ds = _dstate $ _delegationState ls
      -- reserves and rewards change
      deltaR1 =
        rationalToCoinViaFloor $
          min 1 eta
            * unboundRational (getField @"_rho" pr)
            * fromIntegral reserves
      d = unboundRational (getField @"_d" pr)
      expectedBlocks =
        floor $
          (1 - d) * unboundRational (activeSlotVal asc) * fromIntegral slotsPerEpoch
      -- TODO asc is a global constant, and slotsPerEpoch should not change often at all,
      -- it would be nice to not have to compute expectedBlocks every epoch
      blocksMade = fromIntegral $ Map.foldr (+) 0 b' :: Integer
      eta
        | unboundRational (getField @"_d" pr) >= 0.8 = 1
        | otherwise = blocksMade % expectedBlocks
      Coin rPot = _feeSS ss <> deltaR1
      deltaT1 = floor $ unboundRational (getField @"_tau" pr) * fromIntegral rPot
      _R = Coin $ rPot - deltaT1
      totalStake = circulation es maxSupply
      rewsnap =
        RewardSnapShot
          { rewPstakeGo = _pstakeGo ss,
            rewFeeSS = _feeSS ss,
            rewa0 = getField @"_a0" pr,
            rewnOpt = getField @"_nOpt" pr,
            rewprotocolVersion = getField @"_protocolVersion" pr,
            rewNonMyopic = nm,
            rewDeltaR1 = deltaR1,
            rewR = _R,
            rewDeltaT1 = (Coin deltaT1),
            rewTotalStake = totalStake,
            rewRPot = (Coin rPot)
          }
      free =
        FreeVars
          (unBlocksMade b)
          delegs'
          stake'
          (Map.keysSet $ _rewards ds)
          (unCoin totalStake)
          (unCoin (fold . unStake $ stake'))
          asc
          (sum (unBlocksMade b))
          _R
          slotsPerEpoch
          (getField @"_d" pr)
          (getField @"_a0" pr)
          (getField @"_nOpt" pr)
      pulser :: Pulser (Crypto era)
      pulser =
        RSLP
          pulseSize
          free
          (StrictSeq.fromList $ Map.elems poolParams)
          (RewardAns Map.empty Map.empty)
   in (Pulsing rewsnap pulser)

-- Phase 2

-- | Run the pulser for a bit. If is has nothing left to do, complete it.
pulseStep ::
  PulsingRewUpdate crypto ->
  ProvM (RewardProvenance crypto) ShelleyBase (PulsingRewUpdate crypto)
pulseStep (Complete r) = pure (Complete r)
pulseStep (p@(Pulsing _ pulser)) | done pulser = completeStep p
pulseStep (Pulsing rewsnap pulser) = do
  -- The pulser computes one kind of provenance, pulseOther incorporates it
  -- into the current flavor of provenance: RewardProvenance.
  p2 <- (pulseOther pulser)
  pure (Pulsing rewsnap p2)

-- Phase 3

completeStep ::
  PulsingRewUpdate crypto ->
  ProvM (RewardProvenance crypto) ShelleyBase (PulsingRewUpdate crypto)
completeStep (Complete r) = pure (Complete r)
completeStep (Pulsing rewsnap pulser) = do
  p2 <- completeRupd (Pulsing rewsnap pulser)
  pure (Complete p2)

-- | Phase 3 of reward update has several parts
--   a) completeM the pulser (in case there are still computions to run)
--   b) Combine the pulser provenance with the RewardProvenance
--   c) Construct the final RewardUpdate
completeRupd ::
  PulsingRewUpdate crypto ->
  ProvM (RewardProvenance crypto) ShelleyBase (RewardUpdate crypto)
completeRupd (Complete x) = pure x
completeRupd
  ( Pulsing
      ( rewsnap@RewardSnapShot
          { rewDeltaR1 = deltaR1,
            rewR = oldr,
            rewDeltaT1 = (Coin deltaT1),
            rewNonMyopic = nm,
            rewTotalStake = totalstake,
            rewRPot = rpot,
            rewPstakeGo = gosnap,
            rewFeeSS = feesnap,
            rewa0 = a0,
            rewnOpt = nOpt
          }
        )
      pulser
    ) = do
    let combine (RewardAns rs likely) provPools (rewprov@RewardProvenance {pools = old}) =
          rewprov
            { deltaR2 = oldr <-> (sumRewards rewsnap rs),
              pools = Map.union provPools old,
              desirabilities = (Map.foldlWithKey' addDesireability Map.empty likely)
            }
        -- A function to compute the 'desirablity' aggregate. Called only if we are computing
        -- provenance. Adds nested pair ('key',(LikeliHoodEstimate,Desirability)) to the Map 'ans'
        addDesireability ans key likelihood =
          let SnapShot _ _ poolParams = gosnap
              estimate = (percentile' likelihood)
           in Map.insert
                key
                ( Desirability
                    { hitRateEstimate = unPerformanceEstimate estimate,
                      desirabilityScore = case Map.lookup key poolParams of
                        Just ppx -> desirability (a0, nOpt) rpot ppx estimate totalstake
                        Nothing -> 0
                    }
                )
                ans
    RewardAns rs_ newLikelihoods <- liftProv (completeM pulser) Map.empty combine
    let deltaR2 = oldr <-> (sumRewards rewsnap rs_)
    pure $
      RewardUpdate
        { deltaT = (DeltaCoin deltaT1),
          deltaR = ((invert $ toDeltaCoin deltaR1) <> toDeltaCoin deltaR2),
          rs = rs_,
          deltaF = (invert (toDeltaCoin feesnap)),
          nonMyopic = (updateNonMyopic nm oldr newLikelihoods)
        }

-- | To create a reward update, run all 3 phases
createRUpd ::
  forall era.
  (UsesPP era) =>
  EpochSize ->
  BlocksMade (Crypto era) ->
  EpochState era ->
  Coin ->
  ActiveSlotCoeff ->
  Word64 ->
  ProvM (RewardProvenance (Crypto era)) ShelleyBase (RewardUpdate (Crypto era))
createRUpd slotsPerEpoch blocksmade epstate maxSupply asc secparam = do
  let step1 = startStep slotsPerEpoch blocksmade epstate maxSupply asc secparam
  step2 <- pulseStep step1
  case step2 of
    (Complete r) -> pure r
    (Pulsing rewsnap pulser) -> completeRupd (Pulsing rewsnap pulser)

-- =====================================================================

-- | Calculate the current circulation
--
-- This is used in the rewards calculation, and for API endpoints for pool ranking.
circulation :: EpochState era -> Coin -> Coin
circulation (EpochState acnt _ _ _ _ _) supply =
  supply <-> (_reserves acnt)

-- | Update new epoch state
updateNES ::
  NewEpochState era ->
  BlocksMade (Crypto era) ->
  LedgerState era ->
  NewEpochState era
updateNES
  ( NewEpochState
      eL
      bprev
      _
      (EpochState acnt ss _ pr pp nm)
      ru
      pd
    )
  bcur
  ls =
    NewEpochState eL bprev bcur (EpochState acnt ss ls pr pp nm) ru pd

returnRedeemAddrsToReserves ::
  forall era.
  Era era =>
  EpochState era ->
  EpochState era
returnRedeemAddrsToReserves es = es {esAccountState = acnt', esLState = ls'}
  where
    ls = esLState es
    us = _utxoState ls
    UTxO utxo = _utxo us
    (redeemers, nonredeemers) =
      Map.partition
        ( \out ->
            isBootstrapRedeemer (getField @"address" out)
        )
        utxo
    acnt = esAccountState es
    utxoR = UTxO redeemers :: UTxO era
    acnt' =
      acnt
        { _reserves =
            (_reserves acnt)
              <+> (Val.coin . balance $ utxoR)
        }
    us' = us {_utxo = UTxO nonredeemers :: UTxO era}
    ls' = ls {_utxoState = us'}

--------------------------------------------------------------------------------
-- Default instances
--------------------------------------------------------------------------------

instance Default (PPUPState era) where
  def = PPUPState emptyPPPUpdates emptyPPPUpdates

instance
  Default (State (Core.EraRule "PPUP" era)) =>
  Default (UTxOState era)
  where
  def = UTxOState (UTxO Map.empty) (Coin 0) (Coin 0) def

instance
  (Default (LedgerState era), Default (Core.PParams era)) =>
  Default (EpochState era)
  where
  def = EpochState def def def def def def

instance Default (UTxOState era) => Default (LedgerState era) where
  def = LedgerState def def

instance Default (DPState crypto) where
  def = DPState def def

instance Default (InstantaneousRewards crypto) where
  def = InstantaneousRewards Map.empty Map.empty mempty mempty

instance Default (DState crypto) where
  def =
    DState
      Map.empty
      Map.empty
      biMapEmpty
      Map.empty
      (GenDelegs Map.empty)
      def

instance Default (PState crypto) where
  def =
    PState Map.empty Map.empty Map.empty

instance Default AccountState where
  def = AccountState (Coin 0) (Coin 0)
