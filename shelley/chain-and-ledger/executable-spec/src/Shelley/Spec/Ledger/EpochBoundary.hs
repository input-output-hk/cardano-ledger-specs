{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : EpochBoundary
-- Description : Functions and definitions for rules at epoch boundary.
--
-- This modules implements the necessary functions for the changes that can happen at epoch boundaries.
module Shelley.Spec.Ledger.EpochBoundary
  ( Stake (..),
    BlocksMade (..),
    SnapShot (..),
    SnapShots (..),
    emptySnapShot,
    emptySnapShots,
    aggregateUtxoCoinByCredential,
    poolStake,
    obligation,
    maxPool,
    maxPool',
    StakeDistrPulser (..),
    PulsingStakeDistr (..),
    aggregateUtxoCoinByActiveCredential,
    runToCompletion,
    pulse,
    translateSnapShots,
  )
where

import Cardano.Binary (FromCBOR (..), ToCBOR (..), encodeListLen)
import Cardano.Ledger.Address (Addr (..))
import Cardano.Ledger.BaseTypes (BoundedRational (..), NonNegativeInterval)
import Cardano.Ledger.Coin
  ( Coin (..),
    coinToRational,
    rationalToCoinViaFloor,
  )
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential (Credential, Ptr, StakeReference (..))
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Serialization (decodeRecordNamed)
import Cardano.Ledger.Val ((<+>), (<×>))
import qualified Cardano.Ledger.Val as Val
import Control.DeepSeq (NFData (..))
import Control.Monad.Identity (Identity (..))
import Control.SetAlgebra (dom, eval, setSingleton, (▷), (◁))
import Data.Aeson hiding (decode, encode)
import Data.Coders
  ( Decode (..),
    Encode (..),
    decode,
    encode,
    mapDecode,
    mapEncode,
    (!>),
    (<!),
  )
import Data.Default.Class (Default, def)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Pulse (Pulsable (..))
import Data.Ratio ((%))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Records (HasField, getField)
import NoThunks.Class (NoThunks (..), allNoThunks)
import Numeric.Natural (Natural)
import Quiet
import Shelley.Spec.Ledger.TxBody (PoolParams)
import Shelley.Spec.Ledger.UTxO (UTxO (..))

-- =======================================================

-- | Blocks made
newtype BlocksMade crypto = BlocksMade
  { unBlocksMade :: Map (KeyHash 'StakePool crypto) Natural
  }
  deriving (Eq, NoThunks, Generic, NFData)
  deriving (Show) via Quiet (BlocksMade crypto)

deriving instance (CC.Crypto crypto) => ToJSON (BlocksMade crypto)

deriving instance (CC.Crypto crypto) => FromJSON (BlocksMade crypto)

deriving instance CC.Crypto crypto => ToCBOR (BlocksMade crypto)

deriving instance CC.Crypto crypto => FromCBOR (BlocksMade crypto)

-- | Type of stake as map from hash key to coins associated.
newtype Stake crypto = Stake
  { unStake :: Map (Credential 'Staking crypto) Coin
  }
  deriving (Show, Eq, Ord, NoThunks, NFData)

deriving newtype instance
  CC.Crypto crypto => ToCBOR (Stake crypto)

deriving newtype instance
  CC.Crypto crypto => FromCBOR (Stake crypto)

-- A TxOut has 4 different shapes, depending on the shape its embedded of Addr.
-- Credentials are stored in only 2 of the 4 cases.
-- 1) TxOut (Addr _ _ (StakeRefBase cred)) coin   -> HERE
-- 2) TxOut (Addr _ _ (StakeRefPtr ptr)) coin     -> HERE
-- 3) TxOut (Addr _ _ StakeRefNull) coin          -> NOT HERE
-- 4) TxOut (AddrBootstrap _) coin                -> NOT HERE
-- Unfortunately TxOut is a pattern, that deserializes the address. This can be expensive, so if
-- we only deserialize the parts that we need, for the 2 cases that count, we can speed
-- things up considerably. That is the role of deserialiseAddrStakeRef. It returns (Just stake)
-- for the two cases that matter, and Nothing for the other two cases.

-- | Sum up all the Coin for each staking Credential
aggregateUtxoCoinByCredential ::
  forall era.
  Era era =>
  Map Ptr (Credential 'Staking (Crypto era)) ->
  UTxO era ->
  Map (Credential 'Staking (Crypto era)) Coin ->
  Map (Credential 'Staking (Crypto era)) Coin
aggregateUtxoCoinByCredential ptrs (UTxO u) initial =
  Map.foldl' accum initial u
  where
    accum !ans out =
      case (getField @"address" out, getField @"value" out) of
        (Addr _ _ (StakeRefPtr p), c) ->
          case Map.lookup p ptrs of
            Just cred -> Map.insertWith (<>) cred (Val.coin c) ans
            Nothing -> ans
        (Addr _ _ (StakeRefBase hk), c) ->
          Map.insertWith (<>) hk (Val.coin c) ans
        _other -> ans

-- | Get stake of one pool
poolStake ::
  KeyHash 'StakePool crypto ->
  Map (Credential 'Staking crypto) (KeyHash 'StakePool crypto) ->
  Stake crypto ->
  Stake crypto
poolStake hk delegs (Stake stake) =
  Stake $ eval (dom (delegs ▷ setSingleton hk) ◁ stake)

-- | Calculate total possible refunds.
obligation ::
  forall crypto pp.
  (HasField "_keyDeposit" pp Coin, HasField "_poolDeposit" pp Coin) =>
  pp ->
  Map (Credential 'Staking crypto) Coin ->
  Map (KeyHash 'StakePool crypto) (PoolParams crypto) ->
  Coin
obligation pp rewards stakePools =
  (length rewards <×> getField @"_keyDeposit" pp)
    <+> (length stakePools <×> getField @"_poolDeposit" pp)

-- | Calculate maximal pool reward
maxPool' ::
  NonNegativeInterval ->
  Natural ->
  Coin ->
  Rational ->
  Rational ->
  Coin
maxPool' a0 nOpt r sigma pR = rationalToCoinViaFloor $ factor1 * factor2
  where
    z0 = 1 % fromIntegral nOpt
    sigma' = min sigma z0
    p' = min pR z0
    factor1 = coinToRational r / (1 + unboundRational a0)
    factor2 = sigma' + p' * unboundRational a0 * factor3
    factor3 = (sigma' - p' * factor4) / z0
    factor4 = (z0 - sigma') / z0

-- | Version of maxPool' that extracts a0 and nOpt from a PParam with the right HasField instances
maxPool ::
  (HasField "_a0" pp NonNegativeInterval, HasField "_nOpt" pp Natural) =>
  pp ->
  Coin ->
  Rational ->
  Rational ->
  Coin
maxPool pc r sigma pR = maxPool' a0 nOpt r sigma pR
  where
    a0 = getField @"_a0" pc
    nOpt = getField @"_nOpt" pc

-- | Snapshot of the stake distribution.
data SnapShot crypto = SnapShot
  { _stake :: !(Stake crypto),
    _delegations :: !(Map (Credential 'Staking crypto) (KeyHash 'StakePool crypto)),
    _poolParams :: !(Map (KeyHash 'StakePool crypto) (PoolParams crypto))
  }
  deriving (Show, Eq, Generic)

instance NoThunks (SnapShot crypto)

instance NFData (SnapShot crypto)

instance
  CC.Crypto crypto =>
  ToCBOR (SnapShot crypto)
  where
  toCBOR
    ( SnapShot
        { _stake = s,
          _delegations = d,
          _poolParams = p
        }
      ) =
      encodeListLen 3
        <> toCBOR s
        <> toCBOR d
        <> toCBOR p

instance
  CC.Crypto crypto =>
  FromCBOR (SnapShot crypto)
  where
  fromCBOR = do
    decodeRecordNamed "SnapShot" (const 3) $ do
      s <- fromCBOR
      d <- fromCBOR
      p <- fromCBOR
      pure $ SnapShot s d p

-- | Snapshots of the stake distribution.
data SnapShots era = SnapShots
  { _pstakeMark :: !(PulsingStakeDistr era Identity),
    _pstakeSet :: !(SnapShot (Crypto era)),
    _pstakeGo :: !(SnapShot (Crypto era)),
    _feeSS :: !Coin
  }

deriving instance Show (UTxO era) => Show (SnapShots era)

deriving instance (Era era, Eq (UTxO era)) => Eq (SnapShots era)

deriving instance Generic (SnapShots era)

instance (Era era, NoThunks (UTxO era)) => NoThunks (SnapShots era) where
  showTypeOf _ = "SnapShots"
  wNoThunks ctxt (SnapShots mark set go fee) =
    allNoThunks
      [ noThunks ctxt mark,
        noThunks ctxt set,
        noThunks ctxt go,
        noThunks ctxt fee
      ]

instance (Era era, NFData (UTxO era)) => NFData (SnapShots era) where
  rnf (SnapShots mark set go fee) = seq (rnf mark) (seq (rnf set) (seq (rnf go) (rnf fee)))

-- | CBOR serialization of a SnapShots that is still pulsing, completes the  _pstakeMark field
--   before it is serialized. This has several good consequences.
--   1) The serialization of SnapShots remains the same as it was before pulsing was added
--   2) The size of the Serialization is much smaller (A pulser contains a copy of the UTxO)
--   3) Deserialization always results in a Completed  _pstakeMark field.
instance
  (Era era, ToCBOR (UTxO era)) =>
  ToCBOR (SnapShots era)
  where
  toCBOR (SnapShots (Completed mark) set go fs) =
    encodeListLen 4
      <> toCBOR mark
      <> toCBOR set
      <> toCBOR go
      <> toCBOR fs
  toCBOR (SnapShots (mark@(StillPulsing _)) set go fs) =
    encodeListLen 4
      <> toCBOR (runToCompletion mark)
      <> toCBOR set
      <> toCBOR go
      <> toCBOR fs

instance
  (Era era, FromCBOR (UTxO era), FromCBOR (Core.TxOut era)) =>
  FromCBOR (SnapShots era)
  where
  fromCBOR = do
    decodeRecordNamed "SnapShots" (const 4) $ do
      mark <- fromCBOR
      set <- fromCBOR
      go <- fromCBOR
      f <- fromCBOR
      pure $ SnapShots (Completed mark) set go f

instance Default (SnapShots era) where
  def = emptySnapShots

emptySnapShot :: SnapShot crypto
emptySnapShot = SnapShot (Stake Map.empty) Map.empty Map.empty

emptySnapShots :: SnapShots era
emptySnapShots = SnapShots (Completed emptySnapShot) emptySnapShot emptySnapShot (Coin 0)

-- ===================================================================
-- Pulsing Stake Distribution
-- ===================================================================

-- | A pulsing implementation of a SnapShot
data PulsingStakeDistr era m
  = StillPulsing !(StakeDistrPulser era m (SnapShot (Crypto era))) -- Pulsing work still to do
  | Completed !(SnapShot (Crypto era)) -- Pulsing work completed, ultimate goal reached

-- | Run a PulsingStakeDistr (a lazy SnapShot) until it is completed.
runToCompletion ::
  Era era =>
  PulsingStakeDistr era Identity ->
  SnapShot (Crypto era)
runToCompletion (Completed ss) = ss
runToCompletion (StillPulsing sdp) = runIdentity (completeM sdp)

pulse ::
  Era era =>
  PulsingStakeDistr era Identity ->
  PulsingStakeDistr era Identity
pulse (Completed ss) = (Completed ss)
pulse (StillPulsing sdp) =
  if (done new)
    then Completed (current new)
    else StillPulsing new
  where
    new = (runIdentity (pulseM sdp))

-- | We write our own Eq instance which completes one of the arguments when their constructors differ.
instance
  ( Era era,
    Eq (UTxO era)
  ) =>
  Eq (PulsingStakeDistr era Identity)
  where
  (StillPulsing sdp1) == (StillPulsing sdp2) = sdp1 == sdp2
  (Completed ss1) == (Completed ss2) = ss1 == ss2
  (Completed ss1) == (StillPulsing sdp2) = ss1 == (runIdentity (completeM sdp2))
  (StillPulsing sdp1) == (Completed ss2) = ss2 == (runIdentity (completeM sdp1))

deriving instance (Show (UTxO era)) => Show (PulsingStakeDistr era m)

deriving instance Generic (PulsingStakeDistr era m)

instance (Era era, NoThunks (UTxO era)) => NoThunks (PulsingStakeDistr era m) where
  showTypeOf _ = "PulsingStakeDistr"
  wNoThunks ctxt (StillPulsing x) = allNoThunks [noThunks ctxt x]
  wNoThunks ctxt (Completed x) = allNoThunks [noThunks ctxt x]

instance (Era era, NFData (UTxO era)) => NFData (PulsingStakeDistr era m) where
  rnf (StillPulsing x) = (rnf x)
  rnf (Completed x) = (rnf x)

instance (Typeable m, Era era, ToCBOR (UTxO era)) => ToCBOR (PulsingStakeDistr era m) where
  toCBOR (StillPulsing p) = encode (Sum (StillPulsing @era) 0 !> To p)
  toCBOR (Completed r) = encode (Sum (Completed @era) 1 !> To r)

instance (Typeable m, Era era, FromCBOR (UTxO era), FromCBOR (Core.TxOut era)) => FromCBOR (PulsingStakeDistr era m) where
  fromCBOR = decode (Summands "PulsingStakeDistr" decPSD)
    where
      decPSD 0 = (SumD StillPulsing <! From)
      decPSD 1 = (SumD Completed <! From)
      decPSD n = Invalid n

-- ===============================================================================

-- | StakeDistrPulser acts like a serializable closure for the lazy computation of a SnapShot.
--   It will be made an instance of Puslsable, so it need to be a Ternary type constuctor.
--  'm' is the monad that the pulsing action is executed in, and 'ans' is the type of the object
--  computed by the closure. (it will be SnapShot)
data StakeDistrPulser era (m :: Type -> Type) ans where
  SDP ::
    (ans ~ SnapShot (Crypto era)) =>
    !Int ->
    !(UTxO era) ->
    !(Map.Map Ptr (Credential 'Staking (Crypto era))) ->
    -- We do make SDP lazy in the map of active credentials, so it is not computed at the
    -- at the Epoch Boundary, but only at the first Tick. After that it will already be in normal form.
    (Map.Map (Credential 'Staking (Crypto era)) (KeyHash 'StakePool (Crypto era))) ->
    !ans ->
    StakeDistrPulser era m ans

deriving instance (Eq (UTxO era), Eq ans) => Eq (StakeDistrPulser era m ans)

deriving instance (Show (UTxO era), Show ans) => Show (StakeDistrPulser era m ans)

instance (Era era, NoThunks (UTxO era), c ~ (Crypto era)) => NoThunks (StakeDistrPulser era m (SnapShot c)) where
  showTypeOf _ = "StakeDistrPulser"
  wNoThunks ctxt (SDP n u ptrs activedelegs ans) =
    allNoThunks
      [ noThunks ctxt n,
        noThunks ctxt u,
        noThunks ctxt ptrs,
        noThunks ctxt activedelegs,
        noThunks ctxt ans
      ]

instance (Era era, NFData (UTxO era), c ~ (Crypto era)) => NFData (StakeDistrPulser era m (SnapShot c)) where
  rnf (SDP n u ptrs active ans) = seq (rnf n) (seq (rnf u) (seq (rnf ptrs) (seq (rnf active) (rnf ans))))

instance (Typeable m, Era era, c ~ Crypto era, ToCBOR (UTxO era)) => ToCBOR (StakeDistrPulser era m (SnapShot c)) where
  toCBOR (SDP n utxo ptrs active ans) =
    encode (Rec SDP !> To n !> To utxo !> mapEncode ptrs !> mapEncode active !> To ans)

instance (Typeable m, Era era, c ~ Crypto era, FromCBOR (UTxO era)) => FromCBOR (StakeDistrPulser era m (SnapShot c)) where
  fromCBOR =
    decode
      ( RecD SDP <! From <! From <! mapDecode <! mapDecode <! From
      )

-- ====================================================================

-- NOW make it an instance of Pulsable, for (StakeDistrPulser era)

instance
  ( Era era,
    c ~ Crypto era
  ) =>
  Pulsable (StakeDistrPulser era)
  where
  done (SDP _n (UTxO u) _ptrs _active _ans) = Map.null u
  current (SDP _n _utxo _ptrs _active ans) = ans
  pulseM ll@(SDP _n (UTxO u) _ptrs _active _ans) | Map.null u = pure ll
  pulseM (SDP n (UTxO u) ptrs active (SnapShot (Stake b) ds ps)) = do
    let (!steps, !smaller_u) = Map.splitAt n u
        new = SnapShot (Stake (aggregateUtxoCoinByActiveCredential @era ptrs active (UTxO steps) b)) ds ps
    pure (SDP n (UTxO smaller_u) ptrs active new)
  completeM (SDP _n utxo ptrs active (SnapShot (Stake b) ds ps)) =
    let stakeRelation = aggregateUtxoCoinByActiveCredential @era ptrs active utxo b
     in pure $ SnapShot (Stake stakeRelation) ds ps

-- | Sum up all the Coin for each active staking Credential
aggregateUtxoCoinByActiveCredential ::
  forall era.
  Era era =>
  Map.Map Ptr (Credential 'Staking (Crypto era)) ->
  Map.Map (Credential 'Staking (Crypto era)) (KeyHash 'StakePool (Crypto era)) ->
  UTxO era ->
  Map.Map (Credential 'Staking (Crypto era)) Coin ->
  Map.Map (Credential 'Staking (Crypto era)) Coin
aggregateUtxoCoinByActiveCredential ptrs active (UTxO u) initial =
  Map.foldl' accum initial u
  where
    accum !ans out =
      case (getField @"address" out, getField @"value" out) of
        (Addr _ _ (StakeRefPtr p), c) ->
          case Map.lookup p ptrs of
            Just cred ->
              if Map.member cred active -- Add it only if the credential is active.
                then Map.insertWith (<>) cred (Val.coin c) ans
                else ans
            Nothing -> ans
        (Addr _ _ (StakeRefBase hk), c) ->
          if Map.member hk active -- Add it only if the credential is active.
            then Map.insertWith (<>) hk (Val.coin c) ans
            else ans
        _other -> ans

-- | Translates (and completes) a SnapShots structure from one Era to another arbitrary Era.
--   Usefull in the translation phase from one Era (like ShelleyEra) to another (say AllegrEra).
--   A SnapShot is Era invariant, but the PulsingStakeDistr in the  _pstakeMark field of a
--   SnapShots, differs between Era as it contains an UTxO. By completing the  _pstakeMark field,
--   we remove the Era dependence, because the Completed  _pstakeMark field can live in any Era.
--   The consequence of this is that any Hardfork, any SnapsShots still pulsing, will be completed
--   at the hard fork. A similar strategy is used when serializing SnapShots.
translateSnapShots ::
  forall era1 era2.
  ( Era era1,
    Crypto era1 ~ Crypto era2
  ) =>
  SnapShots era1 ->
  SnapShots era2
translateSnapShots (SnapShots mark set go fee) =
  SnapShots (Completed (runToCompletion mark)) set go fee
