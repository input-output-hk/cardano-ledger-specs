{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Cardano.Ledger.ModelChain.Script where

import qualified Cardano.Ledger.Alonzo.Scripts as Alonzo
import qualified Cardano.Ledger.Crypto as C
import Cardano.Ledger.Keys
import Cardano.Ledger.ShelleyMA.Timelocks
import Cardano.Slotting.Slot hiding (at)
import qualified Data.Sequence.Strict as StrictSeq
import qualified GHC.Exts as GHC
import Numeric.Natural (Natural)
import Test.Cardano.Ledger.ModelChain.FeatureSet

data ModelAddress (k :: TyScriptFeature) where
  ModelAddress :: String -> ModelAddress k
  ModelScriptAddress :: ModelPlutusScript -> ModelAddress ('TyScriptFeature x 'True)

deriving instance Eq (ModelAddress k)

deriving instance Ord (ModelAddress k)

deriving instance Show (ModelAddress k)

instance GHC.IsString (ModelAddress k) where
  fromString s = ModelAddress s

data ModelScript (k :: TyScriptFeature) where
  ModelScript_Timelock :: ModelTimelock -> ModelScript ('TyScriptFeature 'True x)
  ModelScript_PlutusV1 :: ModelPlutusScript -> ModelScript ('TyScriptFeature x 'True)

deriving instance Eq (ModelScript k)

deriving instance Ord (ModelScript k)

deriving instance Show (ModelScript k)

data ModelPlutusScript
  = ModelPlutusScript_AlwaysSucceeds Natural
  | ModelPlutusScript_AlwaysFails Natural
  deriving (Eq, Ord, Show)

modelScriptNeededSigs :: ModelTimelock -> [ModelAddress k]
modelScriptNeededSigs = go
  where
    go = \case
      ModelTimelock_Signature (ModelAddress ma) -> [ModelAddress ma]
      ModelTimelock_AllOf xs -> go =<< xs
      ModelTimelock_AnyOf xs -> go =<< take 1 xs
      ModelTimelock_MOfN n xs -> go =<< take n xs
      ModelTimelock_TimeStart _ -> []
      ModelTimelock_TimeExpire _ -> []

-- modelScriptNeededSigs (ModelScript_PlutusV1 {}) = []
-- TODO: start/expire are somewhat irritating since absolute slot numbers aren't
-- visible in the model; it should probably be refactored to use epochs + slot
-- in epoch
data ModelTimelock
  = ModelTimelock_Signature (ModelAddress ('TyScriptFeature 'False 'False))
  | ModelTimelock_AllOf [ModelTimelock]
  | ModelTimelock_AnyOf [ModelTimelock]
  | ModelTimelock_MOfN Int [ModelTimelock] -- Note that the Int may be negative in which case (MOfN -2 [..]) is always True
  | ModelTimelock_TimeStart SlotNo -- The start time
  | ModelTimelock_TimeExpire SlotNo -- The time it expires
  deriving (Eq, Ord, Show)

elaborateModelTimelock ::
  forall crypto m.
  (C.Crypto crypto, Applicative m) =>
  (ModelAddress ('TyScriptFeature 'False 'False) -> m (KeyHash 'Witness crypto)) ->
  ModelTimelock ->
  m (Timelock crypto)
elaborateModelTimelock f = go
  where
    go :: ModelTimelock -> m (Timelock crypto)
    go = \case
      ModelTimelock_Signature maddr -> RequireSignature <$> f maddr
      ModelTimelock_AllOf xs -> RequireAllOf . StrictSeq.fromList <$> traverse go xs
      ModelTimelock_AnyOf xs -> RequireAnyOf . StrictSeq.fromList <$> traverse go xs
      ModelTimelock_MOfN m xs -> RequireMOf m . StrictSeq.fromList <$> traverse go xs
      ModelTimelock_TimeStart slotNo -> pure $ RequireTimeStart slotNo
      ModelTimelock_TimeExpire slotNo -> pure $ RequireTimeExpire slotNo

elaborateModelScript ::
  ModelPlutusScript ->
  Alonzo.Script era
elaborateModelScript = \case
  ModelPlutusScript_AlwaysSucceeds n -> Alonzo.alwaysSucceeds n
  ModelPlutusScript_AlwaysFails n -> Alonzo.alwaysFails n
