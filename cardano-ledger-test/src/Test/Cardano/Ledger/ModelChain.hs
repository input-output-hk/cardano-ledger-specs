{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.ModelChain where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Crypto as C
import Cardano.Ledger.Mary.Value (AssetName, PolicyID (..))
import qualified Cardano.Ledger.Mary.Value
import qualified Cardano.Ledger.Val as Val
import Cardano.Slotting.Slot hiding (at)
import Control.Lens
import qualified Control.Monad.State.Strict as State
import Data.Foldable (fold)
import Data.Kind (Type)
import qualified Data.Map as Map
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import qualified GHC.Exts as GHC
import qualified PlutusTx
import Shelley.Spec.Ledger.STS.EraMapping ()
import Test.Cardano.Ledger.ModelChain.Address
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Script
import Test.Cardano.Ledger.ModelChain.Value

class Val.Val val => ValueFromList val crypto | val -> crypto where
  valueFromList :: Integer -> [(PolicyID crypto, AssetName, Integer)] -> val

  insert :: (Integer -> Integer -> Integer) -> PolicyID crypto -> AssetName -> Integer -> val -> val

  gettriples :: val -> (Integer, [(PolicyID crypto, AssetName, Integer)])

instance C.Crypto crypto => ValueFromList (Cardano.Ledger.Mary.Value.Value crypto) crypto where
  valueFromList = Cardano.Ledger.Mary.Value.valueFromList

  insert = Cardano.Ledger.Mary.Value.insert

  gettriples (Cardano.Ledger.Mary.Value.Value c m1) = (c, triples)
    where
      triples =
        [ (policyId, aname, amount)
          | (policyId, m2) <- Map.toList m1,
            (aname, amount) <- Map.toList m2
        ]

-- TODO: this is a bit overconstrained, we probably want a more constraints
-- based approach using ValueFromList
type family ElaborateValueType (valF :: TyValueExpected) crypto :: Type where
  ElaborateValueType 'ExpectAdaOnly _ = Coin
  ElaborateValueType 'ExpectAnyOutput crypto = Cardano.Ledger.Mary.Value.Value crypto

instance RequiredFeatures ModelTxOut where
  filterFeatures tag@(FeatureTag v _) (ModelTxOut addr qty dat) =
    hasKnownValueFeature v $
      ModelTxOut
        <$> filterModelAddress tag addr
        <*> (filterFeatures tag =<< filterModelValue qty)
        <*> (filterSupportsPlutus tag dat)

filterModelValueVars ::
  forall a b c d.
  (KnownRequiredFeatures c, KnownValueFeature d) =>
  ModelValueVars a b ->
  Maybe (ModelValueVars c d)
filterModelValueVars (ModelValue_Reward x) = ModelValue_Reward <$> filterModelAddress (reifyRequiredFeatures (Proxy @c)) x
filterModelValueVars (ModelValue_MA x ys) = do
  Refl <- reifyExpectAnyOutput (reifyValueFeature (Proxy @d))
  Refl <- reifyExpectAnyOutput (reifyValueFeature (Proxy @(ValueFeature c)))

  let f :: ModelScript (ScriptFeature a) -> Maybe (ModelScript (ScriptFeature c))
      f = \case
        ModelScript_Timelock t -> case reifyScriptFeature (Proxy @(ScriptFeature c)) of
          ScriptFeatureTag_None -> Nothing
          ScriptFeatureTag_Simple -> Just $ ModelScript_Timelock t
          ScriptFeatureTag_PlutusV1 -> Just $ ModelScript_Timelock t
        ModelScript_PlutusV1 t -> case reifyScriptFeature (Proxy @(ScriptFeature c)) of
          ScriptFeatureTag_None -> Nothing
          ScriptFeatureTag_Simple -> Nothing
          ScriptFeatureTag_PlutusV1 -> Just $ ModelScript_PlutusV1 t

  ModelValue_MA x . Map.fromList <$> (traverse . _1) f (Map.toList ys)

-- change the "expected return type" of a ModelValue
filterModelValue ::
  forall a b c.
  (KnownValueFeature b, KnownRequiredFeatures c) =>
  ModelValue a c ->
  Maybe (ModelValue b c)
filterModelValue = \case
  ModelValue x -> ModelValue <$> traverse filterModelValueVars x

instance KnownValueFeature v => RequiredFeatures (ModelValue v) where
  filterFeatures tag (ModelValue val) = ModelValue <$> traverse (hasKnownRequiredFeatures tag filterModelValueVars) val

instance RequiredFeatures ModelTx where
  filterFeatures :: forall a b. KnownRequiredFeatures a => FeatureTag b -> ModelTx a -> Maybe (ModelTx b)
  filterFeatures tag (ModelTx a ins outs fee dcert wdrl g cins) =
    ModelTx a ins
      <$> (traverse . traverse) (filterFeatures tag) outs
      <*> (filterFeatures tag fee)
      <*> traverse (filterFeatures tag) dcert
      <*> fmap Map.fromList (for (Map.toList wdrl) $ \(k, v) -> (,) <$> filterModelAddress tag k <*> filterFeatures tag v) -- traverse (filterFeatures tag) f
      <*> case g of
        NoMintSupport () -> case tag of
          FeatureTag ValueFeatureTag_AdaOnly _ -> pure $ NoMintSupport ()
          FeatureTag ValueFeatureTag_AnyOutput _ -> pure (SupportsMint . ModelValue . ModelValue_Inject $ Coin 0)
        SupportsMint g' -> case tag of
          FeatureTag ValueFeatureTag_AdaOnly _ | g' == ModelValue (ModelValue_Inject $ Val.zero) -> pure $ NoMintSupport ()
          FeatureTag ValueFeatureTag_AdaOnly _ -> Nothing
          FeatureTag ValueFeatureTag_AnyOutput _ -> SupportsMint <$> filterFeatures tag g'
      <*> let setNotEmpty :: Set x -> Maybe (Set x)
              setNotEmpty x
                | Set.null x = Nothing
                | otherwise = Just x
           in (fmap (mapSupportsPlutus fold) $ filterSupportsPlutus tag $ mapSupportsPlutus setNotEmpty cins)

filterModelAddress ::
  FeatureTag b ->
  ModelAddress a ->
  Maybe (ModelAddress (ScriptFeature b))
filterModelAddress (FeatureTag _ s) = \case
  ModelAddress a -> Just (ModelAddress a)
  ModelScriptAddress a -> case s of
    ScriptFeatureTag_None -> Nothing
    ScriptFeatureTag_Simple -> Nothing
    ScriptFeatureTag_PlutusV1 -> Just (ModelScriptAddress a)

instance RequiredFeatures ModelBlock where
  filterFeatures tag (ModelBlock slotNo txns) =
    ModelBlock slotNo
      <$> traverse (filterFeatures tag) txns

instance RequiredFeatures ModelEpoch where
  filterFeatures tag (ModelEpoch blocks x) =
    ModelEpoch
      <$> traverse (filterFeatures tag) blocks
      <*> pure x

newtype ModelTxId = ModelTxId Integer
  deriving (Eq, Ord, Show, Num)

type ModelTxIn = ModelUTxOId

type ModelMA era = Map.Map (ModelScript era) (Map.Map AssetName Integer)

data ModelValueVars era (k :: TyValueExpected) where
  ModelValue_Reward :: ModelAddress (ScriptFeature era) -> ModelValueVars era k
  ModelValue_MA ::
    ('ExpectAnyOutput ~ ValueFeature era) =>
    Coin ->
    ModelMA (ScriptFeature era) ->
    ModelValueVars era 'ExpectAnyOutput

deriving instance Show (ModelValueVars era valF)

deriving instance Eq (ModelValueVars era valF)

deriving instance Ord (ModelValueVars era valF)

newtype ModelValue k era = ModelValue {unModelValue :: ModelValueF (ModelValueVars era k)}
  deriving (Eq, Ord, Show)

data ModelTxOut era = ModelTxOut
  { _mtxo_address :: !(ModelAddress (ScriptFeature era)),
    _mtxo_value :: !(ModelValue (ValueFeature era) era),
    _mtxo_data :: !(IfSupportsPlutus () (Maybe PlutusTx.Data) (ScriptFeature era))
  }
  deriving (Eq, Ord, Show)

newtype ModelUTxOId = ModelUTxOId {unModelUTxOId :: Integer}
  deriving (Eq, Ord, Show, Num, Enum)

data ModelTx (era :: FeatureSet) = ModelTx
  { _mtxId :: !ModelTxId,
    _mtxInputs :: !(Set ModelTxIn),
    _mtxOutputs :: ![(ModelUTxOId, ModelTxOut era)],
    _mtxFee :: !(ModelValue 'ExpectAdaOnly era),
    _mtxDCert :: ![ModelDCert era],
    _mtxWdrl :: !(Map.Map (ModelAddress (ScriptFeature era)) (ModelValue 'ExpectAdaOnly era)),
    _mtxMint :: !(IfSupportsMint () (ModelValue (ValueFeature era) era) (ValueFeature era)),
    _mtxCollateral :: !(IfSupportsPlutus () (Set ModelTxIn) (ScriptFeature era))
  }

data ModelBlock era = ModelBlock SlotNo [ModelTx era]

newtype ModelPoolId = ModelPoolId {unModelPoolId :: String}
  deriving (Eq, Ord, Show, GHC.IsString)

data ModelBlocksMade = ModelBlocksMade (Map.Map ModelPoolId Rational)

repartition :: forall a b t. (Traversable t, Integral a, RealFrac b) => a -> t b -> t a
repartition total weights = State.evalState (traverse step weights) (0 :: b)
  where
    step weight = do
      err <- State.get
      let fracValue :: b
          fracValue = err + fromIntegral total * weight
          value :: a
          value = round fracValue
      State.put (fracValue - fromIntegral value)
      pure value

data ModelEpoch era = ModelEpoch [ModelBlock era] ModelBlocksMade

data ModelDelegation era = ModelDelegation
  { _mdDelegator :: !(ModelAddress (ScriptFeature era)),
    _mdDelegatee :: !ModelPoolId
  }

instance RequiredFeatures ModelDelegation where
  filterFeatures tag (ModelDelegation a b) =
    ModelDelegation
      <$> filterModelAddress tag a
      <*> pure b

data ModelPoolParams era = ModelPoolParams
  { _mppId :: !ModelPoolId,
    _mppPledge :: !Coin,
    _mppCost :: !Coin,
    _mppMargin :: !UnitInterval,
    _mppRAcnt :: !(ModelAddress (ScriptFeature era)),
    _mppOwners :: ![ModelAddress (ScriptFeature era)]
  }

instance RequiredFeatures ModelPoolParams where
  filterFeatures tag (ModelPoolParams poolId pledge cost margin rAcnt owners) =
    ModelPoolParams poolId pledge cost margin
      <$> filterModelAddress tag rAcnt
      <*> traverse (filterModelAddress tag) owners

-- ignores genesis delegation details.
data ModelDCert era
  = ModelRegisterStake (ModelAddress (ScriptFeature era))
  | ModelDeRegisterStake (ModelAddress (ScriptFeature era))
  | ModelDelegate (ModelDelegation era)
  | ModelRegisterPool (ModelPoolParams era)
  | ModelRetirePool ModelPoolId EpochNo

instance RequiredFeatures ModelDCert where
  filterFeatures tag = \case
    ModelRegisterStake a -> ModelRegisterStake <$> filterModelAddress tag a
    ModelDeRegisterStake a -> ModelDeRegisterStake <$> filterModelAddress tag a
    ModelDelegate a -> ModelDelegate <$> filterFeatures tag a
    ModelRegisterPool a -> ModelRegisterPool <$> filterFeatures tag a
    ModelRetirePool a b -> pure $ ModelRetirePool a b

-- TODO: | ModelMIRCert Shelley.MIRPot (Map.Map ModelAddress DeltaCoin)

instance Semigroup ModelBlocksMade where
  ModelBlocksMade x <> ModelBlocksMade y = ModelBlocksMade $ Map.unionWith (+) x y

instance Monoid ModelBlocksMade where
  mempty = ModelBlocksMade Map.empty

data ModelPredicateFailure era
  = ModelValueNotConservedUTxO
      !(ModelValue (ValueFeature era) era)
      -- ^ the Coin consumed by this transaction
      !(ModelValue (ValueFeature era) era)
      -- ^ the Coin produced by this transaction
