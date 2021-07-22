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
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Test.Cardano.Ledger.Elaborators where

-- TODO use CPS'ed writer

import qualified Cardano.Crypto.DSIGN.Class as DSIGN
import qualified Cardano.Crypto.Hash.Class as Hash
import qualified Cardano.Crypto.VRF.Class (VerKeyVRF)
import Cardano.Ledger.Address
import qualified Cardano.Ledger.Alonzo.Data as Alonzo
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..))
import qualified Cardano.Ledger.Alonzo.Scripts as Alonzo
import Cardano.Ledger.Alonzo.Tx (ScriptPurpose (..))
import qualified Cardano.Ledger.Alonzo.Tx as Alonzo
import qualified Cardano.Ledger.Alonzo.TxWitness as Alonzo
import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Credential (Credential (..), StakeCredential, StakeReference (..))
import qualified Cardano.Ledger.Crypto as C
import Cardano.Ledger.Era
import Cardano.Ledger.Hashes (ScriptHash)
import Cardano.Ledger.Keys
import Cardano.Ledger.Mary.Value (PolicyID (..))
import Cardano.Ledger.SafeHash (SafeHash, hashAnnotated)
import Cardano.Ledger.Shelley.Constraints
import Cardano.Ledger.ShelleyMA.Timelocks (Timelock)
import qualified Cardano.Ledger.Val as Val
import Cardano.Slotting.EpochInfo.API
import Cardano.Slotting.Slot hiding (at)
import Control.Lens
import Control.Monad
import qualified Control.Monad.Except as Except
import Control.Monad.State (MonadState (..))
import qualified Control.Monad.State.Class as State
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.State as State hiding (get, gets, state)
import qualified Control.Monad.Writer as Writer
import Data.Default.Class
import Data.Foldable
import Data.Function (on)
import Data.Functor.Compose
import qualified Data.Map as Map
import Data.Proxy
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import Data.Traversable
import Data.Tuple (swap)
import Data.Typeable (Typeable)
import Data.Void
import Data.Word (Word64)
import GHC.Records (HasField (..))
import Numeric.Natural
import qualified PlutusTx
import Shelley.Spec.Ledger.API.Genesis
import Shelley.Spec.Ledger.API.Mempool
import Shelley.Spec.Ledger.API.Validation
import Shelley.Spec.Ledger.EpochBoundary (BlocksMade (..))
import Shelley.Spec.Ledger.Genesis
import Shelley.Spec.Ledger.LedgerState (NewEpochState)
import qualified Shelley.Spec.Ledger.LedgerState as LedgerState
import Shelley.Spec.Ledger.STS.EraMapping ()
import qualified Shelley.Spec.Ledger.Tx as Shelley
import Shelley.Spec.Ledger.TxBody
  ( DCert (..),
    DelegCert (..),
    Delegation (..),
    PoolCert (..),
    PoolParams (..),
  )
import qualified Shelley.Spec.Ledger.TxBody as Shelley
import qualified Shelley.Spec.Ledger.UTxO as UTxO
import Test.Cardano.Ledger.ModelChain
import Test.Cardano.Ledger.ModelChain.Address
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Script
import Test.Cardano.Ledger.ModelChain.Value
import Test.Shelley.Spec.Ledger.Generator.ScriptClass (mkKeyPairs)
import Test.Shelley.Spec.Ledger.Utils (RawSeed (..), mkKeyPair, mkVRFKeyPair)
import qualified Text.Show as Show

data ExpectedValueTypeC era where
  ExpectedValueTypeC_Simple ::
    ( Core.Value era ~ Coin,
      EraValueFeature era ~ 'ExpectAdaOnly
    ) =>
    ExpectedValueTypeC era
  ExpectedValueTypeC_MA ::
    ( ValueFromList (Core.Value era) (Crypto era),
      EraValueFeature era ~ 'ExpectAnyOutput,
      ValidateScript era
    ) =>
    ExpectedValueTypeC era

newtype ElaboratedScriptsCache era = ElaboratedScriptsCache
  {unElaboratedScriptsCache :: Map.Map (ScriptHash (Crypto era)) (Core.Script era)}

instance Semigroup (ElaboratedScriptsCache era) where
  ElaboratedScriptsCache a <> ElaboratedScriptsCache b = ElaboratedScriptsCache $ Map.unionWith const a b

instance Monoid (ElaboratedScriptsCache era) where
  mempty = ElaboratedScriptsCache Map.empty

instance Show (ElaboratedScriptsCache era) where
  showsPrec n (ElaboratedScriptsCache xs) =
    Show.showParen (n >= 11) $
      Show.showString "ElaboratedScriptsCache "
        . showsPrec 11 (Map.keysSet xs)

-- when creating outputs at "genesis", we know the txid's apriori; and recorde
-- them immediately.  otherwise we don't know the txid's until we're done
-- composing the txBody, and need a layer of indirection.
type ModelTxId' c = Either (Shelley.TxIn c) (ModelTxId, Natural)

data EraElaboratorState era = EraElaboratorState
  { _eesUnusedKeyPairs :: Word64,
    _eesKeys :: Map.Map (ModelAddress (EraScriptFeature era)) (TestAddrInfo era),
    _eesPools :: Map.Map ModelPoolId (TestPoolKey era),
    _eesTxIds :: Map.Map ModelTxId (Shelley.TxId (Crypto era)),
    _eesCurrentEpoch :: EpochNo,
    _eesUTxOs :: Map.Map ModelUTxOId (TestUTxOInfo era),
    _eesCurrentSlot :: SlotNo,
    _eesStakeCredentials :: Map.Map (StakeCredential (Crypto era)) (ModelAddress (EraScriptFeature era))
  }

deriving instance
  (C.Crypto (Crypto era), Show (Core.Script era)) =>
  Show (EraElaboratorState era)

data TestUTxOInfo era = TestUTxOInfo
  { _tuoi_txid :: ModelTxId' (Crypto era),
    _tuoi_maddr :: ModelAddress (EraScriptFeature era),
    _tuoi_data :: StrictMaybe (Alonzo.DataHash (Crypto era), (Alonzo.Data era))
  }
  deriving (Show)

data EraElaboratorTxAccum era = EraElaboratorTxAccum
  { _eesPendingWitnessKeys :: [KeyPair 'Witness (Crypto era)],
    _eesScripts :: ElaboratedScriptsCache era,
    _eesRedeemers :: [TestRedeemer era],
    _eetaDats :: Alonzo.TxDats era
  }

instance Typeable era => Semigroup (EraElaboratorTxAccum era) where
  EraElaboratorTxAccum a b c d <> EraElaboratorTxAccum a' b' c' d' =
    EraElaboratorTxAccum
      (a <> a')
      (b <> b')
      (c <> c')
      (d <> d')

instance Typeable era => Monoid (EraElaboratorTxAccum era) where
  mempty = EraElaboratorTxAccum mempty mempty mempty mempty

-- under normal circumstances, this arises during elaboration, at which time the
-- era is already known
data TestRedeemer era = TestRedeemer
  { _trdmrPtr :: !(Alonzo.ScriptPurpose (Crypto era)),
    _trdmData :: !PlutusTx.Data,
    _trdmExUnits :: !ExUnits
  }
  deriving (Eq, Show)

elaborateModelRedeemer ::
  forall era.
  ( HasField "inputs" (Core.TxBody era) (Set.Set (Shelley.TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Shelley.Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq.StrictSeq (DCert (Crypto era))),
    HasField "minted" (Core.TxBody era) (Set.Set (ScriptHash (Crypto era)))
  ) =>
  Core.TxBody era ->
  TestRedeemer era ->
  StrictMaybe (Alonzo.RdmrPtr, (Alonzo.Data era, Alonzo.ExUnits))
elaborateModelRedeemer tx (TestRedeemer scriptPurpose dat exUnits) =
  (,) <$> (Alonzo.rdptr @era tx scriptPurpose) <*> pure (Alonzo.Data dat, exUnits)

eesUnusedKeyPairs :: Functor f => (Word64 -> f Word64) -> EraElaboratorState era -> f (EraElaboratorState era)
eesUnusedKeyPairs a2fb s = (\b -> s {_eesUnusedKeyPairs = b}) <$> a2fb (_eesUnusedKeyPairs s)

eesKeys :: Lens' (EraElaboratorState era) (Map.Map (ModelAddress (ScriptFeature (EraFeatureSet era))) (TestAddrInfo era))
eesKeys a2fb s = (\b -> s {_eesKeys = b}) <$> a2fb (_eesKeys s)

eesPools :: Lens' (EraElaboratorState era) (Map.Map ModelPoolId (TestPoolKey era))
eesPools a2fb s = (\b -> s {_eesPools = b}) <$> a2fb (_eesPools s)

eesTxIds :: Functor f => (Map.Map ModelTxId (Shelley.TxId (Crypto era)) -> f (Map.Map ModelTxId (Shelley.TxId (Crypto era)))) -> EraElaboratorState era -> f (EraElaboratorState era)
eesTxIds a2fb s = (\b -> s {_eesTxIds = b}) <$> a2fb (_eesTxIds s)

eesCurrentEpoch :: Functor f => (EpochNo -> f EpochNo) -> EraElaboratorState era -> f (EraElaboratorState era)
eesCurrentEpoch a2fb s = (\b -> s {_eesCurrentEpoch = b}) <$> a2fb (_eesCurrentEpoch s)

eesStakeCredentials :: Lens' (EraElaboratorState era) (Map.Map (StakeCredential (Crypto era)) (ModelAddress (EraScriptFeature era)))
eesStakeCredentials a2fb s = (\b -> s {_eesStakeCredentials = b}) <$> a2fb (_eesStakeCredentials s)

eesUTxOs :: Lens' (EraElaboratorState era) (Map.Map ModelUTxOId (TestUTxOInfo era))
eesUTxOs a2fb s = (\b -> s {_eesUTxOs = b}) <$> a2fb (_eesUTxOs s)

eesCurrentSlot :: Lens' (EraElaboratorState era) SlotNo
eesCurrentSlot a2fb s = (\b -> s {_eesCurrentSlot = b}) <$> a2fb (_eesCurrentSlot s)

data TestAddrInfo era = TestAddrInfo
  { _taiAddr :: Addr (Crypto era),
    _taiPmt :: TestCredentialInfo 'Payment era,
    _taiStk :: TestCredentialInfo 'Staking era
  }

deriving instance Eq (Core.Script era) => Eq (TestAddrInfo era)

deriving instance Ord (Core.Script era) => Ord (TestAddrInfo era)

deriving instance (C.Crypto (Crypto era), Show (Core.Script era)) => Show (TestAddrInfo era)

data TestCredentialInfo k era = TestCredentialInfo
  { _tciCred :: Credential k (Crypto era),
    _tciKey :: TestKey k era
  }

deriving instance Eq (Core.Script era) => Eq (TestCredentialInfo k era)

deriving instance Ord (Core.Script era) => Ord (TestCredentialInfo k era)

deriving instance (C.Crypto (Crypto era), Show (Core.Script era)) => Show (TestCredentialInfo k era)

data TestKey k era
  = TestKey_Keyed (TestKeyKeyed k (Crypto era))
  | TestKey_Script (TestKeyScript era)

deriving instance Eq (Core.Script era) => Eq (TestKey k era)

deriving instance Ord (Core.Script era) => Ord (TestKey k era)

deriving instance (C.Crypto (Crypto era), Show (Core.Script era)) => Show (TestKey k era)

data TestKeyKeyed (k :: KeyRole) c = TestKeyKeyed
  { _tkkKeyPair :: KeyPair k c,
    _tkkKeyHash :: KeyHash k c
  }

instance Eq (TestKeyKeyed k c) where (==) = (==) `on` _tkkKeyHash

instance Ord (TestKeyKeyed k c) where compare = compare `on` _tkkKeyHash

deriving instance C.Crypto c => Show (TestKeyKeyed k c)

data TestKeyScript era = TestKeyScript (Core.Script era) (ScriptHash (Crypto era))

deriving instance Eq (Core.Script era) => Eq (TestKeyScript era)

deriving instance Ord (Core.Script era) => Ord (TestKeyScript era)

deriving instance Show (Core.Script era) => Show (TestKeyScript era)

elaborateModelAddress ::
  forall era proxy.
  ElaborateEraModel era =>
  proxy era ->
  Word64 ->
  ModelAddress (EraScriptFeature era) ->
  TestAddrInfo era
elaborateModelAddress _ seed (ModelAddress _) =
  let keyPair@(pmtKey, stakeKey) = mkKeyPairs @(Crypto era) seed
      pmtHash = hashKey $ vKey pmtKey
      stakeHash = hashKey $ vKey stakeKey
   in TestAddrInfo
        (toAddr Testnet keyPair)
        (TestCredentialInfo (KeyHashObj pmtHash) (TestKey_Keyed $ TestKeyKeyed pmtKey pmtHash))
        (TestCredentialInfo (KeyHashObj stakeHash) (TestKey_Keyed $ TestKeyKeyed stakeKey stakeHash))
elaborateModelAddress proxy _ (ModelScriptAddress ms) =
  let realPolicy = makePlutusScript proxy (SupportsPlutus $ elaborateModelScript ms)
      pmtHash = hashScript @era realPolicy
      stakeHash = hashScript @era realPolicy
   in TestAddrInfo
        (Addr Testnet (ScriptHashObj pmtHash) (StakeRefBase $ ScriptHashObj stakeHash))
        (TestCredentialInfo (ScriptHashObj pmtHash) (TestKey_Script $ TestKeyScript realPolicy pmtHash))
        (TestCredentialInfo (ScriptHashObj stakeHash) (TestKey_Script $ TestKeyScript realPolicy stakeHash))

testStakeCredential ::
  TestAddrInfo era ->
  StakeCredential (Crypto era)
testStakeCredential = _tciCred . _taiStk

-- | get the TestKeyPair for a ModelAddress
getKeyPairForImpl ::
  forall m era proxy.
  ( MonadState (EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  proxy era ->
  ModelAddress (EraScriptFeature era) ->
  m (TestAddrInfo era)
getKeyPairForImpl proxy mAddr = do
  st <- use id
  case Map.lookup mAddr (_eesKeys st) of
    Just k -> pure k
    Nothing -> do
      unusedKeyPairId <- eesUnusedKeyPairs <<%= succ
      let k = elaborateModelAddress proxy unusedKeyPairId mAddr
      eesKeys . at mAddr .= Just k
      eesStakeCredentials . at (testStakeCredential k) .= Just mAddr
      pure k

getPmtKeyFor ::
  forall m era proxy.
  ( MonadState (EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  proxy era ->
  ModelAddress (EraScriptFeature era) ->
  m (TestKey 'Payment era)
getPmtKeyFor proxy mAddr = _tciKey . _taiPmt <$> getKeyPairForImpl proxy mAddr

getStakeKeyFor ::
  forall m era proxy.
  ( MonadState (EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  proxy era ->
  ModelAddress (EraScriptFeature era) ->
  m (TestKey 'Staking era)
getStakeKeyFor proxy mAddr = _tciKey . _taiStk <$> getKeyPairForImpl proxy mAddr

-- | get the Addr for a ModelAddress
getAddrFor ::
  forall m era proxy.
  ( MonadState (EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  proxy era ->
  ModelAddress (EraScriptFeature era) ->
  m (Addr (Crypto era))
getAddrFor proxy mAddr = _taiAddr <$> getKeyPairForImpl proxy mAddr

-- | get the Addr for a ModelAddress
getStakingKeyHashFor ::
  forall m era proxy.
  ( MonadState (EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  proxy era ->
  ModelAddress (EraScriptFeature era) ->
  m (KeyHash 'Staking (Crypto era))
getStakingKeyHashFor proxy maddr =
  let f (TestKey_Keyed (TestKeyKeyed _ k)) = k
      f _ = error $ ("unexpected script address:" <> show maddr)
   in f . _tciKey . _taiStk <$> getKeyPairForImpl proxy maddr

data TestPoolKey era = TestPoolKey
  { _tpkHash :: KeyHash 'StakePool (Crypto era),
    _tpkVRFHash :: Hash.Hash (C.HASH (Crypto era)) (Cardano.Crypto.VRF.Class.VerKeyVRF (C.VRF (Crypto era))),
    _tpkKey :: KeyPair 'StakePool (Crypto era)
  }

instance Eq (TestPoolKey era) where
  a == b = compare a b == EQ

instance Ord (TestPoolKey era) where
  compare =
    on compare _tpkHash
      <> on compare _tpkVRFHash

deriving instance (C.Crypto (Crypto era)) => Show (TestPoolKey era)

getTestPoolKeyImpl ::
  ( MonadState (EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  proxy era ->
  ModelPoolId ->
  m (TestPoolKey era)
getTestPoolKeyImpl proxy poolId = do
  st <- use id
  case Map.lookup poolId (_eesPools st) of
    Just k -> pure k
    Nothing -> do
      unusedKeyPairId <- eesUnusedKeyPairs <<%= succ
      let k = elaboratePoolId proxy unusedKeyPairId poolId
      eesPools . at poolId .= Just k
      pure k

elaboratePoolId ::
  forall era proxy.
  ( ElaborateEraModel era
  ) =>
  proxy era ->
  Word64 ->
  ModelPoolId ->
  TestPoolKey era
elaboratePoolId _ seed (ModelPoolId _) =
  let {- vrf@ -}
      (_, vrf') = mkVRFKeyPair @(C.VRF (Crypto era)) (RawSeed 1 0 0 0 seed)
      poolKey@(KeyPair _ _) = uncurry KeyPair . swap . mkKeyPair @(Crypto era) $ RawSeed 1 1 0 0 seed
      poolHash = hashKey $ vKey poolKey
   in TestPoolKey
        { _tpkHash = poolHash,
          _tpkVRFHash = hashVerKeyVRF vrf',
          _tpkKey = poolKey
        }

liftModelAddress ::
  ModelAddress ('TyScriptFeature 'False 'False) ->
  ModelAddress a
liftModelAddress (ModelAddress a) = ModelAddress a

-- | get the StakePool hash for a ModelAddress
getScriptWitnessFor ::
  forall m era proxy.
  ( MonadState (EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  proxy era ->
  ModelAddress (EraScriptFeature era) ->
  m (KeyHash 'Witness (Crypto era))
getScriptWitnessFor proxy maddr0 = case filterModelAddress (eraFeatureSet (Proxy @era)) maddr0 of
  Nothing -> error $ "unexpectedly unupgradable address: " <> show maddr0
  Just maddr ->
    let f (TestKey_Keyed (TestKeyKeyed _ x)) = x
        f (TestKey_Script _) = error $ "unexpected script addr in timelock" <> show maddr0
     in coerceKeyRole @_ @_ @(Crypto era) . f . _tciKey . _taiPmt <$> getKeyPairForImpl proxy maddr

-- | get the StakeCredential for a ModelAddress
getStakeCredenetialFor ::
  forall m era proxy.
  ( MonadState (EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  proxy era ->
  ModelAddress (EraScriptFeature era) ->
  m (StakeCredential (Crypto era))
getStakeCredenetialFor proxy maddr = _tciCred . _taiStk <$> getKeyPairForImpl proxy maddr

instance Default (EraElaboratorState era) where
  def =
    EraElaboratorState
      { _eesUnusedKeyPairs = 1,
        _eesKeys = Map.empty,
        _eesPools = Map.empty,
        _eesTxIds = Map.empty,
        _eesCurrentEpoch = 0,
        _eesCurrentSlot = 0,
        _eesStakeCredentials = Map.empty,
        _eesUTxOs = Map.empty
      }

tellMintWitness ::
  ( ElaborateEraModel era,
    MonadState (NewEpochState era, EraElaboratorState era) m
  ) =>
  proxy era ->
  ModelScript (EraScriptFeature era) ->
  ScriptHash (Crypto era) ->
  Core.Script era ->
  Writer.WriterT (EraElaboratorTxAccum era) m ()
tellMintWitness _ modelPolicy policyHash realPolicy = do
  Writer.tell $
    mempty
      { _eesScripts = ElaboratedScriptsCache $ Map.singleton policyHash realPolicy
      }
  myKeys :: [TestKey 'Payment era] <- case modelPolicy of
    ModelScript_PlutusV1 _s1 ->
      pure [TestKey_Script $ TestKeyScript realPolicy policyHash]
    ModelScript_Timelock tl -> for (modelScriptNeededSigs tl) $ \mAddr -> do
      State.state $ State.runState $ zoom _2 $ getPmtKeyFor (Proxy :: Proxy era) mAddr
  for_ myKeys $ tellWitness (Minting $ PolicyID policyHash)

noScriptAction ::
  Applicative m =>
  proxy era ->
  ModelScript (EraScriptFeature era) ->
  ScriptHash (Crypto era) ->
  Core.Script era ->
  m ()
noScriptAction _ _ _ _ = pure ()

lookupModelValue ::
  forall era valF m.
  ( Val.Val (ElaborateValueType valF (Crypto era)),
    MonadState (NewEpochState era, EraElaboratorState era) m,
    ElaborateEraModel era
  ) =>
  (Proxy era -> ModelScript (EraScriptFeature era) -> ScriptHash (Crypto era) -> Core.Script era -> m ()) ->
  ModelValueVars (EraFeatureSet era) valF ->
  m (ElaborateValueType valF (Crypto era))
lookupModelValue scriptAction = \case
  ModelValue_Reward maddr -> do
    allRewards <- observeRewards <$> State.get
    pure $ Val.inject $ maybe (Coin 0) id $ Map.lookup maddr allRewards
  ModelValue_MA (Coin ad) x -> case reifyValueConstraint @era of
    ExpectedValueTypeC_MA -> do
      x' <- Writer.execWriterT $
        ifor_ (Compose x) $ \(modelPolicy, assetName) qty -> do
          realPolicy :: Core.Script era <- State.state $ elaborateScript modelPolicy
          let policyHash = hashScript @era realPolicy
          lift $ scriptAction (Proxy @era) modelPolicy policyHash realPolicy

          Writer.tell $ [(PolicyID policyHash, assetName, qty)]
      pure $ valueFromList ad x'

mkTxOut ::
  forall m era.
  ( MonadState (NewEpochState era, EraElaboratorState era) m,
    Except.MonadError (ElaborateBlockError era) m,
    Era era,
    UsesTxOut era,
    ElaborateEraModel era
  ) =>
  ModelTxId ->
  Natural ->
  ModelUTxOId ->
  ModelTxOut (EraFeatureSet era) ->
  m (Core.TxOut era)
mkTxOut mtxId idx mutxoId (ModelTxOut mAddr (ModelValue mValue) mDat) = (=<<) Except.liftEither $
  State.state $
    State.runState $
      Except.runExceptT $ do
        addr <- zoom _2 $ getAddrFor (Proxy :: Proxy era) mAddr
        val :: Core.Value era <- either (Except.throwError . ElaborateBlockError_TxValue @era) pure =<< evalModelValue (lookupModelValue noScriptAction) mValue
        let txo = makeTxOut (Proxy :: Proxy era) addr val
            (dat, txo') = case mDat of
              NoPlutusSupport () -> (SNothing, txo)
              SupportsPlutus Nothing -> (SNothing, txo)
              SupportsPlutus (Just dat') ->
                let d = Alonzo.Data dat'
                    dh = (Alonzo.hashData @era $ d)
                 in (SJust (dh, d), makeExtendedTxOut (Proxy @era) txo $ SupportsPlutus dh)
        _2 . eesUTxOs . at mutxoId .= Just (TestUTxOInfo (Right (mtxId, idx)) mAddr dat)
        pure txo'

mkTxIn ::
  forall m era.
  ( MonadState (EraElaboratorState era) m,
    Writer.MonadWriter (EraElaboratorTxAccum era) m,
    ElaborateEraModel era
  ) =>
  ModelTxIn ->
  m (Set.Set (Shelley.TxIn (Crypto era)))
mkTxIn moid = do
  ses <- use id
  mutxo <- use $ eesUTxOs . at moid
  case mutxo of
    -- TODO: handle missing txnIds more gracefully?
    Nothing -> pure mempty
    Just (TestUTxOInfo mutxo' mAddr mDat) -> do
      myKeys <- getPmtKeyFor (Proxy :: Proxy era) mAddr

      for_ mDat $ \(k, v) ->
        Writer.tell $
          mempty
            { _eetaDats = Alonzo.TxDats $ Map.singleton k v
            }

      txins <- case mutxo' of
        Left txin -> pure (Set.singleton txin)
        Right (mtxId, idx) ->
          pure . maybe Set.empty Set.singleton $ Shelley.TxIn <$> Map.lookup mtxId (_eesTxIds ses) <*> pure idx
      for_ txins $ \txin -> tellWitness (Spending txin) myKeys
      pure txins

tellWitnessKey ::
  forall kr m era.
  Writer.MonadWriter (EraElaboratorTxAccum era) m =>
  KeyPair kr (Crypto era) ->
  m ()
tellWitnessKey keyP = do
  Writer.tell $
    mempty
      { _eesPendingWitnessKeys = [coerceKeyRole @_ @_ @(Crypto era) keyP]
      }

-- | accumulate a witness while elaborating a ModelTx.
tellWitness ::
  forall kr m era.
  Writer.MonadWriter (EraElaboratorTxAccum era) m =>
  ScriptPurpose (Crypto era) ->
  TestKey kr era ->
  m ()
tellWitness _ (TestKey_Keyed (TestKeyKeyed keyP _)) = tellWitnessKey keyP
tellWitness sp (TestKey_Script (TestKeyScript realPolicy policyHash)) = do
  Writer.tell $
    mempty
      { _eesRedeemers = pure $ TestRedeemer sp (PlutusTx.I 1) (ExUnits 10 10),
        _eesScripts = ElaboratedScriptsCache $ Map.singleton policyHash realPolicy
      }

-- | return all accumulated witnesses.
elaborateWitnesses ::
  forall kr proxy era.
  ( DSIGN.Signable (C.DSIGN (Crypto era)) (Hash.Hash (C.HASH (Crypto era)) Shelley.EraIndependentTxBody),
    C.Crypto (Crypto era)
  ) =>
  proxy era ->
  [KeyPair kr (Crypto era)] ->
  SafeHash (Crypto era) Shelley.EraIndependentTxBody ->
  (Set.Set (Shelley.WitVKey 'Witness (Crypto era)))
elaborateWitnesses _ witness bodyHash = flip foldMap witness $ \keyP ->
  Set.singleton $ UTxO.makeWitnessVKey bodyHash keyP

-- | lens to focus the ledger state from that used by ApplyBlock to that used by
-- ApplyTx
mempoolState :: Functor f => (MempoolState era -> f (MempoolState era)) -> (NewEpochState era -> f (NewEpochState era))
mempoolState = \a2b s ->
  let nesEs = LedgerState.nesEs s
      esLState = LedgerState.esLState nesEs

      mkNES (utxoState, delegationState) =
        s
          { LedgerState.nesEs =
              nesEs
                { LedgerState.esLState =
                    esLState
                      { LedgerState._utxoState = utxoState,
                        LedgerState._delegationState = delegationState
                      }
                }
          }
   in mkNES <$> a2b (mkMempoolState s)
{-# INLINE mempoolState #-}

data ElaborateBlockError era
  = ElaborateBlockError_ApplyTx (ApplyTxError era)
  | ElaborateBlockError_Fee (ModelValueError Coin)
  | ElaborateBlockError_TxValue (ModelValueError (Core.Value era))

deriving instance
  ( Show (ApplyTxError era),
    Show (Core.Value era)
  ) =>
  Show (ElaborateBlockError era)

data TxBodyArguments era = TxBodyArguments
  { -- | ttl
    _txBodyArguments_ttl :: !SlotNo,
    -- | fee
    _txBodyArguments_fee :: !Coin,
    -- | inputs
    _txBodyArguments_inputs :: !(Set.Set (Shelley.TxIn (Crypto era))),
    -- | outputs
    _txBodyArguments_outputs :: !(StrictSeq.StrictSeq (Core.TxOut era)),
    -- | Deleg certs.
    _txBodyArguments_delegCerts :: !(StrictSeq.StrictSeq (DCert (Crypto era))),
    -- | withdrawals
    _txBodyArguments_withdrawals :: !(Shelley.Wdrl (Crypto era)),
    -- | mint
    _txBodyArguments_mint :: !(IfSupportsMint () (Core.Value era) (EraValueFeature era)),
    _txBodyArguments_redeemers :: !(IfSupportsPlutus () (StrictMaybe (Alonzo.Redeemers era, Alonzo.TxDats era)) (EraScriptFeature era)),
    -- | collateral
    _txBodyArguments_collateral :: !(IfSupportsPlutus () (Set.Set (Shelley.TxIn (Crypto era))) (EraScriptFeature era))
  }

data TxWitnessArguments era = TxWitnessArguments
  { _txWitnessArguments_vkey :: !(Set.Set (Shelley.WitVKey 'Witness (Crypto era))),
    _txWitnessArguments_scripts ::
      !( IfSupportsScript
           ()
           (Map.Map (ScriptHash (Crypto era)) (Core.Script era))
           (EraScriptFeature era)
       ),
    _txWitnessArguments_redeemers ::
      !( IfSupportsPlutus
           ()
           (Alonzo.Redeemers era, Alonzo.TxDats era)
           (EraScriptFeature era)
       )
  }

mkTxWitnessArguments ::
  forall era m.
  ( Monad m,
    C.Crypto (Crypto era),
    ElaborateEraModel era,
    HasField "certs" (Core.TxBody era) (StrictSeq.StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set.Set (Shelley.TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Shelley.Wdrl (Crypto era)),
    DSIGN.Signable (C.DSIGN (Crypto era)) (Hash.Hash (C.HASH (Crypto era)) Shelley.EraIndependentTxBody)
  ) =>
  NewEpochState era ->
  EraElaboratorTxAccum era ->
  TxBodyArguments era ->
  m (Core.TxBody era, TxWitnessArguments era)
mkTxWitnessArguments nes (EraElaboratorTxAccum pendingWits (ElaboratedScriptsCache pendingScripts) pendingRedeemers pendingDats) txBodyArguments = do
  let fakeTxBody = makeTxBody @era nes $ txBodyArguments
  redeemers <- case reifySupportsPlutus (Proxy @(EraScriptFeature era)) of
    NoPlutusSupport () -> pure (NoPlutusSupport ())
    SupportsPlutus () -> do
      case traverse (elaborateModelRedeemer fakeTxBody) pendingRedeemers of
        SNothing -> error "cant elaborate ptr"
        SJust xs -> do
          let redeemers = Alonzo.Redeemers $ Map.fromList xs
          pure (SupportsPlutus (redeemers, pendingDats))
  let bodyHash = hashAnnotated realTxBody
      realTxBody = case redeemers of
        SupportsPlutus (r, _)
          | not (Alonzo.nullRedeemers r) ->
            makeTxBody @era nes $
              txBodyArguments
                { _txBodyArguments_redeemers = mapSupportsPlutus SJust redeemers
                }
          | otherwise -> fakeTxBody
        NoPlutusSupport () -> fakeTxBody
      witVKey = elaborateWitnesses (Proxy :: Proxy era) pendingWits bodyHash

      scripts :: IfSupportsScript () (Map.Map (ScriptHash (Crypto era)) (Core.Script era)) (EraScriptFeature era)
      scripts = case reifyScriptFeature (Proxy @(EraScriptFeature era)) of
        ScriptFeatureTag_None -> NoScriptSupport ()
        tag@ScriptFeatureTag_Simple -> SupportsScript tag pendingScripts
        tag@ScriptFeatureTag_PlutusV1 -> SupportsScript tag pendingScripts

  pure $
    (,) realTxBody $
      TxWitnessArguments
        { _txWitnessArguments_vkey = witVKey,
          _txWitnessArguments_scripts = scripts,
          _txWitnessArguments_redeemers = redeemers
        }

type EraValueFeature era = ValueFeature (EraFeatureSet era)

type EraScriptFeature era = ScriptFeature (EraFeatureSet era)

class
  ( ElaborateValueType (EraValueFeature era) (Crypto era) ~ Core.Value era,
    KnownRequiredFeatures (EraFeatureSet era),
    ValidateScript era
  ) =>
  ElaborateEraModel era
  where
  type EraFeatureSet era :: FeatureSet
  eraFeatureSet :: proxy era -> FeatureTag (EraFeatureSet era)

  reifyValueConstraint ::
    ExpectedValueTypeC era

  -- | Apply a ModelBlock to a specific era's ledger.
  elaborateBlock ::
    Globals ->
    ModelBlock (EraFeatureSet era) ->
    (NewEpochState era, EraElaboratorState era) ->
    ( Either (ElaborateBlockError era) (),
      (NewEpochState era, EraElaboratorState era)
    )
  default elaborateBlock ::
    ( ApplyBlock era,
      ApplyTx era
    ) =>
    Globals ->
    ModelBlock (EraFeatureSet era) ->
    (NewEpochState era, EraElaboratorState era) ->
    ( Either (ElaborateBlockError era) (),
      (NewEpochState era, EraElaboratorState era)
    )
  elaborateBlock globals =
    State.runState . Except.runExceptT . \case
      ModelBlock mslot mtxSeq -> do
        currentEpoch <- use $ _2 . eesCurrentEpoch
        let slot = runIdentity (epochInfoFirst ei currentEpoch) + mslot
            ei = epochInfo globals
            ttl = succ slot

        unless (currentEpoch == runIdentity (epochInfoEpoch ei slot)) $ error $ "model slot out of range: " <> show mslot
        _2 . eesCurrentSlot .= slot
        -- tick the model
        lift $ zoom _1 $ State.state $ \nes0 -> ((), applyTick globals nes0 slot)
        txSeq ::
          [Core.Tx era] <-
          for mtxSeq $ \tx -> Except.ExceptT $ State.state $ elaborateTx (Proxy :: Proxy era) globals ttl tx

        mempoolEnv <- (\(nes0, _) -> mkMempoolEnv nes0 slot) <$> get

        -- apply the transactions.
        for_ txSeq $ \tx -> do
          (nes0, ems) <- get
          (mps', _) <- liftApplyTxError $ applyTx globals mempoolEnv (view mempoolState nes0) tx

          let nes1 = set mempoolState mps' nes0
          put (nes1, ems)

        pure ()

  -- | get a NewEpochState from genesis conditions.
  elaborateInitialState ::
    ShelleyGenesis era ->
    AdditionalGenesisConfig era ->
    -- | Initial coins present at time of genesis.  Each address will have its full balance in a single UTxO from a single "transaction"
    [(ModelUTxOId, ModelAddress (EraScriptFeature era), Coin)] ->
    EraElaboratorState era ->
    ( NewEpochState era,
      EraElaboratorState era
    )
  default elaborateInitialState ::
    ( CanStartFromGenesis era
    ) =>
    ShelleyGenesis era ->
    AdditionalGenesisConfig era ->
    [(ModelUTxOId, ModelAddress (EraScriptFeature era), Coin)] ->
    EraElaboratorState era ->
    ( NewEpochState era,
      EraElaboratorState era
    )
  elaborateInitialState sg additionalGenesesConfig genesisAccounts = State.runState $ do
    utxo0 <- fmap Map.fromList $
      for genesisAccounts $ \(oid, mAddr, coins) -> do
        addr <- getAddrFor (Proxy :: Proxy era) mAddr
        eesUTxOs . at oid .= Just (TestUTxOInfo (Left (initialFundsPseudoTxIn addr)) mAddr SNothing)
        pure (addr, coins)

    pure $ initialState sg {sgInitialFunds = Map.unionWith const utxo0 $ sgInitialFunds sg} additionalGenesesConfig

  makeTimelockScript ::
    proxy era ->
    IfSupportsTimelock Void (Timelock (Crypto era)) (EraScriptFeature era) ->
    Core.Script era

  makePlutusScript ::
    proxy era ->
    IfSupportsPlutus Void (Alonzo.Script era) (EraScriptFeature era) ->
    Core.Script era

  makeExtendedTxOut ::
    proxy era ->
    Core.TxOut era ->
    IfSupportsPlutus Void (Alonzo.DataHash (Crypto era)) (EraScriptFeature era) ->
    Core.TxOut era

  elaborateScript ::
    ModelScript (EraScriptFeature era) ->
    (NewEpochState era, EraElaboratorState era) ->
    ( (Core.Script era),
      (NewEpochState era, EraElaboratorState era)
    )
  default elaborateScript ::
    ModelScript (EraScriptFeature era) ->
    (NewEpochState era, EraElaboratorState era) ->
    ( (Core.Script era),
      (NewEpochState era, EraElaboratorState era)
    )
  elaborateScript ms0 = State.runState $ case ms0 of
    ModelScript_PlutusV1 ms ->
      pure $ makePlutusScript (Proxy :: Proxy era) (SupportsPlutus $ elaborateModelScript ms)
    ModelScript_Timelock ms -> do
      x <- elaborateModelTimelock (zoom _2 . getScriptWitnessFor (Proxy :: Proxy era) . liftModelAddress) ms
      pure $ makeTimelockScript (Proxy :: Proxy era) $ SupportsTimelock x

  -- | Construct a TxBody from some elaborated inputs.
  makeTxBody ::
    NewEpochState era ->
    TxBodyArguments era ->
    Core.TxBody era

  -- | apply a single Model transaction to a specific eras ledger
  elaborateTx ::
    proxy era ->
    Globals ->
    -- | ttl
    SlotNo ->
    ModelTx (EraFeatureSet era) ->
    (NewEpochState era, EraElaboratorState era) ->
    ( Either (ElaborateBlockError era) (Core.Tx era),
      (NewEpochState era, EraElaboratorState era)
    )
  default elaborateTx ::
    ( DSIGN.Signable (C.DSIGN (Crypto era)) (Hash.Hash (C.HASH (Crypto era)) Shelley.EraIndependentTxBody),
      UsesTxOut era,
      HasField "inputs" (Core.TxBody era) (Set.Set (Shelley.TxIn (Crypto era))),
      HasField "wdrls" (Core.TxBody era) (Shelley.Wdrl (Crypto era)),
      HasField "certs" (Core.TxBody era) (StrictSeq.StrictSeq (DCert (Crypto era)))
    ) =>
    proxy era ->
    Globals ->
    SlotNo ->
    ModelTx (EraFeatureSet era) ->
    (NewEpochState era, EraElaboratorState era) ->
    ( Either (ElaborateBlockError era) (Core.Tx era),
      (NewEpochState era, EraElaboratorState era)
    )
  elaborateTx proxy _ maxTTL (ModelTx mtxId mtxInputs mtxOutputs (ModelValue mtxFee) mtxDCert mtxWdrl mtxMint mtxCollateral) = State.runState $
    Except.runExceptT $ do
      (txBodyArguments, txAccum) <- Writer.runWriterT $ do
        let liftEvalModelValue ::
              forall e a.
              (e -> ElaborateBlockError era) ->
              Writer.WriterT (EraElaboratorTxAccum era) (State.State (NewEpochState era, EraElaboratorState era)) (Either e a) ->
              Writer.WriterT
                (EraElaboratorTxAccum era)
                ( Except.ExceptT
                    (ElaborateBlockError era)
                    (State.State (NewEpochState era, EraElaboratorState era))
                )
                a
            liftEvalModelValue onErr xs =
              Writer.WriterT $
                Except.ExceptT $
                  fmap (\(x, y) -> either (Left . onErr) (Right . (,y)) x) $
                    Writer.runWriterT $
                      xs

        outs <- ifor mtxOutputs $ \idx (oid, o) -> mkTxOut mtxId (toEnum @Natural idx) oid o
        ins :: Set.Set (Shelley.TxIn (Crypto era)) <- zoom _2 $ fmap fold $ traverse mkTxIn $ Set.toList mtxInputs
        cins <- traverseSupportsPlutus (zoom _2 . fmap fold . traverse mkTxIn . Set.toList) mtxCollateral
        dcerts <- traverse (mkDCerts (Proxy :: Proxy era)) mtxDCert
        wdrl :: Map.Map (RewardAcnt (Crypto era)) Coin <-
          fmap Map.fromList $
            for (Map.toList mtxWdrl) $ \(mAddr, ModelValue mqty) -> do
              stakeCredential <- zoom _2 $ getStakeCredenetialFor proxy mAddr
              stakeKey <- zoom _2 $ getStakeKeyFor proxy mAddr
              let ra = RewardAcnt Testnet stakeCredential
              tellWitness (Rewarding ra) stakeKey
              qty <- liftEvalModelValue ElaborateBlockError_Fee $ evalModelValue (lookupModelValue noScriptAction) mqty
              pure (ra, qty)
        fee :: Coin <-
          liftEvalModelValue ElaborateBlockError_Fee $
            evalModelValue (lookupModelValue noScriptAction) mtxFee

        mint ::
          IfSupportsMint () (Core.Value era) (EraValueFeature era) <-
          case reifyValueConstraint @era of
            ExpectedValueTypeC_Simple -> pure $ NoMintSupport ()
            ExpectedValueTypeC_MA -> case mtxMint of
              SupportsMint m' ->
                fmap SupportsMint $
                  liftEvalModelValue ElaborateBlockError_TxValue $
                    evalModelValue (lookupModelValue (tellMintWitness @era)) (unModelValue m')

        pure $
          TxBodyArguments
            { _txBodyArguments_ttl = maxTTL,
              _txBodyArguments_fee = fee,
              _txBodyArguments_inputs = ins,
              _txBodyArguments_outputs = StrictSeq.fromList outs,
              _txBodyArguments_delegCerts = StrictSeq.fromList dcerts,
              _txBodyArguments_withdrawals = Shelley.Wdrl wdrl,
              _txBodyArguments_mint = mint,
              _txBodyArguments_redeemers = ifSupportsPlutus (Proxy @(EraScriptFeature era)) () SNothing,
              _txBodyArguments_collateral = cins
            }

      nes <- State.gets fst
      (realTxBody, txWitnessArguments) <- mkTxWitnessArguments nes txAccum txBodyArguments

      _2 . eesTxIds . at mtxId .= Just (UTxO.txid @era realTxBody)
      pure $ makeTx proxy realTxBody txWitnessArguments

  -- | build a full tx from TxBody and set of witnesses.
  makeTx ::
    proxy era ->
    Core.TxBody era ->
    TxWitnessArguments era ->
    Core.Tx era

  -- | convert an expeced failure by the model to the concrete error that will
  -- be produced.
  toEraPredicateFailure ::
    ModelPredicateFailure (EraFeatureSet era) ->
    (NewEpochState era, EraElaboratorState era) ->
    Either (ModelValueError (Core.Value era)) (ApplyBlockTransitionError era)

  -- | apply the model New Epoch event to a specific eras ledger
  elaborateBlocksMade ::
    Globals ->
    ModelBlocksMade ->
    (NewEpochState era, EraElaboratorState era) ->
    ( BlocksMade (Crypto era),
      (NewEpochState era, EraElaboratorState era)
    )
  default elaborateBlocksMade ::
    ApplyBlock era =>
    Globals ->
    ModelBlocksMade ->
    (NewEpochState era, EraElaboratorState era) ->
    ( BlocksMade (Crypto era),
      (NewEpochState era, EraElaboratorState era)
    )
  elaborateBlocksMade globals (ModelBlocksMade mblocksMadeWeights) = State.runState $ do
    prevEpoch <- use $ _2 . eesCurrentEpoch
    epoch <- _2 . eesCurrentEpoch <%= succ
    let ei = epochInfo globals
        slotsInEpoch = runIdentity $ epochInfoSize ei prevEpoch

    let mblocksMade = repartition (fromIntegral slotsInEpoch) mblocksMadeWeights
    bs <- for (Map.toList mblocksMade) $ \(maddr, n) -> do
      poolKey <- zoom _2 $ _tpkHash <$> getTestPoolKeyImpl (Proxy :: Proxy era) maddr
      pure (poolKey, n)

    let bs' = BlocksMade $ Map.fromList bs
    _1 %= emulateBlocksMade bs'

    let firstOfNew = runIdentity $ epochInfoFirst ei epoch

        neededSlot =
          SlotNo (randomnessStabilisationWindow globals)
            + runIdentity (epochInfoFirst ei prevEpoch)

    currentSlot <- _2 . eesCurrentSlot <<.= firstOfNew

    unless (currentSlot > neededSlot) $
      zoom _1 $ State.state $ \nes0 -> ((), applyTick globals nes0 (neededSlot + 1))
    zoom _1 $ State.state $ \nes0 -> ((), applyTick globals nes0 firstOfNew)

    pure bs'

  -- | convert a model deleg certificate to a real DCert
  elaborateDCert ::
    proxy era ->
    ModelDCert (EraFeatureSet era) ->
    EraElaboratorState era ->
    ((DCert (Crypto era), EraElaboratorTxAccum era), EraElaboratorState era)
  default elaborateDCert ::
    proxy era ->
    ModelDCert (EraFeatureSet era) ->
    EraElaboratorState era ->
    ((DCert (Crypto era), EraElaboratorTxAccum era), EraElaboratorState era)
  elaborateDCert proxy mdc = State.runState . Writer.runWriterT $ do
    (dc, dcwits) <- Writer.runWriterT $ case mdc of
      ModelRegisterStake maddr ->
        DCertDeleg . RegKey
          <$> getStakeCredenetialFor proxy maddr
      ModelDeRegisterStake maddr ->
        DCertDeleg . DeRegKey
          <$> getStakeCredenetialFor proxy maddr
      ModelDelegate (ModelDelegation mdelegator mdelegatee) -> do
        dtor <- getStakeCredenetialFor proxy mdelegator
        dtee <- _tpkHash <$> getTestPoolKeyImpl proxy mdelegatee
        stakeKey <- getStakeKeyFor proxy mdelegator
        Writer.tell [stakeKey]
        pure $ (DCertDeleg . Delegate) $ Delegation dtor dtee
      ModelRegisterPool (ModelPoolParams mPoolId pledge cost margin mRAcnt mOwners) -> do
        TestPoolKey poolId poolVRF poolKey <- getTestPoolKeyImpl proxy mPoolId
        lift $ tellWitnessKey poolKey
        poolOwners <- Set.fromList <$> traverse (getStakingKeyHashFor proxy) mOwners
        for_ mOwners $ Writer.tell . pure <=< getStakeKeyFor proxy
        rAcnt <- RewardAcnt Testnet <$> getStakeCredenetialFor proxy mRAcnt
        pure $
          (DCertPool . RegPool) $
            PoolParams
              { _poolId = poolId,
                _poolVrf = poolVRF,
                _poolPledge = pledge,
                _poolCost = cost,
                _poolMargin = margin,
                _poolRAcnt = rAcnt,
                _poolOwners = poolOwners,
                _poolRelays = StrictSeq.empty,
                _poolMD = SNothing
              }
      ModelRetirePool maddr epochNo -> do
        TestPoolKey pool _ _ <- getTestPoolKeyImpl proxy maddr
        pure $ DCertPool $ RetirePool pool epochNo
    for_ dcwits $ tellWitness (Certifying dc)
    pure dc

-- TODO: maybe useful someday
-- ModelMIRCert srcPot mRewards ->
--   fmap ( DCertMir . Shelley.MIRCert srcPot . Shelley.StakeAddressesMIR . Map.fromList) $
--   for (Map.toList mRewards) $ \(maddr, reward) -> (,)
--     <$> getStakeCredenetialFor proxy maddr
--     <*> pure reward

class AsApplyTxError era e | e -> era where
  asApplyTxError :: Prism' e (ApplyTxError era)

instance AsApplyTxError era (ApplyTxError era) where asApplyTxError = id

instance AsApplyTxError era (ElaborateBlockError era) where
  asApplyTxError = prism ElaborateBlockError_ApplyTx $ \case
    ElaborateBlockError_ApplyTx x -> Right x
    x -> Left x

liftApplyTxError ::
  (Except.MonadError e m, AsApplyTxError era e) =>
  Except.Except (ApplyTxError era) a ->
  m a
liftApplyTxError = either (Except.throwError . review asApplyTxError) pure . Except.runExcept

mkDCerts ::
  (ElaborateEraModel era) =>
  proxy era ->
  ModelDCert (EraFeatureSet era) ->
  Writer.WriterT
    (EraElaboratorTxAccum era)
    ( Except.ExceptT
        (ElaborateBlockError era)
        ( State.StateT
            (NewEpochState era, EraElaboratorState era)
            Identity
        )
    )
    (DCert (Crypto era))
mkDCerts proxy x = Writer.WriterT . lift . zoom _2 . State.state $ elaborateDCert proxy x

-- | simulate blocks made in the current epoch.  this functions like ApplyBlock or
-- ApplyTx, but without presenting real blocks to the ledger.  This is only
-- useful in testing the correctness of specific aspects of the ledger rather
-- than in normal use.
emulateBlocksMade ::
  forall era.
  BlocksMade (Crypto era) ->
  NewEpochState era ->
  NewEpochState era
emulateBlocksMade (BlocksMade newBlocksMade) nes@(LedgerState.NewEpochState {LedgerState.nesBcur = BlocksMade currentBlocksMade}) =
  nes {LedgerState.nesBcur = BlocksMade (Map.unionWith (+) newBlocksMade currentBlocksMade)}

-- | apply several epochs full of blocks to a ledger
elaborateBlocks_ ::
  forall era.
  (ElaborateEraModel era) =>
  Globals ->
  [ModelEpoch (EraFeatureSet era)] ->
  (NewEpochState era, EraElaboratorState era) ->
  ( Either (ElaborateBlockError era) (),
    (NewEpochState era, EraElaboratorState era)
  )
elaborateBlocks_ globals = State.runState . Except.runExceptT . traverse_ f
  where
    f (ModelEpoch blocks blocksMade) = do
      for_ blocks (Except.ExceptT . State.state . elaborateBlock globals)
      _ :: BlocksMade (Crypto era) <- lift $ State.state $ elaborateBlocksMade globals blocksMade
      pure ()

-- | get the current balance of rewards in terms of the model addresses that can
-- spend them.
observeRewards ::
  forall era.
  (NewEpochState era, EraElaboratorState era) ->
  Map.Map (ModelAddress (EraScriptFeature era)) Coin
observeRewards (nes, ems) =
  let creds = _eesStakeCredentials ems
   in Map.fromList $ do
        (a, b) <- Map.toList . LedgerState._rewards . LedgerState._dstate . LedgerState._delegationState . LedgerState.esLState $ LedgerState.nesEs nes
        a' <- case Map.lookup a creds of
          Just a' -> pure a'
          Nothing -> error $ "observeRewards: can't find " <> show a
        pure (a', b)

data ApplyBlockTransitionError era
  = ApplyBlockTransitionError_Tx (ApplyTxError era)

deriving instance
  ( Show (ApplyTxError era)
  ) =>
  Show (ApplyBlockTransitionError era)

deriving instance
  ( Eq (ApplyTxError era)
  ) =>
  Eq (ApplyBlockTransitionError era)

deriving instance
  ( Ord (ApplyTxError era)
  ) =>
  Ord (ApplyBlockTransitionError era)
