{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}

module Shelley.Spec.Ledger.Bench.Rewards
  ( createRUpd,
    createRUpdWithProv,
    genChainInEpoch,
  )
where

import Cardano.Crypto.VRF (hashVerKeyVRF)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Slotting.EpochInfo
import Cardano.Slotting.Slot (EpochNo)
import Control.Monad.Reader (runReader, runReaderT)
import Control.Provenance (runProvM, runWithProvM)
import Control.State.Transition.Extended (IRC (..), TRC (..), applySTS)
import Data.Default.Class (Default (def))
import Data.Either (fromRight)
import Data.Functor.Identity (runIdentity)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import Cardano.Ledger.Address
  ( Addr (..),
    mkRwdAcnt,
  )
import Cardano.Ledger.BaseTypes
  ( Globals (activeSlotCoeff, securityParameter),
    Network (Testnet),
    StrictMaybe (..),
    epochInfo,
    truncateUnitInterval,
  )
import Cardano.Ledger.Credential (Credential (..), StakeReference (..))
import Shelley.Spec.Ledger.Genesis (ShelleyGenesisStaking (..))
import Cardano.Ledger.Keys (KeyHash, KeyRole (Staking))
import qualified Shelley.Spec.Ledger.LedgerState as LS
import Shelley.Spec.Ledger.PParams (PParams' (..))
import Shelley.Spec.Ledger.RewardProvenance (RewardProvenance)
import Shelley.Spec.Ledger.STS.Chain (CHAIN, ChainState, chainNes, totalAda)
import Shelley.Spec.Ledger.TxBody (PoolParams (..), TxOut (..))
import Shelley.Spec.Ledger.UTxO (UTxO (..))
import Test.QuickCheck (Gen)
import Test.Shelley.Spec.Ledger.BenchmarkFunctions (B, B_Crypto)
import Test.Shelley.Spec.Ledger.Generator.Block (genBlockWithTxGen)
import Test.Shelley.Spec.Ledger.Generator.Constants
  ( maxGenesisUTxOouts,
    minGenesisUTxOouts,
  )
import Test.Shelley.Spec.Ledger.Generator.Core
  ( AllIssuerKeys (..),
    GenEnv (..),
    ScriptSpace(..),
    geConstants,
    geKeySpace,
    ksStakePools,
  )
import Test.Shelley.Spec.Ledger.Generator.Presets (genEnv)
import Test.Shelley.Spec.Ledger.Generator.Trace.Chain
  ( mkGenesisChainState,
    registerGenesisStaking,
  )
import Test.Shelley.Spec.Ledger.Utils (testGlobals)

-- | Generate a chain state at a given epoch. Since we are only concerned about
-- rewards, this will populate the chain with empty blocks (only issued by the
-- original genesis delegates).
genChainInEpoch :: EpochNo -> Gen (ChainState B)
genChainInEpoch epoch = do
  genesisChainState <-
    fromRight (error "genChainState failed")
      <$> mkGenesisChainState @B (GenEnv ks (ScriptSpace [] [] Map.empty Map.empty) cs) (IRC ())
  -- Our genesis chain state contains no registered staking. Since we want to
  -- calculate a reward update, we will set some up.
  -- What do we want to do here?
  -- - We find all the addresses which are present in the initial UTxO, and
  --   register them all for staking
  -- - We group them into 50 groups (number of stake pools). The first one in
  --   each group becomes the pool owner, with pledge set to the value in that
  --   address.
  let initUtxo =
        LS._utxo
          . LS._utxoState
          . LS.esLState
          . LS.nesEs
          $ chainNes genesisChainState
      initUtxoAddrs =
        Map.elems
          . Map.mapMaybe (\(TxOut addr _) -> addrToKeyHash addr)
          . unUTxO
          $ initUtxo
      stakeMap =
        zip stakePools $
          chunk (length initUtxoAddrs `div` length stakePools) initUtxoAddrs

  let chainState =
        registerGenesisStaking
          (mkGenesisStaking stakeMap)
          genesisChainState
  -- Now run the empty block generator over the chain state until we hit the
  -- desired epoch.
  applyUntil
    chainState
    ( \x ->
        if (LS.nesEL $ chainNes x) >= epoch
          then Nothing
          else Just $ applyBlk x <$> genEmptyBlock x
    )
  where
    applyUntil :: Monad m => a -> (a -> Maybe (m a)) -> m a
    applyUntil x f = case f x of
      Nothing -> pure x
      Just x' -> x' >>= flip applyUntil f
    applyBlk cs' blk =
      (either err id) . flip runReader testGlobals
        . applySTS @(CHAIN B)
        $ TRC ((), cs', blk)
      where
        err :: Show a => a -> b
        err msg = error $ "Panic! applyBlk failed: " <> (show msg)
    ge = genEnv (Proxy @B)
    -- Small UTxO set; we just want enough to stake to pools
    cs =
      (geConstants ge)
        { minGenesisUTxOouts = 5000,
          maxGenesisUTxOouts = 5000
        }
    ks = geKeySpace ge
    genEmptyBlock = genBlockWithTxGen @B (\_ _ _ _ -> pure mempty) ge
    mkGenesisStaking stakeMap =
      ShelleyGenesisStaking
        { sgsPools =
            Map.fromList
              [ (hk, pp)
                | (AllIssuerKeys {vrf, hk}, (owner : _)) <- stakeMap,
                  let pp =
                        PoolParams
                          { _poolId = hk,
                            _poolVrf = hashVerKeyVRF $ snd vrf,
                            _poolPledge = Coin 1,
                            _poolCost = Coin 1,
                            _poolMargin = truncateUnitInterval 0,
                            _poolRAcnt = mkRwdAcnt Testnet $ KeyHashObj owner,
                            _poolOwners = Set.singleton owner,
                            _poolRelays = StrictSeq.empty,
                            _poolMD = SNothing
                          }
              ],
          sgsStake =
            Map.fromList
              [ (dlg, hk)
                | (AllIssuerKeys {hk}, dlgs) <- stakeMap,
                  dlg <- dlgs
              ]
        }
    stakePools = ksStakePools ks
    chunk :: Int -> [a] -> [[a]]
    chunk n _ | n <= 0 = []
    chunk n xs = go [] xs
      where
        go !acc [] = acc
        go !acc xs' = let (a, b) = splitAt n xs' in go (a : acc) b

    addrToKeyHash :: Addr crypto -> Maybe (KeyHash 'Staking crypto)
    addrToKeyHash (Addr _ _ (StakeRefBase (KeyHashObj kh))) = Just kh
    addrToKeyHash _ = Nothing

-- | Benchmark creating a reward update.
createRUpd ::
  Globals ->
  ChainState B ->
  LS.RewardUpdate B_Crypto
createRUpd globals cs =
  runIdentity $
    runReaderT
      (runProvM (LS.createRUpd epochSize bm es total asc k))
      globals
  where
    nes = chainNes cs
    bm = LS.nesBprev nes
    es = LS.nesEs nes
    total = totalAda cs
    epochSize =
      runIdentity $
        epochInfoSize (epochInfo globals) (LS.nesEL nes)
    asc = activeSlotCoeff globals
    k = securityParameter testGlobals

-- | Benchmark creating a reward update.
createRUpdWithProv ::
  Globals ->
  ChainState B ->
  (LS.RewardUpdate B_Crypto, RewardProvenance B_Crypto)
createRUpdWithProv globals cs =
  runIdentity $
    runReaderT
      (runWithProvM def (LS.createRUpd epochSize bm es total asc k))
      globals
  where
    nes = chainNes cs
    bm = LS.nesBprev nes
    es = LS.nesEs nes
    total = totalAda cs
    epochSize =
      runIdentity $
        epochInfoSize (epochInfo globals) (LS.nesEL nes)
    asc = activeSlotCoeff globals
    k = securityParameter testGlobals
