{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module STS.NewEpoch
  ( NEWEPOCH
  )
where

import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe (fromMaybe)

import           BaseTypes
import           Coin
import           EpochBoundary
import           LedgerState
import           PParams
import           Slot
import           TxData

import           STS.Epoch

import           Delegation.Certificates

import           Control.State.Transition

data NEWEPOCH hashAlgo dsignAlgo

instance STS (NEWEPOCH hashAlgo dsignAlgo) where
  type State (NEWEPOCH hashAlgo dsignAlgo) = NewEpochState hashAlgo dsignAlgo
  type Signal (NEWEPOCH hashAlgo dsignAlgo) = Epoch
  type Environment (NEWEPOCH hashAlgo dsignAlgo) = NewEpochEnv dsignAlgo
  data PredicateFailure (NEWEPOCH hashAlgo dsignAlgo)
    = EpochFailure (PredicateFailure (EPOCH hashAlgo dsignAlgo))
    deriving (Show, Eq)

  initialRules =
    [ pure $
      NewEpochState
        (Epoch 0)
        (mkNonce 0)
        (BlocksMade Map.empty)
        (BlocksMade Map.empty)
        emptyEpochState
        Nothing
        (PoolDistr Map.empty)
        Map.empty]
  transitionRules = [newEpochTransition]

newEpochTransition :: forall hashAlgo dsignAlgo . TransitionRule (NEWEPOCH hashAlgo dsignAlgo)
newEpochTransition = do
  TRC ( NewEpochEnv eta1 _s gkeys
      , src@(NewEpochState (Epoch eL') _ _ bcur es ru _pd _osched)
      , e@(Epoch e')) <- judgmentContext
  if eL' + 1 /= e'
    then pure src
    else do
      let es_ = case ru of
            Nothing  -> es
            Just ru' -> applyRUpd ru' es
      es' <- trans @(EPOCH hashAlgo dsignAlgo) $ TRC ((), es_, e)
      let EpochState acnt ss ls pp = es'
      let (Stake stake, delegs)    = _pstakeSet ss
      let Coin total               = Map.foldl (+) (Coin 0) stake
      let etaE                     = _extraEntropy pp
      let osched'                  = overlaySchedule e gkeys eta1 pp
      let es'' = EpochState acnt ss ls (pp { _extraEntropy = NeutralSeed })
      let sd = foldr
            (\(hk, Coin c) m ->
              Map.insertWith (+) hk (fromIntegral c / fromIntegral total) m
            )
            Map.empty
            [ (poolKey, Maybe.fromMaybe (Coin 0) (Map.lookup stakeKey stake))
            | (stakeKey, poolKey) <- Map.toList delegs
            ]
      let pd' = Map.intersectionWith (,) sd (Map.map _poolVrf (_poolsSS ss))
      pure $ NewEpochState e
                           (eta1 ⭒ etaE)
                           bcur
                           (BlocksMade Map.empty)
                           es''
                           Nothing
                           (PoolDistr pd')
                           osched'

instance Embed (EPOCH hashAlgo dsignAlgo) (NEWEPOCH hashAlgo dsignAlgo) where
  wrapFailed = EpochFailure
