{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module STS.Utxow
  ( UTXOW
  ) where

import           Lens.Micro               ((^.))

import           Delegation.Certificates
import           Keys
import           LedgerState
import           PParams
import           Slot
import           UTxO

import           Control.State.Transition

import           STS.Utxo

data UTXOW

instance STS UTXOW where
  type State UTXOW = UTxOState
  type Signal UTXOW = TxWits
  type Environment UTXOW = (Slot, PParams, StakeKeys, StakePools, Dms)
  data PredicateFailure UTXOW = InvalidWitnessesUTXOW
                            | MissingWitnessesUTXOW
                            | UnneededWitnessesUTXOW
                            | UtxoFailure (PredicateFailure UTXO)
                                deriving (Eq, Show)
  transitionRules = [utxoWitnessed]
  initialRules = [initialLedgerStateUTXOW]

initialLedgerStateUTXOW :: InitialRule UTXOW
initialLedgerStateUTXOW = do
  IRC (slots, pp, stakeKeys, stakePools, dms) <- judgmentContext
  trans @UTXO $ IRC (slots, pp, stakeKeys, stakePools, dms)

utxoWitnessed :: TransitionRule UTXOW
utxoWitnessed = do
  TRC ((slot, pp, stakeKeys, stakePools, dms), u, txwits) <- judgmentContext
  verifiedWits txwits == Valid ?! InvalidWitnessesUTXOW
  enoughWits txwits dms u == Valid ?! MissingWitnessesUTXOW
  noUnneededWits txwits dms u == Valid ?! UnneededWitnessesUTXOW
  trans @UTXO $ TRC ((slot, pp, stakeKeys, stakePools, dms), u, txwits ^. body)

instance Embed UTXO UTXOW where
  wrapFailed = UtxoFailure
