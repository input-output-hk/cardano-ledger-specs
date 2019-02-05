{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

{-|
Module      : LedgerState
Description : Operational Rules

This module implements the operation rules for treating UTxO transactions ('TxWits')
as state transformations on a ledger state ('LedgerState'),
as specified in /A Simplified Formal Specification of a UTxO Ledger/.
-}


module LedgerState
  ( LedgerState(..)
  , Ix
  , DWState(..)
  , DState(..)
  , AccountState(..)
  , dstate
  , pstate
  , ptrs
  , PState(..)
  , avgs
  , LedgerValidation(..)
  , KeyPairs
  , UTxOState(..)
  , StakeShare(..)
  , Avgs(..)
  , mkStakeShare
  -- * state transitions
  , asStateTransition
  , asStateTransition'
  , delegatedStake
  , retirePools
  , emptyDelegation
  -- * Genesis State
  , genesisId
  , genesisState
  -- * Validation
  , ValidationError (..)
  , minfee
  -- lenses
  , utxoState
  , delegationState
  , pcs
  -- UTxOState
  , utxo
  , deposits
  , fees
  -- DelegationState
  , rewards
  , stKeys
  , delegations
  , stPools
  , pParams
  , retiring
  -- refunds
  , keyRefunds
  -- epoch boundary
  , movingAvg
  , poolRew
  , leaderRew
  , memberRew
  , indivRew
  , rewardOnePool
  , reward
  ) where

import           Control.Monad           (foldM)
import           Crypto.Hash             (hash)
import qualified Data.Map                as Map
import           Data.Maybe              (mapMaybe, fromMaybe)
import           Numeric.Natural         (Natural)
import           Data.Set                (Set)
import qualified Data.Set                as Set
import           Data.Ratio

import           Lens.Micro              ((^.), (&), (.~), (%~))
import           Lens.Micro.TH           (makeLenses)

import           Coin                    (Coin (..))
import           Slot                    (Slot (..), Epoch (..), (-*),
                                               epochFromSlot)
import           Keys
import           UTxO
import           PParams                 (PParams(..), minfeeA, minfeeB,
                                                 intervalValue, movingAvgWeight,
                                                 movingAvgExp, rho, tau,
                                                 slotsPerEpoch)
import           EpochBoundary

import           Delegation.Certificates (DCert (..), refund, getRequiredSigningKey, StakeKeys(..), StakePools(..), decayKey)
import           Delegation.StakePool    (Delegation (..), StakePool (..),
                                                     poolPubKey, poolSpec)

import Control.State.Transition

-- | Representation of a list of pairs of key pairs, e.g., pay and stake keys
type KeyPairs = [(KeyPair, KeyPair)]

-- | A ledger validation state consists of a ledger state 't' and the list of
-- validation errors that occurred from a valid 's' to reach 't'.
data LedgerValidation = LedgerValidation [ValidationError] LedgerState
                        deriving (Show, Eq)

-- |Validation errors represent the failures of a transaction to be valid
-- for a given ledger state.
data ValidationError =
  -- | The transaction inputs are not valid.
    BadInputs
  -- | The transaction has expired
  | Expired Slot Slot
  -- | Pool Retirement Certificate expired
  | RetirementCertExpired Slot Slot
  -- | The transaction fee is too small
  | FeeTooSmall Coin Coin
  -- | Value is not conserved
  | ValueNotConserved Coin Coin
  -- | Unknown reward account
  | IncorrectRewards
  -- | One of the transaction witnesses is invalid.
  | InvalidWitness
  -- | The transaction does not have the required witnesses.
  | MissingWitnesses
  -- | The transaction includes a redundant witness.
  | UnneededWitnesses
  -- | Missing Replay Attack Protection, at least one input must be spent.
  | InputSetEmpty
  -- | A stake key cannot be registered again.
  | StakeKeyAlreadyRegistered
  -- | A stake key must be registered to be used or deregistered.
  | StakeKeyNotRegistered
  -- | The stake key to which is delegated is not known.
  | StakeDelegationImpossible
  -- | Stake pool not registered for key, cannot be retired.
  | StakePoolNotRegisteredOnKey
    deriving (Show, Eq)

-- |The validity of a transaction, where an invalid transaction
-- is represented by list of errors.
data Validity = Valid | Invalid [ValidationError] deriving (Show, Eq)

instance Semigroup Validity where
  Valid <> b                 = b
  a <> Valid                 = a
  (Invalid a) <> (Invalid b) = Invalid (a ++ b)

instance Monoid Validity where
  mempty = Valid
  mappend = (<>)

type RewardAccounts = Map.Map RewardAcnt Coin

-- | Blocks made
newtype BlocksMade =
    BlocksMade (Map.Map HashKey Natural)
               deriving (Show, Eq)

-- | Performance moving averages
newtype Avgs =
  Avgs (Map.Map HashKey StakeShare)
        deriving (Show, Eq)

-- | StakeShare type
newtype StakeShare =
  StakeShare Rational
  deriving (Show, Ord, Eq)

-- | Construct an optional probability value
mkStakeShare :: Rational -> Maybe StakeShare
mkStakeShare p =
  if 0 <= p
    then Just $ StakeShare p
    else Nothing

data DState = DState
    {  -- |The active stake keys.
      _stKeys      :: StakeKeys
      -- |The active accounts.
    ,  _rewards    :: RewardAccounts
      -- |The current delegations.
    , _delegations :: Map.Map HashKey HashKey
      -- |The pointed to hash keys.
    , _ptrs        :: Map.Map Ptr HashKey
    } deriving (Show, Eq)

data PState = PState
    { -- |The active stake pools.
      _stPools     :: StakePools
      -- |The pool parameters.
    , _pParams     :: Map.Map HashKey StakePool
      -- |A map of retiring stake pools to the epoch when they retire.
    , _retiring    :: Map.Map HashKey Epoch
      -- |Moving average for key in epoch.
    , _avgs        :: Avgs
    } deriving (Show, Eq)

-- |The state associated with the current stake delegation.
data DWState =
    DWState
    {
      _dstate :: DState
    , _pstate :: PState
    } deriving (Show, Eq)

data AccountState = AccountState
  { _treasury   :: Coin
  , _reserves   :: Coin
  , _rewardPool :: Coin
  } deriving (Show, Eq)

emptyAccount :: AccountState
emptyAccount = AccountState (Coin 0) (Coin 0) (Coin 0)

emptyDelegation :: DWState
emptyDelegation =
    DWState emptyDState emptyPState

emptyDState :: DState
emptyDState = DState (StakeKeys Map.empty) Map.empty Map.empty Map.empty

emptyPState :: PState
emptyPState = PState (StakePools Map.empty) Map.empty Map.empty (Avgs Map.empty)

data UTxOState =
    UTxOState
    {
      _utxo      :: !UTxO
    , _deposits  :: Coin
    , _fees      :: Coin
    } deriving (Show, Eq)

-- |The state associated with a 'Ledger'.
data LedgerState =
  LedgerState
  { -- |The current unspent transaction outputs.
    _utxoState         :: !UTxOState
    -- |The current delegation state
  , _delegationState   :: !DWState
    -- |The current protocol constants.
  , _pcs               :: !PParams
    -- | The current transaction index in the current slot.
  , _txSlotIx          :: Ix
  , _currentSlot       :: Slot
  } deriving (Show, Eq)

makeLenses ''DWState
makeLenses ''DState
makeLenses ''PState
makeLenses ''UTxOState
makeLenses ''AccountState
makeLenses ''LedgerState

-- |The transaction Id for 'UTxO' included at the beginning of a new ledger.
genesisId :: TxId
genesisId = TxId $ hash (Tx Set.empty [] [] Map.empty (Coin 0) (Slot 0))

-- |Creates the ledger state for an empty ledger which
-- contains the specified transaction outputs.
genesisState :: PParams -> [TxOut] -> LedgerState
genesisState pc outs = LedgerState
  (UTxOState
    (UTxO $ Map.fromList
              [(TxIn genesisId idx, out) | (idx, out) <- zip [0..] outs])
    (Coin 0)
    (Coin 0))
  emptyDelegation
  pc
  0
  (Slot 0)

-- | Determine if the transaction has expired
current :: Tx -> Slot -> Validity
current tx slot =
    if tx ^. ttl < slot
    then Invalid [Expired (tx ^. ttl) slot]
    else Valid

-- | Determine if the input set of a transaction consumes at least one input,
-- else it would be possible to do a replay attack using this transaction.
validNoReplay :: Tx -> Validity
validNoReplay tx =
    if txins tx == Set.empty
    then Invalid [InputSetEmpty]
    else Valid

-- |Determine if the inputs in a transaction are valid for a given ledger state.
validInputs :: Tx -> UTxOState -> Validity
validInputs tx u =
  if txins tx `Set.isSubsetOf` dom (u ^. utxo)
    then Valid
    else Invalid [BadInputs]

-- |Implementation of abstract transaction size
txsize :: Tx -> Natural
txsize = toEnum . length . show

-- |Minimum fee calculation
minfee :: PParams -> Tx -> Coin
minfee pc tx = Coin $ pc ^. minfeeA * txsize tx + pc ^. minfeeB

-- |Determine if the fee is large enough
validFee :: PParams -> Tx -> Validity
validFee pc tx =
  if needed <= given
    then Valid
    else Invalid [FeeTooSmall needed given]
      where
        needed = minfee pc tx
        given  = tx ^. txfee

-- |Compute the lovelace which are created by the transaction
created :: StakePools -> PParams -> Tx -> Coin
created stakePools pc tx =
    balance (txouts tx) + tx ^. txfee + depositAmount pc stakePools tx

-- |Compute the key deregistration refunds in a transaction
keyRefunds :: PParams -> StakeKeys -> Tx -> Coin
keyRefunds pc (StakeKeys stkeys) tx =
  sum [refund' key | (RegKey key) <- tx ^. certs]
  where refund' key =
          case Map.lookup (hashKey key) stkeys of
            Nothing -> Coin 0
            Just s -> refund dval dmin lambda $ (tx ^. ttl) -* s
        (dval, dmin, lambda) = decayKey pc

-- |Compute the lovelace which are destroyed by the transaction
destroyed :: StakeKeys -> PParams -> Tx -> UTxOState -> Coin
destroyed stakeKeys pc tx u =
    balance (txins tx <| (u ^. utxo)) + refunds + withdrawals
  where
    refunds = keyRefunds pc stakeKeys tx
    withdrawals = sum $ tx ^. wdrls

-- |Determine if the balance of the ledger state would be effected
-- in an acceptable way by a transaction.
preserveBalance :: StakePools -> StakeKeys -> PParams -> Tx -> UTxOState -> Validity
preserveBalance stakePools stakeKeys pc tx u =
  if destroyed' == created'
    then Valid
    else Invalid [ValueNotConserved destroyed' created']
  where
    destroyed' = destroyed stakeKeys pc tx u
    created' = created stakePools pc tx

-- |Determine if the reward witdrawals correspond
-- to the rewards in the ledger state
correctWithdrawals :: RewardAccounts -> RewardAccounts -> Validity
correctWithdrawals accs withdrawals =
  if withdrawals `Map.isSubmapOf` accs
    then Valid
    else Invalid [IncorrectRewards]

-- |Collect the set of hashes of keys that needs to sign a
-- given transaction. This set consists of the txin owners,
-- certificate authors, and withdrawal reward accounts.
requiredSigners :: Tx -> UTxO -> Set HashKey
requiredSigners tx utxo' = inputAuthors `Set.union` wdrlAuthors `Set.union` certAuthors
  where
    inputAuthors = Set.foldr insertHK Set.empty (tx ^. inputs)
    insertHK txin hkeys =
      case txinLookup txin utxo' of
        Just (TxOut (AddrTxin pay _) _) -> Set.insert pay hkeys
        _                               -> hkeys

    wdrlAuthors = Set.map getRwdHK (Map.keysSet (tx ^. wdrls))

    certAuthors = Set.fromList (fmap getCertHK (tx ^. certs))
    getCertHK cert = hashKey $ getRequiredSigningKey cert

-- |Given a ledger state, determine if the UTxO witnesses in a given
-- transaction are correct.
verifiedWits :: TxWits -> Validity
verifiedWits (TxWits tx wits) =
  if all (verifyWit tx) wits
    then Valid
    else Invalid [InvalidWitness]

-- |Given a ledger state, determine if the UTxO witnesses in a given
-- transaction are sufficient.
-- We check that there are not more witnesses than inputs, if several inputs
-- from the same address are used, it is not strictly necessary to include more
-- than one witness.
enoughWits :: TxWits -> UTxOState -> Validity
enoughWits (TxWits tx wits) u =
  if requiredSigners tx (u ^. utxo) `Set.isSubsetOf` signers
    then Valid
    else Invalid [MissingWitnesses]
  where
    signers = Set.map (\(Wit vkey _) -> hashKey vkey) wits

-- |Check that there are no redundant witnesses.
noUnneededWits :: TxWits -> UTxOState -> Validity
noUnneededWits (TxWits tx wits) u =
  if signers `Set.isSubsetOf` requiredSigners tx (u ^. utxo)
    then Valid
    else Invalid [UnneededWitnesses]
  where
    signers = Set.map (\(Wit vkey _) -> hashKey vkey) wits

validRuleUTXO ::
    RewardAccounts -> StakePools -> StakeKeys -> PParams -> Slot -> Tx -> UTxOState -> Validity
validRuleUTXO accs stakePools stakeKeys pc slot tx u =
                          validInputs tx u
                       <> current tx slot
                       <> validNoReplay tx
                       <> validFee pc tx
                       <> preserveBalance stakePools stakeKeys pc tx u
                       <> correctWithdrawals accs (tx ^. wdrls)

validRuleUTXOW :: TxWits -> LedgerState -> Validity
validRuleUTXOW tx l = verifiedWits tx
                   <> enoughWits tx (l ^. utxoState)
                   <> noUnneededWits tx (l ^. utxoState)

validTx :: TxWits -> Slot -> LedgerState -> Validity
validTx tx slot l =
    validRuleUTXO  (l ^. delegationState . dstate . rewards)
                   (l ^. delegationState . pstate . stPools)
                   (l ^. delegationState . dstate . stKeys)
                   (l ^. pcs)
                   slot
                   (tx ^. body)
                   (l ^. utxoState)
 <> validRuleUTXOW tx l

-- The rules for checking validiy of stake delegation transitions return
-- `certificate_type_correct(cert) -> valid_cert(cert)`, i.e., if the
-- certificate is of a different type, it's considered to be valid due to the
-- falsified hypothesis.

-- | Checks whether a key registration certificat is valid.
validKeyRegistration :: DCert -> DWState -> Validity
validKeyRegistration cert ds =
  case cert of
    RegKey key -> if not $ Map.member (hashKey key) stakeKeys
                  then Valid else Invalid [StakeKeyAlreadyRegistered]
                   where (StakeKeys stakeKeys) = ds ^. dstate . stKeys
    _          -> Valid

validKeyDeregistration :: DCert -> DWState -> Validity
validKeyDeregistration cert ds =
  case cert of
    DeRegKey key -> if Map.member (hashKey key) stakeKeys
                    then Valid else Invalid [StakeKeyNotRegistered]
                      where (StakeKeys stakeKeys) = ds ^. dstate . stKeys
    _            -> Valid

validStakeDelegation :: DCert -> DWState -> Validity
validStakeDelegation cert ds =
  case cert of
    Delegate (Delegation source _)
      -> if Map.member (hashKey source) stakeKeys
         then Valid else Invalid [StakeDelegationImpossible]
           where (StakeKeys stakeKeys) = ds ^. dstate . stKeys
    _ -> Valid

-- there is currently no requirement that could make this invalid
validStakePoolRegister :: DCert -> DWState -> Validity
validStakePoolRegister _ _ = Valid

validStakePoolRetire :: DCert -> DWState -> Validity
validStakePoolRetire cert ds =
  case cert of
    RetirePool key _ -> if Map.member (hashKey key) stakePools
                        then Valid else Invalid [StakePoolNotRegisteredOnKey]
                         where (StakePools stakePools) = ds ^. pstate . stPools
    _                -> Valid

validDelegation :: DCert -> DWState -> Validity
validDelegation cert ds =
     validKeyRegistration cert ds
  <> validKeyDeregistration cert ds
  <> validStakeDelegation cert ds
  <> validStakePoolRegister cert ds
  <> validStakePoolRetire cert ds

-- |In the case where a transaction is valid for a given ledger state,
-- apply the transaction as a state transition function on the ledger state.
-- Otherwise, return a list of validation errors.
asStateTransition
  :: Slot -> LedgerState -> TxWits -> Either [ValidationError] LedgerState
asStateTransition slot ls tx =
  case validTx tx slot ls of
    Invalid errors -> Left errors
    Valid          -> foldM (certAsStateTransition slot (ls ^. txSlotIx)) ls' cs
      where
        ls' = applyTxBody slot ls (tx ^. body)
        cs = zip [0..] (tx ^. body . certs) -- index certificates

-- |In the case where a certificate is valid for a given ledger state,
-- apply the certificate as a state transition function on the ledger state.
-- Otherwise, return a list of validation errors.
certAsStateTransition
  :: Slot -> Ix -> LedgerState -> (Ix, DCert) -> Either [ValidationError] LedgerState
certAsStateTransition slot txIx ls (clx, cert) =
  case validDelegation cert (ls ^. delegationState) of
    Invalid errors -> Left errors
    Valid          -> Right $ ls & delegationState %~ applyDCert slot txIx clx cert

-- | Apply transition independent of validity, collect validation errors on the
-- way.
asStateTransition'
  :: Slot -> LedgerValidation -> TxWits -> LedgerValidation
asStateTransition' slot (LedgerValidation valErrors ls) tx =
    let ls' = applyTxBody slot ls (tx ^. body) in
    case validTx tx slot ls of
      Invalid errors -> LedgerValidation (valErrors ++ errors) ls'
      Valid          -> LedgerValidation valErrors ls'

-- Functions for stake delegation model

-- |Retire the appropriate stake pools when the epoch changes.
retirePools :: LedgerState -> Epoch -> LedgerState
retirePools ls@(LedgerState _ ds _ _ _) epoch =
    ls & delegationState .~
           (ds & pstate . stPools .~
                 (StakePools $ Map.filterWithKey
                        (\hk _ -> Map.notMember hk retiring')
                        stakePools)
               & pstate . retiring .~ active)
  where (active, retiring') = Map.partition (epoch /=) (ds ^. pstate . retiring)
        (StakePools stakePools) = ds ^. pstate . stPools

-- |Calculate the change to the deposit pool for a given transaction.
depositPoolChange :: LedgerState -> Tx -> Coin
depositPoolChange ls tx = (currentPool + txDeposits) - txRefunds
  -- Note that while (currentPool + txDeposits) >= txRefunds,
  -- it could be that txDeposits < txRefunds. We keep the parenthesis above
  -- to emphasize this point.
  where
    currentPool = ls ^. utxoState . deposits
    txDeposits = depositAmount (ls ^. pcs) (ls ^. delegationState . pstate . stPools) tx
    txRefunds = keyRefunds (ls ^. pcs) (ls ^. delegationState . dstate . stKeys) tx

-- |Apply a transaction body as a state transition function on the ledger state.
applyTxBody :: Slot -> LedgerState -> Tx -> LedgerState
applyTxBody slot ls tx =
    ls & utxoState %~ flip applyUTxOUpdate tx
       & utxoState . deposits .~ depositPoolChange ls tx
       & utxoState . fees .~ (tx ^. txfee) + (ls ^. utxoState . fees)
       & delegationState . dstate . rewards .~ newAccounts
       & txSlotIx  %~ (if slot == ls ^. currentSlot then (+1) else const (0::Natural))
       & currentSlot .~ slot
  where
    newAccounts = reapRewards (ls ^. delegationState . dstate. rewards) (tx ^. wdrls)

reapRewards :: RewardAccounts -> RewardAccounts -> RewardAccounts
reapRewards dStateRewards withdrawals =
    Map.mapWithKey removeRewards dStateRewards
    where removeRewards k v = if k `Map.member` withdrawals then Coin 0 else v

applyUTxOUpdate :: UTxOState -> Tx -> UTxOState
applyUTxOUpdate u tx = u & utxo .~ txins tx </| (u ^. utxo) `union` txouts tx

-- |Apply a delegation certificate as a state transition function on the ledger state.
applyDCert :: Slot -> Ix -> Ix -> DCert -> DWState -> DWState
applyDCert slot txIx clx (RegKey key) ds =
    ds & dstate . stKeys  .~ (StakeKeys $ Map.insert hksk slot stkeys')
       & dstate . rewards %~ Map.insert (RewardAcnt hksk) (Coin 0)
       & dstate . ptrs    %~ Map.insert (Ptr slot txIx clx) hksk
        where hksk = hashKey key
              (StakeKeys stkeys') = ds ^. dstate . stKeys

applyDCert slot txIx clx (DeRegKey key) ds =
    ds & dstate . stKeys      .~ (StakeKeys $ Map.delete hksk stkeys')
       & dstate . rewards     %~ Map.delete (RewardAcnt hksk)
       & dstate . delegations %~ Map.delete hksk
       & dstate . ptrs        %~ Map.delete (Ptr slot txIx clx)
        where hksk = hashKey key
              (StakeKeys stkeys') = ds ^. dstate . stKeys

-- TODO do we also have to check hashKey target?
applyDCert _ _ _ (Delegate (Delegation source target)) ds =
    ds & dstate . delegations %~ Map.insert (hashKey source) (hashKey target)

applyDCert slot _ _ (RegPool sp) ds =
    ds & pstate . stPools  .~ (StakePools $ Map.insert hsk slot' pools)
       & pstate . pParams  %~ Map.insert hsk sp
       & pstate . retiring %~ Map.delete hsk
  where hsk = hashKey $ sp ^. poolPubKey
        (StakePools pools) = ds ^. pstate . stPools
        slot' = fromMaybe slot (Map.lookup hsk pools)

-- TODO check epoch (not in new doc atm.)
applyDCert _ _ _ (RetirePool key epoch) ds =
    ds & pstate . retiring %~ Map.insert hk_sp epoch
  where hk_sp = hashKey key

-- |Compute how much stake each active stake pool controls.
delegatedStake :: LedgerState -> Map.Map HashKey Coin
delegatedStake ls@(LedgerState _ ds _ _ _) = Map.fromListWith mappend delegatedOutputs
  where
    getOutputs (UTxO utxo') = Map.elems utxo'
    addStake delegs (TxOut (AddrTxin _ hsk) c) = do
      pool <- Map.lookup hsk delegs
      return (pool, c)
    addStake delegs (TxOut (AddrPtr ptr) c) = do
      key  <- Map.lookup ptr $ ds ^. dstate . ptrs
      pool <- Map.lookup key delegs
      return (pool, c)
    outs = getOutputs $ ls ^. utxoState . utxo
    delegatedOutputs = mapMaybe (addStake $ ds ^. dstate . delegations) outs

---------------------------------
-- epoch boundary calculations --
---------------------------------

-- | Calulcate moving average
movingAvg :: PParams -> HashKey -> Natural -> Rational -> Avgs -> Rational
movingAvg pc hk n expectedSlots (Avgs averages) =
  let fraction = fromIntegral n / max expectedSlots 1
   in case Map.lookup hk averages of
        Nothing -> fraction
        Just (StakeShare prev) -> alpha * fraction + (1 - alpha) * prev
          where alpha = intervalValue $ pc ^. movingAvgWeight

-- | Calculate pool reward
poolRew ::
     PParams
  -> HashKey
  -> Natural
  -> Rational
  -> Avgs
  -> Coin
  -> (Coin, Rational)
poolRew pc hk n expectedSlots averages (Coin maxP) =
  (floor $ e * fromIntegral maxP, avg)
  where
    avg = intervalValue $ pc ^. movingAvgExp
    gamma = movingAvg pc hk n expectedSlots averages
    e = fromRational avg ** fromRational gamma :: Double

-- | Calculate pool leader reward
leaderRew :: Coin -> StakePool -> StakeShare -> StakeShare -> Coin
leaderRew f@(Coin f') pool (StakeShare sigma) (StakeShare s)
  | f' <= c = f
  | otherwise =
    floor $ fromIntegral (c + (f' - c)) * (m' + (1 - m') * sigma / s)
  where
    (Coin c, m, _) = poolSpec pool
    m' = intervalValue m

-- | Calculate pool member reward
memberRew :: Coin -> StakePool -> StakeShare -> StakeShare -> Coin
memberRew (Coin f') pool (StakeShare sigma) (StakeShare s)
  | f' <= c = 0
  | otherwise = floor $ fromIntegral (f' - c) * (1 - m') * sigma / s
  where
    (Coin c, m, _) = poolSpec pool
    m' = intervalValue m

-- | Calculate individual reward
indivRew :: Coin -> StakePool -> StakeShare -> StakeShare -> Bool -> Coin
indivRew f pool sigma s True  = leaderRew f pool sigma s
indivRew f pool sigma s False = memberRew f pool sigma s

-- | Reward one pool
rewardOnePool ::
     PParams
  -> Coin
  -> Natural
  -> HashKey
  -> StakePool
  -> Map.Map HashKey Coin
  -> Avgs
  -> Coin
  -> (Map.Map RewardAcnt Coin, StakeShare)
rewardOnePool pc r n poolHK pool actgr averages (Coin total) =
  (Map.fromList keysVals, StakeShare avg)
  where
    (Coin pstake) = Map.foldl (+) (Coin 0) actgr
    sigma = fromIntegral pstake % fromIntegral total
    expectedSlots = sigma * fromIntegral (pc ^. slotsPerEpoch)
    (_, _, Coin p) = poolSpec pool
    pr = fromIntegral p % fromIntegral total
    maxP =
      if p <= pstake
        then maxPool pc r sigma pr
        else 0
    (poolR, avg) = poolRew pc poolHK n expectedSlots averages maxP
    sFrac = StakeShare (sigma / fromIntegral total)
    keysVals =
      [ ( RewardAcnt hk
        , indivRew
            poolR
            pool
            sFrac
            (StakeShare (fromIntegral c % fromIntegral total))
            (hk == poolHK))
      | (hk, Coin c) <- Map.toList actgr
      ]

reward ::
     Production
  -> PParams
  -> Coin
  -> DWState
  -> [TxOut]
  -> (Map.Map RewardAcnt Coin, Avgs)
reward (Production prod) pc r dwstate outs =
  ( foldl Map.union Map.empty [rew | (_, (rew, _)) <- results]
  , Avgs $ Map.fromList [(hk, avg) | (hk, (_, avg)) <- results])
  where
    active =
      activeStake
        outs
        (dwstate ^. dstate . ptrs)
        (dwstate ^. dstate . stKeys)
        (dwstate ^. dstate . delegations)
        (dwstate ^. pstate . stPools)
    total = Map.foldl (+) (Coin 0) active
    pactive = groupByPool active (dwstate ^. dstate . delegations)
    pdata =
      [ ( key
        , ( (dwstate ^. pstate . pParams) Map.! key
          , prod Map.! key
          , pactive Map.! key))
      | key <-
          Set.toList $ Map.keysSet (dwstate ^. pstate . pParams) `Set.intersection`
          Map.keysSet prod `Set.intersection`
          Map.keysSet pactive
      ]
    results =
      [ ( hk
        , rewardOnePool pc r n hk pool actgr (dwstate ^. pstate . avgs) total)
      | (hk, (pool, n, actgr)) <- pdata
      ]

-- | Update moving averages
updateAvgs ::
     PParams
  -> Avgs
  -> BlocksMade
  -> (Map.Map HashKey (Set.Set Stake))
  -> Avgs
updateAvgs pp avgs blocks pooledStake = undefined
    where
      tot = Map.foldl (+) (Coin 0) $ Map.map sumStake pooledStake
      sumStake s = Set.foldl (\sum (Stake (_, c)) -> sum + c) (Coin 0) s
      expected hk = case Map.lookup hk pooledStake of
                      Just st -> (sumStake st) * fromIntegral (pp ^. slotsPerEpoch)
                      Nothing -> Coin 0


---------------------------------------------------------------------------------
-- State transition system
---------------------------------------------------------------------------------

data UTXO

instance STS UTXO where
    type State UTXO       = UTxOState
    type Signal UTXO      = Tx
    type Environment UTXO = (PParams, Slot, StakeKeys, StakePools)
    data PredicateFailure UTXO = BadInputsUTxO
                               | ExpiredUTxO Slot Slot
                               | InputSetEmptyUTxO
                               | FeeTooSmallUTxO Coin Coin
                               | ValueNotConservedUTxO Coin Coin
                               | UnexpectedFailureUTXO [ValidationError]
                               | UnexpectedSuccessUTXO
                   deriving (Eq, Show)

    transitionRules = [ utxoInductive ]

    initialRules = [ initialLedgerState ]

initialLedgerState :: InitialRule UTXO
initialLedgerState = do
  IRC _ <- judgmentContext
  pure $ UTxOState (UTxO Map.empty) (Coin 0) (Coin 0)

utxoInductive :: TransitionRule UTXO
utxoInductive = do
  TRC ((pc, slot, stakeKeys, stakePools), u, tx) <- judgmentContext
  validInputs tx u       == Valid ?! BadInputsUTxO
  current tx slot        == Valid ?! ExpiredUTxO (tx ^. ttl) slot
  validNoReplay tx       == Valid ?! InputSetEmptyUTxO
  let validateFee         = validFee pc tx
  validateFee            == Valid ?! unwrapFailureUTXO validateFee
  let validateBalance     = preserveBalance stakePools stakeKeys pc tx u
  validateBalance        == Valid ?! unwrapFailureUTXO validateBalance
  pure $ applyUTxOUpdate u tx

unwrapFailureUTXO :: Validity -> PredicateFailure UTXO
unwrapFailureUTXO (Invalid [e]) = unwrapFailureUTXO' e
unwrapFailureUTXO Valid         = UnexpectedSuccessUTXO
unwrapFailureUTXO (Invalid x)   = UnexpectedFailureUTXO x

unwrapFailureUTXO' :: ValidationError -> PredicateFailure UTXO
unwrapFailureUTXO' BadInputs                = BadInputsUTxO
unwrapFailureUTXO' (Expired s s')           = ExpiredUTxO s s'
unwrapFailureUTXO' InputSetEmpty            = InputSetEmptyUTxO
unwrapFailureUTXO' (FeeTooSmall c c')       = FeeTooSmallUTxO c c'
unwrapFailureUTXO' (ValueNotConserved c c') = ValueNotConservedUTxO c c'
unwrapFailureUTXO' x                        = UnexpectedFailureUTXO [x]

data UTXOW

instance STS UTXOW where
    type State UTXOW       = UTxOState
    type Signal UTXOW      = TxWits
    type Environment UTXOW = (PParams, Slot, StakeKeys, StakePools)
    data PredicateFailure UTXOW = InvalidWitnessesUTXOW
                                | MissingWitnessesUTXOW
                                | UnneededWitnessesUTXOW
                                | UtxoFailure (PredicateFailure UTXO)
                   deriving (Eq, Show)

    transitionRules = [ utxoWitnessed ]

    initialRules = [ initialLedgerStateUTXOW ]

initialLedgerStateUTXOW :: InitialRule UTXOW
initialLedgerStateUTXOW = do
  IRC (pc, slots, stakeKeys, stakePools) <- judgmentContext
  trans @UTXO $ IRC (pc, slots, stakeKeys, stakePools)


utxoWitnessed :: TransitionRule UTXOW
utxoWitnessed = do
  TRC ((pc, slot, stakeKeys, stakePools), u, txwits) <- judgmentContext
  verifiedWits txwits     == Valid ?! InvalidWitnessesUTXOW
  enoughWits txwits u     == Valid ?! MissingWitnessesUTXOW
  noUnneededWits txwits u == Valid ?! UnneededWitnessesUTXOW
  trans @UTXO $ TRC ((pc, slot, stakeKeys, stakePools), u, txwits ^. body)

data DELRWDS

instance STS DELRWDS where
    type State DELRWDS            = DWState
    type Signal DELRWDS           = RewardAccounts
    type Environment DELRWDS      = Slot
    data PredicateFailure DELRWDS = IncorrectWithdrawalDELRWDS
                     deriving (Show, Eq)

    initialRules    = [ pure emptyDelegation ]
    transitionRules = [ delrwdsTransition    ]

delrwdsTransition :: TransitionRule DELRWDS
delrwdsTransition = do
  TRC (_, d, withdrawals) <- judgmentContext
  correctWithdrawals (d ^. dstate . rewards) withdrawals == Valid ?! IncorrectWithdrawalDELRWDS
  pure $ d & dstate . rewards .~ reapRewards (d ^. dstate . rewards) withdrawals


data DELEG

instance STS DELEG where
    type State DELEG            = DWState
    type Signal DELEG           = DCert
    type Environment DELEG      = (Slot, Ix, Ix)
    data PredicateFailure DELEG = StakeKeyAlreadyRegisteredDELEG
                                | StakeKeyNotRegisteredDELEG
                                | StakeDelegationImpossibleDELEG
                                | WrongCertificateTypeDELEG
                   deriving (Show, Eq)

    initialRules    = [ pure emptyDelegation ]
    transitionRules = [ delegationTransition ]

delegationTransition :: TransitionRule DELEG
delegationTransition = do
  TRC((slot, txIx, clx), d, c) <- judgmentContext
  case c of
    RegKey _   -> do
           validKeyRegistration c d == Valid ?! StakeKeyAlreadyRegisteredDELEG
           pure $ applyDCert slot txIx clx c d
    DeRegKey _ -> do
           validKeyDeregistration c d == Valid ?! StakeKeyNotRegisteredDELEG
           pure $ applyDCert slot txIx clx c d
    Delegate _ -> do
           validStakeDelegation c d == Valid ?! StakeDelegationImpossibleDELEG
           pure $ applyDCert slot txIx clx c d
    _         -> do
           False ?! WrongCertificateTypeDELEG -- this always fails
           pure d

data POOL

instance STS POOL where
    type State POOL         = DWState
    type Signal POOL        = DCert
    type Environment POOL   = (Slot, Ix, Ix)
    data PredicateFailure POOL = StakePoolNotRegisteredOnKeyPOOL
                               | WrongCertificateTypePOOL
                  deriving (Show, Eq)

    initialRules = [ pure emptyDelegation ]
    transitionRules = [ poolDelegationTransition ]

poolDelegationTransition :: TransitionRule POOL
poolDelegationTransition = do
  TRC((slot, txIx, clx), d, c) <- judgmentContext
  case c of
    RegPool _      -> pure $ applyDCert slot txIx clx c d
    RetirePool _ _ -> do
           validStakePoolRetire c d == Valid ?! StakePoolNotRegisteredOnKeyPOOL
           pure $ applyDCert slot txIx clx c d
    _   -> do
           False ?! WrongCertificateTypePOOL
           pure $ applyDCert slot txIx clx c d

data DELPL
instance STS DELPL where
    type State DELPL       = DWState
    type Signal DELPL      = DCert
    type Environment DELPL = (Slot, Ix, Ix)
    data PredicateFailure DELPL = PoolFailure (PredicateFailure POOL)
                                | DelegFailure (PredicateFailure DELEG)
                   deriving (Show, Eq)

    initialRules    = [ pure emptyDelegation ]
    transitionRules = [ delplTransition      ]

delplTransition :: TransitionRule DELPL
delplTransition = do
  TRC(slotIx, d, c) <- judgmentContext
  case c of
    RegPool    _   -> trans @POOL  $ TRC (slotIx, d, c)
    RetirePool _ _ -> trans @POOL  $ TRC (slotIx, d, c)
    RegKey _       -> trans @DELEG $ TRC (slotIx, d, c)
    DeRegKey _     -> trans @DELEG $ TRC (slotIx, d, c)
    Delegate _     -> trans @DELEG $ TRC (slotIx, d, c)

data DELEGS
instance STS DELEGS where
    type State DELEGS       = DWState
    type Signal DELEGS      = [DCert]
    type Environment DELEGS = (Slot, Ix)
    data PredicateFailure DELEGS = DelplFailure (PredicateFailure DELPL)
                    deriving (Show, Eq)

    initialRules    = [ pure emptyDelegation ]
    transitionRules = [ delegsTransition     ]

delegsTransition :: TransitionRule DELEGS
delegsTransition = do
  TRC((slot, ix), d, certificates) <- judgmentContext
  foldM (\d' (clx, c) -> trans @DELPL $
                        TRC((slot, ix, clx), d', c)) d $ zip [0..] certificates

data DELEGT
instance STS DELEGT where
    type State DELEGT       = DWState
    type Signal DELEGT      = Tx
    type Environment DELEGT = (Slot, Ix)
    data PredicateFailure DELEGT = DelegsFailure (PredicateFailure DELEGS)
                                 | DelrwdsFailure (PredicateFailure DELRWDS)
                                 | RegCertWithdrawDELEGT
                                 | DeregCertNotWithdrawDELEGT
                                 | DelegateCertNotStakePoolsDELEGT
                                 | DeregCertRetireOrDelegateDELEGT
                    deriving (Show, Eq)

    initialRules    = [ pure emptyDelegation ]
    transitionRules = [ delegtTransition     ]

splitCerts :: [DCert] -> ([DCert], [DCert], [DCert]) -> ([DCert], [DCert], [DCert])
splitCerts [] t = t
splitCerts (c:cs) (reg, dereg, delegate) = splitCerts cs (reg', dereg', delegate')
    where (reg', dereg', delegate') =
              case c of
                RegKey _   -> (c:reg, dereg, delegate)
                DeRegKey _ -> (reg, c:dereg, delegate)
                Delegate _ -> (reg, dereg, c:delegate)
                _          -> (reg, dereg, delegate)

delegtTransition :: TransitionRule DELEGT
delegtTransition = do
  TRC(slotIx@(slot, _), d, tx) <- judgmentContext
  let withdrawals = tx ^. wdrls
  let StakePools stakePools  = d ^. pstate . stPools
  let (regC, deregC, delegateC) = splitCerts (tx ^. certs) ([], [], [])
  let hk c = hashKey $ getRequiredSigningKey c
  not (any (\c -> Map.member (RewardAcnt $ hk c) withdrawals) regC)
           ?! RegCertWithdrawDELEGT
  all  (\c -> Map.member (RewardAcnt $ hk c) withdrawals) deregC
           ?! DeregCertNotWithdrawDELEGT
  all  (\c -> Map.member (hk c) stakePools) delegateC
           ?! DelegateCertNotStakePoolsDELEGT
  not (any (\c -> let hsk = hk c in
              Map.member hsk stakePools || Map.member hsk (d ^. pstate . retiring)) deregC)
           ?! DeregCertRetireOrDelegateDELEGT
  d'  <- trans @DELRWDS $ TRC(slot,  d, tx ^. wdrls)
  d'' <- trans @DELEGS  $ TRC(slotIx, d', tx ^. certs)
  pure d''

data LEDGER
instance STS LEDGER where
    type State LEDGER       = (UTxOState, DWState)
    type Signal LEDGER      = TxWits
    type Environment LEDGER = (PParams, Slot, Ix)
    data PredicateFailure LEDGER = UtxowFailure (PredicateFailure UTXOW)
                                 | DelegtFailure (PredicateFailure DELEGT)
                    deriving (Show, Eq)

    initialRules    = [ initialLedgerStateLEDGER ]
    transitionRules = [ ledgerTransition         ]

initialLedgerStateLEDGER :: InitialRule LEDGER
initialLedgerStateLEDGER = do
  IRC (pc, slot, ix) <- judgmentContext
  utxo' <- trans @UTXOW  $ IRC (pc, slot, StakeKeys Map.empty, StakePools Map.empty)
  deleg <- trans @DELEGT $ IRC (slot, ix)
  pure (utxo', deleg)

ledgerTransition :: TransitionRule LEDGER
ledgerTransition = do
  TRC ((pc, slot, ix), (u, d), txwits) <- judgmentContext
  utxo'  <- trans @UTXOW  $ TRC ((pc, slot, d ^. dstate . stKeys, d ^. pstate . stPools), u, txwits)
  deleg' <- trans @DELEGT $ TRC ((slot, ix), d, txwits ^. body)
  pure (utxo', deleg')

-- STS rules embeddings:
-- +------------------------------------+
-- |LEDGER                              |
-- |+--------------------------++------+|
-- ||DELEGT                    ||UTXOW ||
-- ||+---------------++-------+||+----+||
-- |||DELEGS         ||DELRWDS||||UTXO|||
-- |||+-------------+|+-------+||+----+||
-- ||||DELPL        ||         |+------+|
-- ||||+-----++----+||         |        |
-- |||||DELEG||POOL|||         |        |
-- ||||+-----++----+||         |        |
-- |||+-------------+|         |        |
-- ||+---------------+         |        |
-- |+--------------------------+        |
-- +------------------------------------+

instance Embed UTXOW LEDGER where
    wrapFailed = UtxowFailure

instance Embed UTXO UTXOW where
    wrapFailed = UtxoFailure

instance Embed DELEGT LEDGER where
    wrapFailed = DelegtFailure

instance Embed DELRWDS DELEGT where
    wrapFailed = DelrwdsFailure

instance Embed DELEGS DELEGT where
    wrapFailed = DelegsFailure

instance Embed DELPL DELEGS where
    wrapFailed = DelplFailure

instance Embed POOL DELPL where
    wrapFailed = PoolFailure

instance Embed DELEG DELPL where
    wrapFailed = DelegFailure

----------------------------------
-- STS rules for epoch boundary --
----------------------------------

data UTXOEP
instance STS UTXOEP where
    type State UTXOEP = UTxOState
    type Signal UTXOEP = ()
    type Environment UTXOEP = (Slot, PParams, StakeKeys, StakePools)
    data PredicateFailure UTXOEP = FailureUTXOEP
                    deriving(Show, Eq)

    initialRules = [ initialUtxo ]
    transitionRules = [ utxoEpTransition ]

initialUtxo :: InitialRule UTXOEP
initialUtxo = do
  IRC _ <- judgmentContext
  pure $ UTxOState (UTxO Map.empty) (Coin 0) (Coin 0)

utxoEpTransition :: TransitionRule UTXOEP
utxoEpTransition = do
  TRC ((slot, pc, stakeKeys, stakePools), u, _) <- judgmentContext
  pure $ u & deposits .~ obligation pc stakeKeys stakePools slot
           & fees     .~ Coin 0

data POOLCLEAN
instance STS POOLCLEAN where
    type State POOLCLEAN = PState
    type Signal POOLCLEAN = ()
    type Environment POOLCLEAN = Slot
    data PredicateFailure POOLCLEAN = NoRetiredPOOLCLEAN
                       deriving (Show, Eq)

    initialRules = [ pure emptyPState ]
    transitionRules = [ poolCleanTransition ]

poolCleanTransition :: TransitionRule POOLCLEAN
poolCleanTransition = do
  TRC(_, p, _) <- judgmentContext
  let currEpoch = Epoch 100
  let retired = Map.keysSet $ Map.filter (== currEpoch) $ p ^. retiring
  let Avgs averages = p ^. avgs
  null retired ?! NoRetiredPOOLCLEAN
  let (StakePools stpools') = p ^. stPools
  pure $ p & stPools  .~ (StakePools $ Map.withoutKeys stpools' retired)
           & pParams  %~ flip Map.withoutKeys retired
           & retiring %~ flip Map.withoutKeys retired
           & avgs     .~ Avgs (Map.withoutKeys averages retired)

data ACCNT
instance STS ACCNT where
    type State ACCNT = (AccountState, DWState)
    type Signal ACCNT = ()
    type Environment ACCNT = (Slot, PParams, Production, UTxOState)
    data PredicateFailure ACCNT = FailureACCNT
                   deriving (Show, Eq)

    initialRules = [ initialAccnt ]
    transitionRules = [ accntTransition ]

initialAccnt :: InitialRule ACCNT
initialAccnt = pure (emptyAccount, emptyDelegation)

accntTransition :: TransitionRule ACCNT
accntTransition = do
    TRC((slot, pp, production, us), (as, dw), _) <- judgmentContext

    let rho' = intervalValue (pp ^. rho)
    let tau' = intervalValue (pp ^. tau)
    let obl = obligation pp (dw ^. dstate . stKeys) (dw ^. pstate . stPools) slot
    let decayed = us ^. deposits - obl          -- underflow?
    let Coin reserves' = as ^. reserves
    let expansion = floor $ rho' * fromIntegral reserves'
    let Coin totalPool = (us ^. fees) + decayed + (as ^. rewardPool) + expansion
    let newTreasury = floor $ tau' * fromIntegral totalPool
    let availablePool = totalPool - newTreasury -- underflow?
    let getOutputs (UTxO utxo') = Map.elems utxo'
    let outs = getOutputs (us ^. utxo)
    let (rewards', avgs') = reward production pp (Coin availablePool) dw outs
    let paidRewards = Map.foldl (+) (Coin 0) rewards'
    let as' = as & treasury %~ (+) (Coin newTreasury)
                 & reserves %~ (-) expansion      -- underflow?
                 & rewardPool .~ Coin availablePool - paidRewards
    -- union is left-biased, new values take precedence
    let dw' = dw & dstate . rewards %~ Map.union rewards'
                 & pstate . avgs .~ avgs'
    pure (as', dw')

data NEWPC
instance STS NEWPC where
    type State NEWPC = (UTxOState, AccountState)
    type Signal NEWPC = ()
    type Environment NEWPC = (Slot, PParams, PParams, DWState)
    data PredicateFailure NEWPC = ExcessObligationNEWPC
                   deriving (Show, Eq)

    initialRules = [ initialNewPc ]
    transitionRules = [ newPcTransition ]

initialNewPc :: InitialRule NEWPC
initialNewPc = pure (UTxOState (UTxO Map.empty) (Coin 0) (Coin 0), emptyAccount)

newPcTransition :: TransitionRule NEWPC
newPcTransition = do
  TRC((slot, ppOld, ppNew, dw), (us, as), _) <- judgmentContext
  let old = obligation ppOld (dw ^. dstate . stKeys) (dw ^. pstate . stPools) slot
  let new = obligation ppNew (dw ^. dstate . stKeys) (dw ^. pstate . stPools) slot
  as ^. reserves + old >= new ?! ExcessObligationNEWPC
  let diff = old - new
  pure (us & deposits .~ new, as & reserves %~ (+) diff)


data EPOCH
instance STS EPOCH where
    type State EPOCH = (UTxOState, AccountState, DWState)
    type Signal EPOCH = ()
    type Environment EPOCH = (Slot, PParams, PParams, Production)
    data PredicateFailure EPOCH = UtxoEpFailure (PredicateFailure UTXOEP)
                                | PoolCleanFailure (PredicateFailure POOLCLEAN)
                                | AccntFailure (PredicateFailure ACCNT)
                                | NewPcFailure (PredicateFailure NEWPC)
                   deriving (Show, Eq)

    initialRules = [ initialEpoch ]
    transitionRules = [ epochTransition ]

initialEpoch :: InitialRule EPOCH
initialEpoch = do
    IRC(slot, ppOld, ppNew, _) <- judgmentContext
    utxo' <- trans @UTXOEP $ IRC (slot, ppOld, StakeKeys Map.empty, StakePools Map.empty)
    (_, dw') <- trans @ACCNT $ IRC (slot, ppOld, Production Map.empty, utxo')
    pstate'' <- trans @POOLCLEAN $ IRC slot
    let dw'' = dw' & pstate .~ pstate''
    (utxo'', accnt'') <- trans @NEWPC $ IRC (slot, ppOld, ppNew, dw'')
    pure (utxo'', accnt'', dw'')

epochTransition :: TransitionRule EPOCH
epochTransition = do
    TRC((slot, ppOld, ppNew, production), (us, as, dw), _) <- judgmentContext
    us' <- trans @UTXOEP $ TRC ((slot
                               , ppOld
                               , dw ^. dstate . stKeys
                               , dw ^. pstate . stPools), us, ())
    (as', dw') <- trans @ACCNT $ TRC ((slot, ppOld, production, us')
                                     , (as, dw)
                                     , ())
    pstate'' <- trans @POOLCLEAN $ TRC (slot, dw' ^. pstate, ())
    let dw'' = dw' & pstate .~ pstate''
    (us'', as'') <- trans @NEWPC $ TRC ((slot, ppOld, ppNew, dw''), (us, as'), ())
    pure (us'', as'', dw'')

instance Embed UTXOEP EPOCH where
    wrapFailed = UtxoEpFailure

instance Embed ACCNT EPOCH where
    wrapFailed = AccntFailure

instance Embed POOLCLEAN EPOCH where
    wrapFailed = PoolCleanFailure

instance Embed NEWPC EPOCH where
    wrapFailed = NewPcFailure
