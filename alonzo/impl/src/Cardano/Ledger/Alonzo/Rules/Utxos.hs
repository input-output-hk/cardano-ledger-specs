{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Alonzo.Rules.Utxos
  ( UTXOS,
    UtxosPredicateFailure (..),
    constructValidated,
    lbl2Phase,
  )
where

import Cardano.Binary (FromCBOR (..), ToCBOR (..))
import Cardano.Ledger.Alonzo.Language (Language)
import Cardano.Ledger.Alonzo.PlutusScriptApi
  ( CollectError,
    collectTwoPhaseScriptInputs,
    evalScripts,
  )
import Cardano.Ledger.Alonzo.Scripts (Script)
import Cardano.Ledger.Alonzo.Tx
  ( CostModel,
    DataHash,
    IsValidating (..),
    ValidatedTx (..),
    txouts,
  )
import qualified Cardano.Ledger.Alonzo.TxBody as Alonzo
import Cardano.Ledger.Alonzo.TxInfo (ScriptResult (..))
import qualified Cardano.Ledger.Alonzo.TxWitness as Alonzo
import Cardano.Ledger.BaseTypes
  ( Globals,
    ShelleyBase,
    StrictMaybe (..),
    epochInfo,
    strictMaybeToMaybe,
    systemStart,
  )
import Cardano.Ledger.Coin (Coin)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Mary.Value (Value)
import Cardano.Ledger.Rules.ValidationMode (lblStatic)
import qualified Cardano.Ledger.Val as Val
import Control.Iterate.SetAlgebra (eval, (∪), (⋪), (◁))
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Trans.Reader (asks)
import Control.State.Transition.Extended
import Data.Coders
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import Data.Text
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import NoThunks.Class (NoThunks)
import Shelley.Spec.Ledger.LedgerState (PPUPState (..), UTxOState (..), keyRefunds)
import qualified Shelley.Spec.Ledger.LedgerState as Shelley
import Shelley.Spec.Ledger.PParams (Update)
import Shelley.Spec.Ledger.STS.Ppup (PPUP, PPUPEnv (..), PpupPredicateFailure)
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.TxBody (DCert, TxIn (..), Wdrl)
import Shelley.Spec.Ledger.UTxO (balance, totalDeposits)

--------------------------------------------------------------------------------
-- The UTXOS transition system
--------------------------------------------------------------------------------

data UTXOS era

instance
  forall era.
  ( Era era,
    Eq (Core.PParams era),
    Show (Core.PParams era),
    Show (Core.PParamsDelta era),
    Eq (Core.PParamsDelta era),
    Embed (Core.EraRule "PPUP" era) (UTXOS era),
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Core.Script era ~ Script era,
    Core.Value era ~ Value (Crypto era),
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.TxBody era ~ Alonzo.TxBody era,
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "_costmdls" (Core.PParams era) (Map.Map Language CostModel),
    HasField "datahash" (Core.TxOut era) (StrictMaybe (DataHash (Crypto era)))
  ) =>
  STS (UTXOS era)
  where
  type BaseM (UTXOS era) = ShelleyBase
  type Environment (UTXOS era) = UtxoEnv era
  type State (UTXOS era) = UTxOState era
  type Signal (UTXOS era) = ValidatedTx era
  type PredicateFailure (UTXOS era) = UtxosPredicateFailure era

  transitionRules = [utxosTransition]

utxosTransition ::
  forall era.
  ( Era era,
    Core.Script era ~ Script era,
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Embed (Core.EraRule "PPUP" era) (UTXOS era),
    Eq (Core.PParams era),
    Show (Core.PParams era),
    Show (Core.PParamsDelta era),
    Eq (Core.PParamsDelta era),
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.Value era ~ Value (Crypto era),
    Core.TxBody era ~ Alonzo.TxBody era,
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "collateral" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "_costmdls" (Core.PParams era) (Map.Map Language CostModel)
  ) =>
  TransitionRule (UTXOS era)
utxosTransition =
  judgmentContext >>= \(TRC (_, _, tx)) -> do
    case getField @"isValidating" tx of
      IsValidating True -> scriptsValidateTransition
      IsValidating False -> scriptsNotValidateTransition

scriptsValidateTransition ::
  forall era.
  ( Show (Core.Value era), -- Arises because of the use of (∪) from SetAlgebra, needs Show to report problems.
    Era era,
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Embed (Core.EraRule "PPUP" era) (UTXOS era),
    Eq (Core.PParams era),
    Show (Core.PParams era),
    Show (Core.PParamsDelta era),
    Eq (Core.PParamsDelta era),
    Core.Script era ~ Script era,
    Core.TxBody era ~ Alonzo.TxBody era,
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.Value era ~ Value (Crypto era),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "_costmdls" (Core.PParams era) (Map.Map Language CostModel)
  ) =>
  TransitionRule (UTXOS era)
scriptsValidateTransition = do
  TRC
    ( UtxoEnv slot pp poolParams genDelegs,
      UTxOState utxo deposited fees pup,
      tx
      ) <-
    judgmentContext
  let txb = body tx
      refunded = keyRefunds pp txb
      depositChange =
        ( totalDeposits
            pp
            (`Map.notMember` poolParams)
            (toList $ getField @"certs" txb)
        )
          Val.<-> refunded
  sysSt <- liftSTS $ asks systemStart
  ei <- liftSTS $ asks epochInfo
  case collectTwoPhaseScriptInputs ei sysSt pp tx utxo of
    Right sLst ->
      case evalScripts @era tx sLst of
        Fails sss -> False ?!## ValidationTagMismatch (getField @"isValidating" tx) (pack (Prelude.unlines sss))
        Passes -> pure ()
    Left info -> failBecause (CollectErrors info)
  pup' <-
    trans @(Core.EraRule "PPUP" era) $
      TRC
        (PPUPEnv slot pp genDelegs, pup, strictMaybeToMaybe $ getField @"update" txb)
  pure $
    UTxOState
      { _utxo = eval ((getField @"inputs" txb ⋪ utxo) ∪ txouts @era txb),
        _deposited = deposited <> depositChange,
        _fees = fees <> getField @"txfee" txb,
        _ppups = pup'
      }

scriptsNotValidateTransition ::
  forall era.
  ( Era era,
    Eq (Core.PParams era),
    Show (Core.PParams era),
    Show (Core.PParamsDelta era),
    Eq (Core.PParamsDelta era),
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Embed (Core.EraRule "PPUP" era) (UTXOS era),
    Core.Script era ~ Script era,
    Core.TxBody era ~ Alonzo.TxBody era,
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.Value era ~ Value (Crypto era),
    HasField "collateral" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "_costmdls" (Core.PParams era) (Map.Map Language CostModel),
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin
  ) =>
  TransitionRule (UTXOS era)
scriptsNotValidateTransition = do
  TRC (UtxoEnv _ pp _ _, us@(UTxOState utxo _ fees _), tx) <- judgmentContext
  let txb = body tx
  sysSt <- liftSTS $ asks systemStart
  ei <- liftSTS $ asks epochInfo
  case collectTwoPhaseScriptInputs ei sysSt pp tx utxo of
    Right sLst ->
      case (evalScripts @era tx sLst) of
        Passes -> False ?!## ValidationTagMismatch (getField @"isValidating" tx) (pack ("Script expected to fail, passes."))
        Fails _sss -> pure ()
    Left info -> failBecause (CollectErrors info)
  pure $
    us
      { _utxo = eval (getField @"collateral" txb ⋪ utxo),
        _fees = fees <> Val.coin (balance @era (eval (getField @"collateral" txb ◁ utxo)))
      }

data UtxosPredicateFailure era
  = -- | The 'isValidating' tag on the transaction is incorrect. The tag given
    --   here is that provided on the transaction (whereas evaluation of the
    --   scripts gives the opposite.). The Text tries to explain why it failed.
    ValidationTagMismatch IsValidating Text
  | -- | We could not find all the necessary inputs for a Plutus Script.
    --         Previous PredicateFailure tests should make this impossible, but the
    --         consequences of not detecting this means scripts get dropped, so things
    --         might validate that shouldn't. So we double check in the function
    --         collectTwoPhaseScriptInputs, it should find data for every Script.
    CollectErrors [CollectError (Crypto era)]
  | UpdateFailure (PredicateFailure (Core.EraRule "PPUP" era))
  deriving
    (Generic)

instance
  ( Era era,
    ToCBOR (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  ToCBOR (UtxosPredicateFailure era)
  where
  toCBOR (ValidationTagMismatch v txt) = encode (Sum ValidationTagMismatch 0 !> To v !> To txt)
  toCBOR (CollectErrors cs) =
    encode (Sum (CollectErrors @era) 1 !> To cs)
  toCBOR (UpdateFailure pf) = encode (Sum (UpdateFailure @era) 2 !> To pf)

instance
  ( Era era,
    FromCBOR (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  FromCBOR (UtxosPredicateFailure era)
  where
  fromCBOR = decode (Summands "UtxosPredicateFailure" dec)
    where
      dec 0 = SumD ValidationTagMismatch <! From <! From
      dec 1 = SumD (CollectErrors @era) <! From
      dec 2 = SumD UpdateFailure <! From
      dec n = Invalid n

deriving stock instance
  ( Shelley.TransUTxOState Show era,
    Show (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  Show (UtxosPredicateFailure era)

instance
  ( Shelley.TransUTxOState Eq era,
    Eq (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  Eq (UtxosPredicateFailure era)
  where
  (ValidationTagMismatch a _) == (ValidationTagMismatch b _) = a == b -- Do not compare the Text in an Eq check.
  (CollectErrors x) == (CollectErrors y) = x == y
  (UpdateFailure x) == (UpdateFailure y) = x == y
  _ == _ = False

instance
  ( Shelley.TransUTxOState NoThunks era,
    NoThunks (PredicateFailure (Core.EraRule "PPUP" era))
  ) =>
  NoThunks (UtxosPredicateFailure era)

instance
  ( Era era,
    STS (PPUP era),
    PredicateFailure (Core.EraRule "PPUP" era) ~ PpupPredicateFailure era
  ) =>
  Embed (PPUP era) (UTXOS era)
  where
  wrapFailed = UpdateFailure

-- =================================================================

-- | Construct a 'ValidatedTx' from a 'Core.Tx' by setting the `IsValidating`
-- flag.
--
-- Note that this simply constructs the transaction; it does not validate
-- anything other than the scripts. Thus the resulting transaction may be
-- completely invalid.
constructValidated ::
  forall era m.
  ( MonadError [UtxosPredicateFailure era] m,
    Era era,
    Core.Script era ~ Script era,
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.Value era ~ Value (Crypto era),
    Core.TxBody era ~ Alonzo.TxBody era,
    Core.Witnesses era ~ Alonzo.TxWitness era,
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "datahash" (Core.TxOut era) (StrictMaybe (DataHash (Crypto era))),
    HasField "_costmdls" (Core.PParams era) (Map.Map Language CostModel),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era))
  ) =>
  Globals ->
  UtxoEnv era ->
  UTxOState era ->
  Core.Tx era ->
  m (ValidatedTx era)
constructValidated globals (UtxoEnv _ pp _ _) st tx =
  case collectTwoPhaseScriptInputs ei sysS pp tx utxo of
    Left errs -> throwError [CollectErrors errs]
    Right sLst ->
      let scriptEvalResult = evalScripts @era tx sLst
          vTx =
            ValidatedTx
              (getField @"body" tx)
              (getField @"wits" tx)
              (IsValidating (lift scriptEvalResult))
              (getField @"auxiliaryData" tx)
       in pure vTx
  where
    utxo = _utxo st
    sysS = systemStart globals
    ei = epochInfo globals
    lift Passes = True
    lift (Fails _) = False

--------------------------------------------------------------------------------
-- 2-phase checks
--------------------------------------------------------------------------------

-- $2-phase
--
-- Above and beyond 'static' checks (see 'Cardano.Ledger.Rules.ValidateMode') we
-- additionally label 2-phase checks. This is to support a workflow where we
-- validate a 'ValidatedTx' directly after constructing it with
-- 'constructValidated' - we would like to trust the flag we have ourselves just
-- computed rather than re-calculating it. However, all other checks should be
-- computed as normal.

-- | Indicates that this check depends only upon the signal to the transition,
-- not the state or environment.
lbl2Phase :: Label
lbl2Phase = "2phase"

-- | Construct a 2-phase predicate check.
--
--   Note that 2-phase predicate checks are by definition static.
(?!##) :: Bool -> PredicateFailure sts -> Rule sts ctx ()
(?!##) = labeledPred [lblStatic, lbl2Phase]

infix 1 ?!##
