{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module PlutusScripts
  ( guessDecl,
    guessDecl2args,
    evendataDecl,
    evenRedeemerDecl,
    odddataDecl,
    oddRedeemerDecl,
    sumsTo10Decl,
    evenRedeemerDecl2Args,
    oddRedeemerDecl2Args,
    redeemerIs10Decl2Args,
  ) where

import qualified Plutus.V1.Ledger.Scripts as P
import qualified PlutusTx as P (Data (..), compile)
import qualified PlutusTx.Prelude as P
import Language.Haskell.TH


guessDecl :: Q [Dec]
guessDecl =
  [d| guessTheNumber'3 :: P.Data -> P.Data -> P.Data -> ()
      guessTheNumber'3 d1 d2 _d3 = if d1 P.== d2 then () else (P.error ())
  |]

guessDecl2args :: Q [Dec]
guessDecl2args =
  [d| guessTheNumber'2 :: P.Data -> P.Data -> ()
      guessTheNumber'2 d1 d2 = if d1 P.== d2 then () else (P.error ())
  |]

evendataDecl :: Q [Dec]
evendataDecl =
  [d| evendata' :: P.Data -> P.Data -> P.Data -> ()
      evendata' (P.I n) _d2 _d3 = if (P.modulo n 2) P.== 0 then () else (P.error ())
  |]

evenRedeemerDecl :: Q [Dec]
evenRedeemerDecl =
  [d| evenRedeemer' :: P.Data -> P.Data -> P.Data -> ()
      evenRedeemer' _d1 (P.I n) _d3 = if (P.modulo n 2) P.== 0 then () else (P.error ())
  |]

odddataDecl :: Q [Dec]
odddataDecl =
  [d| odddata' :: P.Data -> P.Data -> P.Data -> ()
      odddata' (P.I n)_d2 _d3 = if (P.modulo n 2) P.== 1 then () else (P.error ())
  |]

oddRedeemerDecl :: Q [Dec]
oddRedeemerDecl =
  [d| oddRedeemer' :: P.Data -> P.Data -> P.Data -> ()
      oddRedeemer' _d1 (P.I n)_d3 = if (P.modulo n 2) P.== 1 then () else (P.error ())
  |]

sumsTo10Decl :: Q [Dec]
sumsTo10Decl =
  [d| sumsTo10' :: P.Data -> P.Data -> P.Data -> ()
      sumsTo10' (P.I m) (P.I n)_d3 = if (m P.+ n) P.== 10 then () else (P.error ())
  |]

-- ===========================
-- 2 arg Plutus scripts, for use in non payment contexts


oddRedeemerDecl2Args :: Q [Dec]
oddRedeemerDecl2Args =
  [d| oddRedeemer2' :: P.Data -> P.Data -> ()
      oddRedeemer2' (P.I n)_d3 = if (P.modulo n 2) P.== 1 then () else (P.error ())
  |]

evenRedeemerDecl2Args :: Q [Dec]
evenRedeemerDecl2Args =
  [d| evenRedeemer2' :: P.Data -> P.Data -> ()
      evenRedeemer2' (P.I n) _d3 = if (P.modulo n 2) P.== 0 then () else (P.error ())
  |]

redeemerIs10Decl2Args :: Q [Dec]
redeemerIs10Decl2Args =
  [d| redeemerIs102' :: P.Data -> P.Data -> ()
      redeemerIs102' (P.I n) _d3 = if n P.== 10 then () else (P.error ())
  |]
