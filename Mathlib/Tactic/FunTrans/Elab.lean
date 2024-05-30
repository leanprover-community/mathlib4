/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Mathlib.Tactic.FunProp.Core
import Mathlib.Tactic.FunTrans.Core

/-!
## `funProp` tactic syntax
-/

namespace Mathlib
open Lean Meta Elab Tactic

namespace Meta.FunTrans

open Lean.Parser.Tactic


syntax (name := funTransTacStx) "fun_trans" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

syntax (name := funTransConvStx) "fun_trans" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? : conv


simproc_decl fun_trans_simproc (_) := funTrans

private def emptyDischarge : Expr → MetaM (Option Expr) :=
  fun e =>
    withTraceNode `Meta.Tactic.fun_trans
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] discharging: {← ppExpr e}") do
      pure none

private def stxToDischarge (stx : Option (TSyntax ``discharger)) : Expr → MetaM (Option Expr) := fun e => do
  match stx with
  | none => (emptyDischarge e)
  | some d =>
    match d with
    | `(discharger| (discharger:=$tac)) => FunProp.tacticToDischarge (← `(tactic| ($tac))) e
    | _ => emptyDischarge e


@[tactic funTransTacStx]
def funTransTac : Tactic := fun stx => do
  match stx with
  | `(tactic| fun_trans $[$cfg]? $[$disch]? $[only]? $[[$a,*]]? $[$loc]?) => do

    -- set fun_trans config
    funTransConfig.modify
      fun c => { c with funPropConfig := { c.funPropConfig with disch := stxToDischarge disch}}

    let a := a.getD (Syntax.TSepArray.mk #[])
    if stx[3].isNone then
      evalTactic (← `(tactic| simp $[$cfg]? $[$disch]? [↓fun_trans_simproc,$a,*]  $[$loc]?))
    else
      evalTactic (← `(tactic| simp $[$cfg]? $[$disch]? only [↓fun_trans_simproc,$a,*]  $[$loc]?))

    -- reset fun_trans config
    funTransConfig.modify fun _ => {}

  | _ => throwUnsupportedSyntax


@[tactic funTransConvStx]
def funTransConv : Tactic := fun stx => do
  match stx with
  | `(conv| fun_trans $[$cfg]? $[$disch]? $[only]? $[[$a,*]]?) => do

    -- set fun_trans config
    funTransConfig.modify
      fun c => { c with funPropConfig := { c.funPropConfig with disch := stxToDischarge disch}}

    let a := a.getD (Syntax.TSepArray.mk #[])
    if stx[3].isNone then
      evalTactic (← `(conv| simp $[$cfg]? $[$disch]? [↓fun_trans_simproc,$a,*]))
    else
      evalTactic (← `(conv| simp $[$cfg]? $[$disch]? only [↓fun_trans_simproc,$a,*]))

    -- reset fun_trans config
    funTransConfig.modify fun _ => {}

  | _ => throwUnsupportedSyntax
