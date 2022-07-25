/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Hanting Zhang
-/

import Mathlib.Lean.Expr.Basic
import Mathlib.Data.Fintype.Basic

open Lean.Meta

namespace Lean.Elab.Tactic

def getMemType (e : Expr) : TacticM (Option Expr) := do
  -- let type ← inferType e -- should be `Prop`
  match e.getAppFnArgs with
  | (``Membership.mem, #[_, type, _, _, _]) =>
    match type.getAppFnArgs with
    | (``List, #[α])     => return α
    | (``Multiset, #[α]) => return α
    | (``Finset, #[α])   => return α
    | _ => throwError m!"Hypothesis must be of type `x ∈ (A : List/Multiset/Finset α)`"
  | _ => return none

partial def finCasesAt (hyp : FVarId) : TacticM Unit := do
  withMainContext do
    let lDecl ←
      match (← getLCtx).find? hyp with
      | none => throwError m!"hypothesis not found"
      | some lDecl => pure lDecl
    match ← getMemType lDecl.type with
    | some _ =>
      -- Deal with `x ∈ A` hypotheses:
      -- everything inside this block is a hack lmao
      liftMetaTacticAux fun mvarId => do
        let rec loop (goal : MVarId) (hyp : FVarId) (cont : Array MVarId) := do
          try
            let #[g₁, g₂] ← cases goal hyp |
              throwError "'cases' tactic failed, unexpected number of subgoals"
            loop g₂.mvarId g₂.fields[3]!.fvarId! (cont.push g₁.mvarId)
          catch _ =>
            return cont
        return ((), Array.toList <|← loop mvarId hyp #[])
    | none =>
      -- Deal with `x : A`, where `[Fintype A]` is available:
      let inst ← synthInstance (← mkAppM ``Fintype #[lDecl.type])
      let elems ← mkAppOptM ``Fintype.elems #[lDecl.type, inst]
      let t ← mkAppM ``Membership.mem #[lDecl.toExpr, elems]
      let v ← mkAppOptM ``Fintype.complete #[lDecl.type, inst, lDecl.toExpr]

      let hyp ← liftMetaTacticAux fun mvarId => do
        let (fvar, mvarId) ← intro1P (← assert mvarId `this t v)
        pure (fvar, [mvarId])

      withMainContext do
        finCasesAt hyp

syntax (name := finCases) "fin_cases " ("*" <|> (term,+)) (" with " term)? : tactic

@[tactic finCases] def evalFinCases : Tactic := fun stx =>
  match stx with
  | `(tactic| fin_cases $hyps,* $[with $es]?) => do
    for (h : TSyntax `term) in hyps.getElems do
      finCasesAt (← getFVarId h)
  | `(tactic| fin_cases * $[with $es]?) => do
    sorry
  | _ => throwUnsupportedSyntax

example {p : Fin 4 → Prop} (i : Fin 4) (h : p i) : p i := by
  fin_cases i
  repeat exact h
