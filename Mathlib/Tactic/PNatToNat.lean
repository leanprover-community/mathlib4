/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.PNat.Basic

/-!
# `pnat_to_nat`

This file implements the `pnat_to_nat` tactic that shifts `PNat`s in the context to `Nat`.

## Implementation details
The implementation follows these steps:
1. For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`.
2. Translate arithmetic on `PNat` to `Nat` using the `pnat_to_nat_coe` simp set.

-/

namespace Mathlib.Tactic.PNatToNat

open private getElimNameInfo generalizeTargets generalizeVars from Lean.Elab.Tactic.Induction

open Lean Meta Elab Tactic Qq

/-- For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`. -/
elab "pnat_positivity" : tactic => withMainContext do
  let result ← (← getLCtx).foldlM (init := ← getMainGoal) fun g decl => do
    let ⟨1, declType, declExpr⟩ ← inferTypeQ decl.toExpr | return g
    let ~q(PNat) := declType | return g
    let pf := q(PNat.pos $declExpr)
    let ctx ← getLCtx
    let alreadyDeclared := Option.isSome <| ← ctx.findDeclM? fun ldecl => do
      if ← isDefEq ldecl.type q(0 < PNat.val $declExpr) then
        pure <| .some ()
      else
        pure .none
    if alreadyDeclared then
      return g
    let (_, mvarIdNew) ← (← g.assert .anonymous q(0 < PNat.val $declExpr) pf).intro1P
    return mvarIdNew
  setGoals [result]

@[pnat_to_nat_coe]
lemma coe_inj (m n : PNat) : m = n ↔ (m : ℕ) = (n : ℕ) := by simp

@[pnat_to_nat_coe]
lemma coe_le_coe (m n : PNat) : m ≤ n ↔ (m : ℕ) ≤ (n : ℕ) := by simp

@[pnat_to_nat_coe]
lemma coe_lt_coe (m n : PNat) : m < n ↔ (m : ℕ) < (n : ℕ) := by simp

attribute [pnat_to_nat_coe] PNat.add_coe PNat.mul_coe PNat.val_ofNat

@[pnat_to_nat_coe]
lemma sub_coe (a b : PNat) : ((a - b : PNat) : Nat) = a.val - 1 - b.val + 1 := by
  cases a
  cases b
  simp only [PNat.mk_coe, _root_.PNat.sub_coe, ← _root_.PNat.coe_lt_coe]
  split_ifs <;> omega

/-- `pnat_to_nat` shifts all `PNat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `pnat_to_nat; omega`. -/
macro "pnat_to_nat" : tactic => `(tactic| focus (
  pnat_positivity;
  simp only [pnat_to_nat_coe] at *)
)

end Mathlib.Tactic.PNatToNat
