/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.ENat.Basic

/-!
# `enat_to_nat`

This file implements the `enat_to_nat` tactic that shifts `ENat`s in the context to `Nat`.

## Implementation details
The implementation follows these steps:
1. Apply the `cases` tactic to each `ENat` variable, producing two goals: one where the variable
   is `⊤`, and one where it is a finite natural number.
2. Simplify arithmetic expressions involving infinities, making (in)equalities either trivial
   or free of infinities. This step uses the `enat_to_nat_top` simp set.
3. Translate the remaining goals from `ENat` to `Nat` using the `enat_to_nat_coe` simp set.

-/

namespace Mathlib.Tactic.ENatToNat

attribute [enat_to_nat_top] OfNat.ofNat_ne_zero ne_eq not_false_eq_true
attribute [enat_to_nat_top] ENat.coe_ne_top ENat.top_ne_coe ENat.coe_lt_top top_le_iff le_top
attribute [enat_to_nat_top] top_add ENat.sub_top ENat.top_sub_coe ENat.mul_top ENat.top_mul

@[enat_to_nat_top] lemma not_lt_top (x : ENat) :
    ¬(⊤ < x) := by cases x <;> simp

@[enat_to_nat_coe] lemma coe_add (m n : ℕ) :
    (m : ENat) + (n : ENat) = ((m + n : ℕ) : ENat) := rfl

@[enat_to_nat_coe] lemma coe_sub (m n : ℕ) :
    (m : ENat) - (n : ENat) = ((m - n : ℕ) : ENat) := rfl

@[enat_to_nat_coe] lemma coe_mul (m n : ℕ) :
    (m : ENat) * (n : ENat) = ((m * n : ℕ) : ENat) := rfl

@[enat_to_nat_coe] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ENat) = (OfNat.ofNat n : ℕ) := rfl

@[enat_to_nat_coe] lemma coe_zero : (0 : ENat) = ((0 : ℕ) : ENat) := rfl

@[enat_to_nat_coe] lemma coe_one : (1 : ENat) = ((1 : ℕ) : ENat) := rfl

attribute [enat_to_nat_coe] ENat.coe_inj ENat.coe_le_coe ENat.coe_lt_coe

open Qq Lean Elab Tactic Term Meta in
/-- Finds the first `ENat` in the context and applies the `cases` tactic to it.
Then simplifies expressions involving `⊤` using the `enat_to_nat_top` simp set. -/
elab "cases_first_enat" : tactic => focus do
  let g ← getMainGoal
  g.withContext do
    let ctx ← getLCtx
    let decl? ← ctx.findDeclM? fun decl => do
      if ← (isExprDefEq (← inferType decl.toExpr) q(ENat)) then
        return Option.some decl
      else
        return Option.none
    let some decl := decl? | throwError "No ENats"
    let isInaccessible := ctx.inaccessibleFVars.find? (·.fvarId == decl.fvarId) |>.isSome
    if isInaccessible then
      let name : Name := `enat_to_nat_aux
      setGoals [← g.rename decl.fvarId name]
      let x := mkIdent name
      evalTactic (← `(tactic| cases $x:ident using ENat.recTopCoe))
    else
      let x := mkIdent decl.userName
      evalTactic
        (← `(tactic| cases $x:ident using ENat.recTopCoe with | top => _ | coe $x:ident => _))
    evalTactic (← `(tactic| all_goals try simp only [enat_to_nat_top] at *))

/-- `enat_to_nat` shifts all `ENat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `enat_to_nat; omega`. -/
macro "enat_to_nat" : tactic => `(tactic| focus (
    (repeat' cases_first_enat) <;>
    (try simp only [enat_to_nat_top, enat_to_nat_coe] at *)
  )
)

end Mathlib.Tactic.ENatToNat
