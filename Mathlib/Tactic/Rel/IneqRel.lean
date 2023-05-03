/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Rel.Basic

open Lean Meta Elab Mathlib Tactic

/-- On applying a lemma or hypothesis successfully, attempt to resolve remaining goals with
`positivity`, but even if that fails, don't backtrack -/
def IneqRelDischarge (g : MVarId) : MetaM (Option (List MVarId)) :=
do Meta.Positivity.positivity g; pure (some []) <|> pure none

syntax (name := IneqRelSyntax) "ineq_rel" " [" term,* "] " : tactic

elab_rules : tactic | `(tactic| ineq_rel [$t,*]) => do
  liftMetaTactic <|
    Lean.MVarId.Rel `ineq_rules t.getElems.toList
      "cannot prove this by 'substituting' the listed relationships"
      IneqRelDischarge

macro_rules | `(tactic| rel [$t,*]) => `(tactic| ineq_rel [$t,*])

syntax (name := IneqExtraSyntax) "ineq_extra" : tactic

elab_rules : tactic | `(tactic| ineq_extra) => do
  liftMetaTactic <|
    Lean.MVarId.Rel `ineq_extra []
      "the two sides don't differ by a neutral quantity for the relation"
      IneqRelDischarge

macro_rules | `(tactic| extra) => `(tactic| ineq_extra)

attribute [ineq_rules]
  le_refl
  -- deliberately no `add_lt_add` since this is an unsafe lemma appplication in the context
  add_le_add add_lt_add_left add_lt_add_right
  sub_le_sub sub_lt_sub_left sub_lt_sub_right
  mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right
  mul_le_mul_of_nonpos_left mul_le_mul_of_nonpos_right
  mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right
  div_le_div_of_le div_lt_div_of_lt
  pow_le_pow_of_le_left pow_lt_pow_of_lt_left
  -- want to apply this only forward on hypotheses, not backward on a general goal
  -- put it last but would be good to implement directly as forward reasoning
  le_of_lt

lemma IneqExtra.neg_le_sub_self_of_nonneg [LinearOrderedAddCommGroup G] {a b : G} (h : 0 ≤ a) :
    -b ≤ a - b := by
  rw [sub_eq_add_neg]
  apply le_add_of_nonneg_left h

attribute [ineq_extra]
  le_add_of_nonneg_right le_add_of_nonneg_left
  lt_add_of_pos_right lt_add_of_pos_left
  IneqExtra.neg_le_sub_self_of_nonneg
  add_le_add_left add_le_add_right add_lt_add_left add_lt_add_right
  sub_le_sub_left sub_le_sub_right sub_lt_sub_left sub_lt_sub_right
  le_refl
