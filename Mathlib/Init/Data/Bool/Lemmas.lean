/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Logic
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Coe

/-!
# Lemmas about booleans

These are the lemmas about booleans which were present in core Lean 3. See also
the file Mathlib.Data.Bool.Basic which contains lemmas about booleans from
mathlib 3.

-/

set_option autoImplicit true

-- We align Lean 3 lemmas with lemmas in `Init.SimpLemmas` in Lean 4.
#align band_self Bool.and_self
#align band_tt Bool.and_true
#align band_ff Bool.and_false
#align tt_band Bool.true_and
#align ff_band Bool.false_and
#align bor_self Bool.or_self
#align bor_tt Bool.or_true
#align bor_ff Bool.or_false
#align tt_bor Bool.true_or
#align ff_bor Bool.false_or
#align bnot_bnot Bool.not_not

namespace Bool

#align bool.cond_tt Bool.cond_true
#align bool.cond_ff Bool.cond_false
#align cond_a_a Bool.cond_self

attribute [simp] xor_self
#align bxor_self Bool.xor_self

#align bxor_tt Bool.xor_true
#align bxor_ff Bool.xor_false
#align tt_bxor Bool.true_xor
#align ff_bxor Bool.false_xor

theorem true_eq_false_eq_False : ¬true = false := by decide
#align tt_eq_ff_eq_false Bool.true_eq_false_eq_False

theorem false_eq_true_eq_False : ¬false = true := by decide
#align ff_eq_tt_eq_false Bool.false_eq_true_eq_False

theorem eq_false_eq_not_eq_true (b : Bool) : (¬b = true) = (b = false) := by simp
#align eq_ff_eq_not_eq_tt Bool.eq_false_eq_not_eq_true

theorem eq_true_eq_not_eq_false (b : Bool) : (¬b = false) = (b = true) := by simp
#align eq_tt_eq_not_eq_ft Bool.eq_true_eq_not_eq_false

theorem eq_false_of_not_eq_true {b : Bool} : ¬b = true → b = false :=
  Eq.mp (eq_false_eq_not_eq_true b)
#align eq_ff_of_not_eq_tt Bool.eq_false_of_not_eq_true

theorem eq_true_of_not_eq_false {b : Bool} : ¬b = false → b = true :=
  Eq.mp (eq_true_eq_not_eq_false b)
#align eq_tt_of_not_eq_ff Bool.eq_true_of_not_eq_false

theorem and_eq_true_eq_eq_true_and_eq_true (a b : Bool) :
    ((a && b) = true) = (a = true ∧ b = true) := by simp
#align band_eq_true_eq_eq_tt_and_eq_tt Bool.and_eq_true_eq_eq_true_and_eq_true

theorem or_eq_true_eq_eq_true_or_eq_true (a b : Bool) :
    ((a || b) = true) = (a = true ∨ b = true) := by simp
#align bor_eq_true_eq_eq_tt_or_eq_tt Bool.or_eq_true_eq_eq_true_or_eq_true

theorem not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false) := by cases a <;> simp
#align bnot_eq_true_eq_eq_ff Bool.not_eq_true_eq_eq_false

#adaptation_note /-- this is no longer a simp lemma,
  as after nightly-2024-03-05 the LHS simplifies. -/
theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by
  cases a <;> cases b <;> simp
#align band_eq_false_eq_eq_ff_or_eq_ff Bool.and_eq_false_eq_eq_false_or_eq_false

theorem or_eq_false_eq_eq_false_and_eq_false (a b : Bool) :
    ((a || b) = false) = (a = false ∧ b = false) := by
  cases a <;> cases b <;> simp
#align bor_eq_false_eq_eq_ff_and_eq_ff Bool.or_eq_false_eq_eq_false_and_eq_false

theorem not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by cases a <;> simp
#align bnot_eq_ff_eq_eq_tt Bool.not_eq_false_eq_eq_true

theorem coe_false : ↑false = False := by simp
#align coe_ff Bool.coe_false

theorem coe_true : ↑true = True := by simp
#align coe_tt Bool.coe_true

theorem coe_sort_false : (false : Prop) = False := by simp
#align coe_sort_ff Bool.coe_sort_false

theorem coe_sort_true : (true : Prop) = True := by simp
#align coe_sort_tt Bool.coe_sort_true

theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p := by simp
#align to_bool_iff Bool.decide_iff

theorem decide_true {p : Prop} [Decidable p] : p → decide p :=
  (decide_iff p).2
#align to_bool_true Bool.decide_true
#align to_bool_tt Bool.decide_true

theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1
#align of_to_bool_true Bool.of_decide_true

theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by cases b <;> decide
#align bool_iff_false Bool.bool_iff_false

theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1
#align bool_eq_false Bool.bool_eq_false

theorem decide_false_iff (p : Prop) {_ : Decidable p} : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))
#align to_bool_ff_iff Bool.decide_false_iff

theorem decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (decide_false_iff p).2
#align to_bool_ff Bool.decide_false

theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1
#align of_to_bool_ff Bool.of_decide_false

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q :=
  decide_eq_decide.mpr h
#align to_bool_congr Bool.decide_congr

@[deprecated (since := "2024-06-07")] alias coe_or_iff := or_eq_true_iff
#align bor_coe_iff Bool.or_eq_true_iff

@[deprecated (since := "2024-06-07")] alias coe_and_iff := and_eq_true_iff
#align band_coe_iff Bool.and_eq_true_iff

theorem coe_xor_iff (a b : Bool) : xor a b ↔ Xor' (a = true) (b = true) := by
  cases a <;> cases b <;> decide
#align bxor_coe_iff Bool.coe_xor_iff

#align ite_eq_tt_distrib Bool.ite_eq_true_distrib
#align ite_eq_ff_distrib Bool.ite_eq_false_distrib

end Bool
