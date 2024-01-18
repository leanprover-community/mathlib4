/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.Bool
import Std.Tactic.CoeExt
import Mathlib.Init.Logic
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

-- In Lean 3 we had `attribute [simp] cond or and not xor` in the corresponding
-- file, but in Lean 4 this makes the `simpNF` linter complain, so instead we
-- manually generate the corresponding equation lemmas and tag them with `@[simp]` instead.
-- `or`, `and`, and `not` are already done in core Lean 4; here is `cond`, and `xor` is done below.
@[simp] lemma cond_true {α : Type u} {a b : α} : cond true a b = a := rfl
#align bool.cond_tt Bool.cond_true

@[simp] lemma cond_false {α : Type u} {a b : α} : cond false a b = b := rfl
#align bool.cond_ff Bool.cond_false

@[simp]
theorem cond_self.{u} {α : Type u} (b : Bool) (a : α) : cond b a a = a := by cases b <;> rfl
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

@[simp]
theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by
  cases a <;> cases b <;> simp
#align band_eq_false_eq_eq_ff_or_eq_ff Bool.and_eq_false_eq_eq_false_or_eq_false

@[simp]
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

theorem coe_sort_false : (↥false : Prop) = False := by simp
#align coe_sort_ff Bool.coe_sort_false

theorem coe_sort_true : (↥true : Prop) = True := by simp
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

theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by cases b <;> exact by decide
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

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  cases h' : decide q with
  | false => exact decide_false (mt h.1 <| of_decide_false h')
  | true => exact decide_true (h.2 <| of_decide_true h')
#align to_bool_congr Bool.decide_congr

theorem coe_or_iff (a b : Bool) : a || b ↔ a ∨ b := by simp
#align bor_coe_iff Bool.coe_or_iff

theorem coe_and_iff (a b : Bool) : a && b ↔ a ∧ b := by simp
#align band_coe_iff Bool.coe_and_iff

theorem coe_xor_iff (a b : Bool) : xor a b ↔ Xor' (a = true) (b = true) := by
  cases a <;> cases b <;> exact by decide
#align bxor_coe_iff Bool.coe_xor_iff

@[simp]
theorem ite_eq_true_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = true) = if c then a = true else b = true := by by_cases c <;> simp [*]
#align ite_eq_tt_distrib Bool.ite_eq_true_distrib

@[simp]
theorem ite_eq_false_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = false) = if c then a = false else b = false := by
  by_cases c <;> simp [*]
#align ite_eq_ff_distrib Bool.ite_eq_false_distrib

end Bool
