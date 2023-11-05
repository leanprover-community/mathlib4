/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Data.Bool.Basic
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

namespace Bool

-- In Lean 3 we had `attribute [simp] cond or and not xor` in the corresponding
-- file, but in Lean 4 this makes the `simpNF` linter complain, so instead we
-- manually generate the corresponding equation lemmas and tag them with `@[simp]` instead.
-- `or`, `and`, and `not` are already done in core Lean 4; here is `cond`, and `xor` is done below.
@[simp] lemma cond_true {α : Type u} {a b : α} : cond true a b = a := rfl

@[simp] lemma cond_false {α : Type u} {a b : α} : cond false a b = b := rfl

@[simp]
theorem cond_self.{u} {α : Type u} (b : Bool) (a : α) : cond b a a = a := by cases b <;> rfl

attribute [simp] xor_self


theorem true_eq_false_eq_False : ¬true = false := by decide

theorem false_eq_true_eq_False : ¬false = true := by decide

theorem eq_false_eq_not_eq_true (b : Bool) : (¬b = true) = (b = false) := by simp

theorem eq_true_eq_not_eq_false (b : Bool) : (¬b = false) = (b = true) := by simp

theorem eq_false_of_not_eq_true {b : Bool} : ¬b = true → b = false :=
  Eq.mp (eq_false_eq_not_eq_true b)

theorem eq_true_of_not_eq_false {b : Bool} : ¬b = false → b = true :=
  Eq.mp (eq_true_eq_not_eq_false b)

theorem and_eq_true_eq_eq_true_and_eq_true (a b : Bool) :
    ((a && b) = true) = (a = true ∧ b = true) := by simp

theorem or_eq_true_eq_eq_true_or_eq_true (a b : Bool) :
    ((a || b) = true) = (a = true ∨ b = true) := by simp

theorem not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false) := by cases a <;> simp

@[simp]
theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by
  cases a <;> cases b <;> simp

@[simp]
theorem or_eq_false_eq_eq_false_and_eq_false (a b : Bool) :
    ((a || b) = false) = (a = false ∧ b = false) := by
  cases a <;> cases b <;> simp

theorem not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by cases a <;> simp

theorem coe_false : ↑false = False := by simp

theorem coe_true : ↑true = True := by simp

theorem coe_sort_false : (↥false : Prop) = False := by simp

theorem coe_sort_true : (↥true : Prop) = True := by simp

theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p := by simp

theorem decide_true {p : Prop} [Decidable p] : p → decide p :=
  (decide_iff p).2

theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1

theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by cases b <;> exact by decide

theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1

theorem decide_false_iff (p : Prop) [Decidable p] : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))

theorem decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (decide_false_iff p).2

theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  cases h' : decide q with
  | false => exact decide_false (mt h.1 <| of_decide_false h')
  | true => exact decide_true (h.2 <| of_decide_true h')

theorem coe_or_iff (a b : Bool) : a || b ↔ a ∨ b := by simp

theorem coe_and_iff (a b : Bool) : a && b ↔ a ∧ b := by simp

theorem coe_xor_iff (a b : Bool) : xor a b ↔ Xor' (a = true) (b = true) := by
  cases a <;> cases b <;> exact by decide

@[simp]
theorem ite_eq_true_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = true) = if c then a = true else b = true := by by_cases c <;> simp [*]

@[simp]
theorem ite_eq_false_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = false) = if c then a = false else b = false := by
  by_cases c <;> simp [*]

end Bool
