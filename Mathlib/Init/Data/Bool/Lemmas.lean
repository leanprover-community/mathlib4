/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Data.Bool.Basic
import Mathlib.Init.Logic

-- *TODO* remove this
set_option autoImplicit false


attribute [simp] cond or and not xor

@[simp]
theorem cond_a_a.{u} {α : Type u} (b : Bool) (a : α) : cond b a a = a := by cases b <;> simp

@[simp]
theorem xor_self (b : Bool) : xor b b = false := by cases b <;> simp

@[simp]
theorem xor_true (b : Bool) : xor b true = not b := by cases b <;> simp

theorem xor_false (b : Bool) : xor b false = b := by cases b <;> simp

@[simp]
theorem true_xor (b : Bool) : xor true b = not b := by cases b <;> simp

theorem false_xor (b : Bool) : xor false b = b := by cases b <;> simp

@[simp]
theorem not_not (b : Bool) : not (not b) = b := by cases b <;> simp

theorem true_eq_false_eq_False : ¬true = false := by decide

theorem false_eq_true_eq_False : ¬false = true := by decide

@[simp]
theorem eq_false_eq_not_eq_true (b : Bool) : (¬b = true) = (b = false) := by cases b <;> simp

@[simp]
theorem eq_true_eq_not_eq_false (b : Bool) : (¬b = false) = (b = true) := by cases b <;> simp

theorem eq_false_of_not_eq_true {b : Bool} : ¬b = true → b = false :=
  Eq.mp (eq_false_eq_not_eq_true b)

theorem eq_true_of_not_eq_false {b : Bool} : ¬b = false → b = true :=
  Eq.mp (eq_true_eq_not_eq_false b)

@[simp]
theorem and_eq_true_eq_eq_true_and_eq_true (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

@[simp]
theorem or_eq_true_eq_eq_true_or_eq_true (a b : Bool) : ((a || b) = true) = (a = true ∨ b = true) := by
  cases a <;> cases b <;> simp

@[simp]
theorem not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false) := by cases a <;> simp

@[simp]
theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) : ((a && b) = false) = (a = false ∨ b = false) := by
  cases a <;> cases b <;> simp

@[simp]
theorem or_eq_false_eq_eq_false_and_eq_false (a b : Bool) : ((a || b) = false) = (a = false ∧ b = false) := by
  cases a <;> cases b <;> simp

@[simp]
theorem not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by cases a <;> simp

@[simp]
theorem coe_false : ↑false = False :=
  show (false = true) = False by simp

@[simp]
theorem coe_true : ↑true = True :=
  show (true = true) = True by simp

-- **TODO** Do we just not want this now?
-- @[simp]
-- theorem coe_sort_false : ↥false = False :=
--   show (false = true) = False by simp

-- **TODO** Do we just not want this now?
-- @[simp]
-- theorem coe_sort_true : ↥true = True :=
--   show (true = true) = True by simp

@[simp]
theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p :=
  match d with
  | isTrue hp => ⟨fun _ => hp, fun _ => rfl⟩
  | isFalse hnp => ⟨fun h => Bool.noConfusion h, fun hp => absurd hp hnp⟩

theorem decide_true {p : Prop} [Decidable p] : p → decide p :=
  (decide_iff p).2

theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1

theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by cases b <;> exact by decide

theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1

@[simp]
theorem decide_false_iff (p : Prop) [Decidable p] : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))

theorem decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (decide_false_iff p).2

theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := by
  cases h' : decide q with
  | false => exact decide_false (mt h.1 <| of_decide_false h')
  | true => exact decide_true (h.2 <| of_decide_true h')

@[simp]
theorem or_coe_iff (a b : Bool) : a || b ↔ a ∨ b := by cases a <;> cases b <;> exact by decide

@[simp]
theorem and_coe_iff (a b : Bool) : a && b ↔ a ∧ b := by cases a <;> cases b <;> exact by decide

@[simp]
theorem xor_coe_iff (a b : Bool) : xor a b ↔ Xor' (a = true) (b = true) := by cases a <;> cases b <;> exact by decide

@[simp]
theorem ite_eq_true_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = true) = if c then a = true else b = true := by by_cases c <;> simp [*]

@[simp]
theorem ite_eq_false_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = false) = if c then a = false else b = false := by by_cases c <;> simp [*]
