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

attribute [simp] cond or and not xor

namespace Bool

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
theorem and_eq_true_eq_eq_true_and_eq_true (a b : Bool) :
    ((a && b) = true) = (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

@[simp]
theorem or_eq_true_eq_eq_true_or_eq_true (a b : Bool) :
    ((a || b) = true) = (a = true ∨ b = true) := by
  cases a <;> cases b <;> simp

@[simp]
theorem not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false) := by cases a <;> simp

@[simp]
theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by
  cases a <;> cases b <;> simp

@[simp]
theorem or_eq_false_eq_eq_false_and_eq_false (a b : Bool) :
    ((a || b) = false) = (a = false ∧ b = false) := by
  cases a <;> cases b <;> simp

@[simp]
theorem not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by cases a <;> simp

@[simp]
theorem coe_false : ↑false = False :=
  show (false = true) = False by simp

@[simp]
theorem coe_true : ↑true = True :=
  show (true = true) = True by simp

@[simp]
theorem coe_sort_false : (↥false : Prop) = False :=
  show (false = true) = False by simp

@[simp]
theorem coe_sort_true : (↥true : Prop) = True :=
   show (true = true) = True by simp

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

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  cases h' : decide q with
  | false => exact decide_false (mt h.1 <| of_decide_false h')
  | true => exact decide_true (h.2 <| of_decide_true h')

@[simp]
theorem or_coe_iff (a b : Bool) : a || b ↔ a ∨ b := by cases a <;> cases b <;> exact by decide

@[simp]
theorem and_coe_iff (a b : Bool) : a && b ↔ a ∧ b := by cases a <;> cases b <;> exact by decide

@[simp]
theorem xor_coe_iff (a b : Bool) : xor a b ↔ Xor' (a = true) (b = true) := by
  cases a <;> cases b <;> exact by decide

@[simp]
theorem ite_eq_true_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = true) = if c then a = true else b = true := by by_cases c <;> simp [*]

@[simp]
theorem ite_eq_false_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = false) = if c then a = false else b = false := by
  by_cases c <;> simp [*]

end Bool

-- note: some of the below aligns are coming from the above file, which contains all
-- of the lemmas in the core Lean 3 file `init.data.bool.lemmas` which are not
-- in core Lean 4; others (e.g. `Bool.and_self`) are aligning lean 3 lemmas with
-- lemmas from various places in core Lean 4, e.g. `lean.Init.SimpLemmas`.
#align cond_a_a Bool.cond_a_a
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
#align bxor_self Bool.xor_self
#align bxor_tt Bool.xor_true
#align bxor_ff Bool.xor_false
#align tt_bxor Bool.true_xor
#align ff_bxor Bool.false_xor
#align bnot_bnot Bool.not_not
#align tt_eq_ff_eq_false Bool.true_eq_false_eq_False
#align ff_eq_tt_eq_false Bool.false_eq_true_eq_False
#align eq_ff_eq_not_eq_tt Bool.eq_false_eq_not_eq_true
#align eq_tt_eq_not_eq_ft Bool.eq_true_eq_not_eq_false
#align eq_ff_of_not_eq_tt Bool.eq_false_of_not_eq_true
#align eq_tt_of_not_eq_ff Bool.eq_true_of_not_eq_false
#align band_eq_true_eq_eq_tt_and_eq_tt Bool.and_eq_true_eq_eq_true_and_eq_true
#align bor_eq_true_eq_eq_tt_or_eq_tt Bool.or_eq_true_eq_eq_true_or_eq_true
#align bnot_eq_true_eq_eq_ff Bool.not_eq_true_eq_eq_false
#align band_eq_false_eq_eq_ff_or_eq_ff Bool.and_eq_false_eq_eq_false_or_eq_false
#align bor_eq_false_eq_eq_ff_and_eq_ff Bool.or_eq_false_eq_eq_false_and_eq_false
#align bnot_eq_ff_eq_eq_tt Bool.not_eq_false_eq_eq_true
#align coe_ff Bool.coe_false
#align coe_tt Bool.coe_true
#align coe_sort_ff Bool.coe_sort_false
#align coe_sort_tt Bool.coe_sort_true
#align to_bool_iff Bool.decide_iff
#align to_bool_true Bool.decide_true
#align to_bool_tt Bool.decide_true
#align of_to_bool_true Bool.of_decide_true
#align bool_iff_false Bool.bool_iff_false
#align bool_eq_false Bool.bool_eq_false
#align to_bool_ff_iff Bool.decide_false_iff
#align to_bool_ff Bool.decide_false
#align of_to_bool_ff Bool.of_decide_false
#align to_bool_congr Bool.decide_congr
#align bor_coe_iff Bool.or_coe_iff
#align band_coe_iff Bool.and_coe_iff
#align bxor_coe_iff Bool.xor_coe_iff
#align ite_eq_tt_distrib Bool.ite_eq_true_distrib
#align ite_eq_ff_distrib Bool.ite_eq_false_distrib

#lint
