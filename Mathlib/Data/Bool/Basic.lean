/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.LinearOrder

/-!
# Booleans

This file proves various trivial lemmas about Booleans and their
relation to decidable propositions.

## Tags
bool, boolean, Bool, De Morgan

-/

namespace Bool

section

/-!
This section contains lemmas about Booleans which were present in core Lean 3.
The remainder of this file contains lemmas about Booleans from mathlib 3.
-/

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

theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by
  cases a <;> cases b <;> simp

theorem or_eq_false_eq_eq_false_and_eq_false (a b : Bool) :
    ((a || b) = false) = (a = false ∧ b = false) := by
  cases a <;> cases b <;> simp

theorem not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by cases a <;> simp

theorem coe_false : ↑false = False := by simp

theorem coe_true : ↑true = True := by simp

theorem coe_sort_false : (false : Prop) = False := by simp

theorem coe_sort_true : (true : Prop) = True := by simp

theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p := by simp

theorem decide_true {p : Prop} [Decidable p] : p → decide p :=
  (decide_iff p).2

theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1

theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by cases b <;> decide

theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1

theorem decide_false_iff (p : Prop) {_ : Decidable p} : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))

theorem decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (decide_false_iff p).2

theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q :=
  decide_eq_decide.mpr h

theorem coe_xor_iff (a b : Bool) : xor a b ↔ Xor' (a = true) (b = true) := by
  cases a <;> cases b <;> decide

end

theorem dichotomy (b : Bool) : b = false ∨ b = true := by cases b <;> simp

theorem not_ne_id : not ≠ id := fun h ↦ false_ne_true <| congrFun h true

theorem or_inl {a b : Bool} (H : a) : a || b := by simp [H]

theorem or_inr {a b : Bool} (H : b) : a || b := by cases a <;> simp [H]

theorem and_elim_left : ∀ {a b : Bool}, a && b → a := by decide

theorem and_intro : ∀ {a b : Bool}, a → b → a && b := by decide

theorem and_elim_right : ∀ {a b : Bool}, a && b → b := by decide

lemma eq_not_iff : ∀ {a b : Bool}, a = !b ↔ a ≠ b := by decide

lemma not_eq_iff : ∀ {a b : Bool}, !a = b ↔ a ≠ b := by decide

theorem ne_not {a b : Bool} : a ≠ !b ↔ a = b :=
  not_eq_not

lemma not_ne_self : ∀ b : Bool, (!b) ≠ b := by decide

lemma self_ne_not : ∀ b : Bool, b ≠ !b := by decide

lemma eq_or_eq_not : ∀ a b, a = b ∨ a = !b := by decide

-- TODO naming issue: these two `not` are different.
theorem not_iff_not : ∀ {b : Bool}, !b ↔ ¬b := by simp

theorem eq_true_of_not_eq_false' {a : Bool} : !a = false → a = true := by
  cases a <;> decide

theorem eq_false_of_not_eq_true' {a : Bool} : !a = true → a = false := by
  cases a <;> decide

theorem bne_eq_xor : bne = xor := by constructor

attribute [simp] xor_assoc

theorem xor_iff_ne : ∀ {x y : Bool}, xor x y = true ↔ x ≠ y := by decide

/-! ### De Morgan's laws for Booleans -/

instance linearOrder : LinearOrder Bool where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := by decide
  max_def := by decide
  min_def := by decide

theorem lt_iff : ∀ {x y : Bool}, x < y ↔ x = false ∧ y = true := by decide

@[simp]
theorem false_lt_true : false < true :=
  lt_iff.2 ⟨rfl, rfl⟩

theorem le_iff_imp : ∀ {x y : Bool}, x ≤ y ↔ x → y := by decide

theorem and_le_left : ∀ x y : Bool, (x && y) ≤ x := by decide

theorem and_le_right : ∀ x y : Bool, (x && y) ≤ y := by decide

theorem le_and : ∀ {x y z : Bool}, x ≤ y → x ≤ z → x ≤ (y && z) := by decide

theorem left_le_or : ∀ x y : Bool, x ≤ (x || y) := by decide

theorem right_le_or : ∀ x y : Bool, y ≤ (x || y) := by decide

theorem or_le : ∀ {x y z}, x ≤ z → y ≤ z → (x || y) ≤ z := by decide

/-- convert a `ℕ` to a `Bool`, `0 -> false`, everything else -> `true` -/
def ofNat (n : Nat) : Bool :=
  decide (n ≠ 0)

@[simp] lemma toNat_beq_zero (b : Bool) : (b.toNat == 0) = !b := by cases b <;> rfl
@[simp] lemma toNat_bne_zero (b : Bool) : (b.toNat != 0) =  b := by simp [bne]
@[simp] lemma toNat_beq_one (b : Bool) : (b.toNat == 1) =  b := by cases b <;> rfl
@[simp] lemma toNat_bne_one (b : Bool) : (b.toNat != 1) = !b := by simp [bne]

theorem ofNat_le_ofNat {n m : Nat} (h : n ≤ m) : ofNat n ≤ ofNat m := by
  simp only [ofNat, ne_eq, _root_.decide_not]
  cases Nat.decEq n 0 with
  | isTrue hn => rw [_root_.decide_eq_true hn]; exact Bool.false_le _
  | isFalse hn =>
    cases Nat.decEq m 0 with
    | isFalse hm => rw [_root_.decide_eq_false hm]; exact Bool.le_true _
    | isTrue hm => subst hm; have h := Nat.le_antisymm h (Nat.zero_le n); contradiction

theorem toNat_le_toNat {b₀ b₁ : Bool} (h : b₀ ≤ b₁) : toNat b₀ ≤ toNat b₁ := by
  cases b₀ <;> cases b₁ <;> simp_all +decide

theorem ofNat_toNat (b : Bool) : ofNat (toNat b) = b := by
  cases b <;> rfl

@[simp]
theorem injective_iff {α : Sort*} {f : Bool → α} : Function.Injective f ↔ f false ≠ f true :=
  ⟨fun Hinj Heq ↦ false_ne_true (Hinj Heq), fun H x y hxy ↦ by
    cases x <;> cases y
    · rfl
    · exact (H hxy).elim
    · exact (H hxy.symm).elim
    · rfl⟩

/-- **Kaminski's Equation** -/
theorem apply_apply_apply (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases x <;> cases h₁ : f true <;> cases h₂ : f false <;> simp only [h₁, h₂]

/-- `xor3 x y c` is `((x XOR y) XOR c)`. -/
protected def xor3 (x y c : Bool) :=
  xor (xor x y) c

/-- `carry x y c` is `x && y || x && c || y && c`. -/
protected def carry (x y c : Bool) :=
  x && y || x && c || y && c

end Bool
