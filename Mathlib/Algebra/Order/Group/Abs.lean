/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Abs
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Order.MinMax

#align_import algebra.order.group.abs from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# Absolute values in ordered groups.
-/


variable {α : Type*}

open Function

section CovariantAddLe

section Neg

-- see Note [lower instance priority]
/-- `abs a` is the absolute value of `a`. -/
@[to_additive "`abs a` is the absolute value of `a`"]
instance (priority := 100) Inv.toHasAbs [Inv α] [Sup α] : Abs α :=
  ⟨fun a => a ⊔ a⁻¹⟩
#align has_inv.to_has_abs Inv.toHasAbs
#align has_neg.to_has_abs Neg.toHasAbs

@[to_additive]
theorem abs_eq_sup_inv [Inv α] [Sup α] (a : α) : |a| = a ⊔ a⁻¹ :=
  rfl
#align abs_eq_sup_inv abs_eq_sup_inv
#align abs_eq_sup_neg abs_eq_sup_neg

variable [Neg α] [LinearOrder α] {a b : α}

theorem abs_eq_max_neg : abs a = max a (-a) :=
  rfl
#align abs_eq_max_neg abs_eq_max_neg

theorem abs_choice (x : α) : |x| = x ∨ |x| = -x :=
  max_choice _ _
#align abs_choice abs_choice

theorem abs_le' : |a| ≤ b ↔ a ≤ b ∧ -a ≤ b :=
  max_le_iff
#align abs_le' abs_le'

theorem le_abs : a ≤ |b| ↔ a ≤ b ∨ a ≤ -b :=
  le_max_iff
#align le_abs le_abs

theorem le_abs_self (a : α) : a ≤ |a| :=
  le_max_left _ _
#align le_abs_self le_abs_self

theorem neg_le_abs_self (a : α) : -a ≤ |a| :=
  le_max_right _ _
#align neg_le_abs_self neg_le_abs_self

theorem lt_abs : a < |b| ↔ a < b ∨ a < -b :=
  lt_max_iff
#align lt_abs lt_abs

theorem abs_le_abs (h₀ : a ≤ b) (h₁ : -a ≤ b) : |a| ≤ |b| :=
  (abs_le'.2 ⟨h₀, h₁⟩).trans (le_abs_self b)
#align abs_le_abs abs_le_abs

theorem abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P |a| :=
  sup_ind _ _ h1 h2
#align abs_by_cases abs_by_cases

end Neg

section AddGroup

variable [AddGroup α] [LinearOrder α]

@[simp]
theorem abs_neg (a : α) : |(-a)| = |a| := by rw [abs_eq_max_neg, max_comm, neg_neg, abs_eq_max_neg]
#align abs_neg abs_neg

theorem eq_or_eq_neg_of_abs_eq {a b : α} (h : |a| = b) : a = b ∨ a = -b := by
  simpa only [← h, eq_comm (a := |a|), neg_eq_iff_eq_neg] using abs_choice a
#align eq_or_eq_neg_of_abs_eq eq_or_eq_neg_of_abs_eq

theorem abs_eq_abs {a b : α} : |a| = |b| ↔ a = b ∨ a = -b := by
  refine' ⟨fun h => _, fun h => _⟩
  · obtain rfl | rfl := eq_or_eq_neg_of_abs_eq h <;>
      simpa only [neg_eq_iff_eq_neg (a := |b|), neg_inj, or_comm] using abs_choice b
  · cases' h with h h <;>
    simp [h, abs_neg]
#align abs_eq_abs abs_eq_abs

theorem abs_sub_comm (a b : α) : |a - b| = |b - a| :=
  calc
    |a - b| = |(-(b - a))| := congr_arg _ (neg_sub b a).symm
    _ = |b - a| := abs_neg (b - a)
#align abs_sub_comm abs_sub_comm

variable [CovariantClass α α (· + ·) (· ≤ ·)] {a b c : α}

theorem abs_of_nonneg (h : 0 ≤ a) : |a| = a :=
  max_eq_left <| (neg_nonpos.2 h).trans h
#align abs_of_nonneg abs_of_nonneg

theorem abs_of_pos (h : 0 < a) : |a| = a :=
  abs_of_nonneg h.le
#align abs_of_pos abs_of_pos

theorem abs_of_nonpos (h : a ≤ 0) : |a| = -a :=
  max_eq_right <| h.trans (neg_nonneg.2 h)
#align abs_of_nonpos abs_of_nonpos

theorem abs_of_neg (h : a < 0) : |a| = -a :=
  abs_of_nonpos h.le
#align abs_of_neg abs_of_neg

theorem abs_le_abs_of_nonneg (ha : 0 ≤ a) (hab : a ≤ b) : |a| ≤ |b| := by
  rwa [abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]
#align abs_le_abs_of_nonneg abs_le_abs_of_nonneg

@[simp]
theorem abs_zero : |0| = (0 : α) :=
  abs_of_nonneg le_rfl
#align abs_zero abs_zero

@[simp]
theorem abs_pos : 0 < |a| ↔ a ≠ 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · simp [abs_of_neg ha, neg_pos, ha.ne, ha]
  · simp
  · simp [abs_of_pos ha, ha, ha.ne.symm]
#align abs_pos abs_pos

theorem abs_pos_of_pos (h : 0 < a) : 0 < |a| :=
  abs_pos.2 h.ne.symm
#align abs_pos_of_pos abs_pos_of_pos

theorem abs_pos_of_neg (h : a < 0) : 0 < |a| :=
  abs_pos.2 h.ne
#align abs_pos_of_neg abs_pos_of_neg

theorem neg_abs_le_self (a : α) : -|a| ≤ a := by
  rcases le_total 0 a with h | h
  · calc
      -|a| = -a := congr_arg Neg.neg (abs_of_nonneg h)
      _ ≤ 0 := neg_nonpos.mpr h
      _ ≤ a := h
  · calc
      -|a| = - -a := congr_arg Neg.neg (abs_of_nonpos h)
      _ ≤ a := (neg_neg a).le
#align neg_abs_le_self neg_abs_le_self

theorem add_abs_nonneg (a : α) : 0 ≤ a + |a| := by
  rw [← add_right_neg a]
  apply add_le_add_left
  exact neg_le_abs_self a
#align add_abs_nonneg add_abs_nonneg

theorem neg_abs_le_neg (a : α) : -|a| ≤ -a := by simpa using neg_abs_le_self (-a)
#align neg_abs_le_neg neg_abs_le_neg

@[simp]
theorem abs_nonneg (a : α) : 0 ≤ |a| :=
  (le_total 0 a).elim (fun h => h.trans (le_abs_self a)) fun h =>
    (neg_nonneg.2 h).trans <| neg_le_abs_self a
#align abs_nonneg abs_nonneg

@[simp]
theorem abs_abs (a : α) : |(|a|)| = |a| :=
  abs_of_nonneg <| abs_nonneg a
#align abs_abs abs_abs

@[simp]
theorem abs_eq_zero : |a| = 0 ↔ a = 0 :=
  Decidable.not_iff_not.1 <| ne_comm.trans <| (abs_nonneg a).lt_iff_ne.symm.trans abs_pos
#align abs_eq_zero abs_eq_zero

@[simp]
theorem abs_nonpos_iff {a : α} : |a| ≤ 0 ↔ a = 0 :=
  (abs_nonneg a).le_iff_eq.trans abs_eq_zero
#align abs_nonpos_iff abs_nonpos_iff

variable [CovariantClass α α (swap (· + ·)) (· ≤ ·)]

theorem abs_le_abs_of_nonpos (ha : a ≤ 0) (hab : b ≤ a) : |a| ≤ |b| := by
  rw [abs_of_nonpos ha, abs_of_nonpos (hab.trans ha)]
  exact neg_le_neg_iff.mpr hab
#align abs_le_abs_of_nonpos abs_le_abs_of_nonpos

theorem abs_lt : |a| < b ↔ -b < a ∧ a < b :=
  max_lt_iff.trans <| and_comm.trans <| by rw [neg_lt]
#align abs_lt abs_lt

theorem neg_lt_of_abs_lt (h : |a| < b) : -b < a :=
  (abs_lt.mp h).1
#align neg_lt_of_abs_lt neg_lt_of_abs_lt

theorem lt_of_abs_lt (h : |a| < b) : a < b :=
  (abs_lt.mp h).2
#align lt_of_abs_lt lt_of_abs_lt

theorem max_sub_min_eq_abs' (a b : α) : max a b - min a b = |a - b| := by
  rcases le_total a b with ab | ba
  · rw [max_eq_right ab, min_eq_left ab, abs_of_nonpos, neg_sub]
    rwa [sub_nonpos]
  · rw [max_eq_left ba, min_eq_right ba, abs_of_nonneg]
    rwa [sub_nonneg]
#align max_sub_min_eq_abs' max_sub_min_eq_abs'

theorem max_sub_min_eq_abs (a b : α) : max a b - min a b = |b - a| := by
  rw [abs_sub_comm]
  exact max_sub_min_eq_abs' _ _
#align max_sub_min_eq_abs max_sub_min_eq_abs

end AddGroup

end CovariantAddLe

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b c d : α}

-- Porting note:
-- Lean can perfectly well find this instance,
-- but in the rewrites below it is going looking for it without having fixed `α`.
example : CovariantClass α α (swap fun x y ↦ x + y) fun x y ↦ x ≤ y := inferInstance

theorem abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b := by rw [abs_le', and_comm, @neg_le α]
#align abs_le abs_le

theorem le_abs' : a ≤ |b| ↔ b ≤ -a ∨ a ≤ b := by rw [le_abs, or_comm, @le_neg α]
#align le_abs' le_abs'

theorem neg_le_of_abs_le (h : |a| ≤ b) : -b ≤ a :=
  (abs_le.mp h).1
#align neg_le_of_abs_le neg_le_of_abs_le

theorem le_of_abs_le (h : |a| ≤ b) : a ≤ b :=
  (abs_le.mp h).2
#align le_of_abs_le le_of_abs_le

@[to_additive]
theorem apply_abs_le_mul_of_one_le' {β : Type*} [MulOneClass β] [Preorder β]
    [CovariantClass β β (· * ·) (· ≤ ·)] [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {f : α → β}
    {a : α} (h₁ : 1 ≤ f a) (h₂ : 1 ≤ f (-a)) : f |a| ≤ f a * f (-a) :=
  (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂
#align apply_abs_le_mul_of_one_le' apply_abs_le_mul_of_one_le'
#align apply_abs_le_add_of_nonneg' apply_abs_le_add_of_nonneg'

@[to_additive]
theorem apply_abs_le_mul_of_one_le {β : Type*} [MulOneClass β] [Preorder β]
    [CovariantClass β β (· * ·) (· ≤ ·)] [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {f : α → β}
    (h : ∀ x, 1 ≤ f x) (a : α) : f |a| ≤ f a * f (-a) :=
  apply_abs_le_mul_of_one_le' (h _) (h _)
#align apply_abs_le_mul_of_one_le apply_abs_le_mul_of_one_le
#align apply_abs_le_add_of_nonneg apply_abs_le_add_of_nonneg

/-- The **triangle inequality** in `LinearOrderedAddCommGroup`s. -/
theorem abs_add (a b : α) : |a + b| ≤ |a| + |b| :=
  abs_le.2
    ⟨(neg_add |a| |b|).symm ▸
        add_le_add ((@neg_le α ..).2 <| neg_le_abs_self _) ((@neg_le α ..).2 <| neg_le_abs_self _),
      add_le_add (le_abs_self _) (le_abs_self _)⟩
#align abs_add abs_add

theorem abs_add' (a b : α) : |a| ≤ |b| + |b + a| := by simpa using abs_add (-b) (b + a)
#align abs_add' abs_add'

theorem abs_sub (a b : α) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg, ← abs_neg b]
  exact abs_add a _
#align abs_sub abs_sub

theorem abs_sub_le_iff : |a - b| ≤ c ↔ a - b ≤ c ∧ b - a ≤ c := by
  rw [abs_le, neg_le_sub_iff_le_add, sub_le_iff_le_add', and_comm, sub_le_iff_le_add']
#align abs_sub_le_iff abs_sub_le_iff

theorem abs_sub_lt_iff : |a - b| < c ↔ a - b < c ∧ b - a < c := by
  rw [@abs_lt α, neg_lt_sub_iff_lt_add', sub_lt_iff_lt_add', and_comm, sub_lt_iff_lt_add']
#align abs_sub_lt_iff abs_sub_lt_iff

theorem sub_le_of_abs_sub_le_left (h : |a - b| ≤ c) : b - c ≤ a :=
  sub_le_comm.1 <| (abs_sub_le_iff.1 h).2
#align sub_le_of_abs_sub_le_left sub_le_of_abs_sub_le_left

theorem sub_le_of_abs_sub_le_right (h : |a - b| ≤ c) : a - c ≤ b :=
  sub_le_of_abs_sub_le_left (abs_sub_comm a b ▸ h)
#align sub_le_of_abs_sub_le_right sub_le_of_abs_sub_le_right

theorem sub_lt_of_abs_sub_lt_left (h : |a - b| < c) : b - c < a :=
  sub_lt_comm.1 <| (abs_sub_lt_iff.1 h).2
#align sub_lt_of_abs_sub_lt_left sub_lt_of_abs_sub_lt_left

theorem sub_lt_of_abs_sub_lt_right (h : |a - b| < c) : a - c < b :=
  sub_lt_of_abs_sub_lt_left (abs_sub_comm a b ▸ h)
#align sub_lt_of_abs_sub_lt_right sub_lt_of_abs_sub_lt_right

theorem abs_sub_abs_le_abs_sub (a b : α) : |a| - |b| ≤ |a - b| :=
  (@sub_le_iff_le_add α ..).2 <|
    calc
      |a| = |a - b + b| := by rw [sub_add_cancel]
      _ ≤ |a - b| + |b| := abs_add _ _
#align abs_sub_abs_le_abs_sub abs_sub_abs_le_abs_sub

theorem abs_abs_sub_abs_le_abs_sub (a b : α) : |(|a| - |b|)| ≤ |a - b| :=
  abs_sub_le_iff.2
    ⟨abs_sub_abs_le_abs_sub _ _, by rw [abs_sub_comm]; apply abs_sub_abs_le_abs_sub⟩
#align abs_abs_sub_abs_le_abs_sub abs_abs_sub_abs_le_abs_sub

theorem abs_eq (hb : 0 ≤ b) : |a| = b ↔ a = b ∨ a = -b := by
  refine' ⟨eq_or_eq_neg_of_abs_eq, _⟩
  rintro (rfl | rfl) <;> simp only [abs_neg, abs_of_nonneg hb]
#align abs_eq abs_eq

theorem abs_le_max_abs_abs (hab : a ≤ b) (hbc : b ≤ c) : |b| ≤ max |a| |c| :=
  abs_le'.2
    ⟨by simp [hbc.trans (le_abs_self c)], by
      simp [((@neg_le_neg_iff α ..).mpr hab).trans (neg_le_abs_self a)]⟩
#align abs_le_max_abs_abs abs_le_max_abs_abs

theorem min_abs_abs_le_abs_max : min |a| |b| ≤ |max a b| :=
  (le_total a b).elim (fun h => (min_le_right _ _).trans_eq <| congr_arg _ (max_eq_right h).symm)
    fun h => (min_le_left _ _).trans_eq <| congr_arg _ (max_eq_left h).symm
#align min_abs_abs_le_abs_max min_abs_abs_le_abs_max

theorem min_abs_abs_le_abs_min : min |a| |b| ≤ |min a b| :=
  (le_total a b).elim (fun h => (min_le_left _ _).trans_eq <| congr_arg _ (min_eq_left h).symm)
    fun h => (min_le_right _ _).trans_eq <| congr_arg _ (min_eq_right h).symm
#align min_abs_abs_le_abs_min min_abs_abs_le_abs_min

theorem abs_max_le_max_abs_abs : |max a b| ≤ max |a| |b| :=
  (le_total a b).elim (fun h => (congr_arg _ <| max_eq_right h).trans_le <| le_max_right _ _)
    fun h => (congr_arg _ <| max_eq_left h).trans_le <| le_max_left _ _
#align abs_max_le_max_abs_abs abs_max_le_max_abs_abs

theorem abs_min_le_max_abs_abs : |min a b| ≤ max |a| |b| :=
  (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
    (congr_arg _ <| min_eq_right h).trans_le <| le_max_right _ _
#align abs_min_le_max_abs_abs abs_min_le_max_abs_abs

theorem eq_of_abs_sub_eq_zero {a b : α} (h : |a - b| = 0) : a = b :=
  sub_eq_zero.1 <| abs_eq_zero.1 h
#align eq_of_abs_sub_eq_zero eq_of_abs_sub_eq_zero

theorem abs_sub_le (a b c : α) : |a - c| ≤ |a - b| + |b - c| :=
  calc
    |a - c| = |a - b + (b - c)| := by rw [sub_add_sub_cancel]
    _ ≤ |a - b| + |b - c| := abs_add _ _
#align abs_sub_le abs_sub_le

theorem abs_add_three (a b c : α) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
#align abs_add_three abs_add_three

theorem dist_bdd_within_interval {a b lb ub : α} (hal : lb ≤ a) (hau : a ≤ ub) (hbl : lb ≤ b)
    (hbu : b ≤ ub) : |a - b| ≤ ub - lb :=
  abs_sub_le_iff.2 ⟨sub_le_sub hau hbl, sub_le_sub hbu hal⟩
#align dist_bdd_within_interval dist_bdd_within_interval

theorem eq_of_abs_sub_nonpos (h : |a - b| ≤ 0) : a = b :=
  eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))
#align eq_of_abs_sub_nonpos eq_of_abs_sub_nonpos

@[simp]
theorem abs_eq_self : |a| = a ↔ 0 ≤ a := by
  rw [abs_eq_max_neg, max_eq_left_iff, neg_le_self_iff]
#align abs_eq_self abs_eq_self

@[simp]
theorem abs_eq_neg_self : |a| = -a ↔ a ≤ 0 := by
  rw [abs_eq_max_neg, max_eq_right_iff, le_neg_self_iff]
#align abs_eq_neg_self abs_eq_neg_self

/-- For an element `a` of a linear ordered ring, either `abs a = a` and `0 ≤ a`,
    or `abs a = -a` and `a < 0`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem abs_cases (a : α) : |a| = a ∧ 0 ≤ a ∨ |a| = -a ∧ a < 0 := by
  by_cases h : 0 ≤ a
  · left
    exact ⟨abs_eq_self.mpr h, h⟩
  · right
    push_neg at h
    exact ⟨abs_eq_neg_self.mpr (le_of_lt h), h⟩
#align abs_cases abs_cases

@[simp]
theorem max_zero_add_max_neg_zero_eq_abs_self (a : α) : max a 0 + max (-a) 0 = |a| := by
  symm
  rcases le_total 0 a with (ha | ha) <;> simp [ha]
#align max_zero_add_max_neg_zero_eq_abs_self max_zero_add_max_neg_zero_eq_abs_self

end LinearOrderedAddCommGroup
