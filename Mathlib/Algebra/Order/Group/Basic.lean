/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Lemmas about the interaction of power operations with order
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Int

variable {α : Type*}

section OrderedCommGroup
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : ℤ} {a b : α}

@[to_additive zsmul_left_strictMono]
lemma zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one]
  exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive zsmul_left_strictAnti]
lemma zpow_right_strictAnti (ha : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one]
  exact mul_lt_of_lt_one_right' (a ^ n) ha

@[to_additive zsmul_left_inj]
lemma zpow_right_inj (ha : 1 < a) {m n : ℤ} : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_strictMono ha).injective.eq_iff

@[to_additive zsmul_left_mono]
lemma zpow_right_mono (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one]
  exact le_mul_of_one_le_right' ha

@[to_additive (attr := gcongr) zsmul_le_zsmul_left]
lemma zpow_le_zpow_right (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono ha h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_left]
lemma zpow_lt_zpow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_right_strictMono ha h

@[to_additive zsmul_le_zsmul_iff_left]
lemma zpow_le_zpow_iff_right (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono ha).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_left]
lemma zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono ha).lt_iff_lt

variable (α)

@[to_additive zsmul_strictMono_right]
lemma zpow_left_strictMono (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]; exact one_lt_zpow (one_lt_div'.2 hab) hn

@[to_additive zsmul_mono_right]
lemma zpow_left_mono (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn

variable {α}

@[to_additive (attr := gcongr) zsmul_le_zsmul_right]
lemma zpow_le_zpow_left (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_left_mono α hn h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_right]
lemma zpow_lt_zpow_left (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := zpow_left_strictMono α hn h

end OrderedCommGroup

section LinearOrderedCommGroup

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {n : ℤ} {a b : α}

@[to_additive zsmul_le_zsmul_iff_right]
lemma zpow_le_zpow_iff_left (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_left_strictMono α hn).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_right]
lemma zpow_lt_zpow_iff_left (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_left_strictMono α hn).lt_iff_lt

@[to_additive]
instance : IsMulTorsionFree α where pow_left_injective _ hn := (pow_left_strictMono hn).injective

variable (α) in
/-- A nontrivial densely linear ordered commutative group can't be a cyclic group. -/
@[to_additive
  /-- A nontrivial densely linear ordered additive commutative group can't be a cyclic group. -/]
theorem not_isCyclic_of_denselyOrdered [DenselyOrdered α] [Nontrivial α] : ¬IsCyclic α := by
  intro h
  rcases exists_zpow_surjective α with ⟨a, ha⟩
  rcases lt_trichotomy a 1 with hlt | rfl | hlt
  · rcases exists_between hlt with ⟨b, hab, hb⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by omega
    rw [← one_lt_inv'] at hlt
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all
  · rcases exists_ne (1 : α) with ⟨b, hb⟩
    simpa [hb.symm] using ha b
  · rcases exists_between hlt with ⟨b, hb, hba⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by omega
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all

end LinearOrderedCommGroup
