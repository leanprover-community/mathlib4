/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Lemmas about the interaction of power operations with order
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Int

variable {α : Type*}

section OrderedCommGroup
variable [OrderedCommGroup α] {m n : ℤ} {a b : α}

@[to_additive zsmul_left_strictMono]
lemma zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one]
  exact lt_mul_of_one_lt_right' (a ^ n) ha

@[deprecated (since := "2024-09-19")] alias zsmul_strictMono_left := zsmul_left_strictMono

@[to_additive zsmul_pos] lemma one_lt_zpow' (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  simpa using zpow_right_strictMono ha hn

@[to_additive zsmul_left_strictAnti]
lemma zpow_right_strictAnti (ha : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one]
  exact mul_lt_of_lt_one_right' (a ^ n) ha

@[to_additive zsmul_left_inj]
lemma zpow_right_inj (ha : 1 < a) {m n : ℤ} : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_strictMono ha).injective.eq_iff

@[to_additive zsmul_mono_left]
lemma zpow_mono_right (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one]
  exact le_mul_of_one_le_right' ha

@[to_additive (attr := gcongr)]
lemma zpow_le_zpow (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := zpow_mono_right ha h

@[to_additive (attr := gcongr)]
lemma zpow_lt_zpow (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_right_strictMono ha h

@[to_additive]
lemma zpow_le_zpow_iff (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n := (zpow_right_strictMono ha).le_iff_le

@[to_additive]
lemma zpow_lt_zpow_iff (ha : 1 < a) : a ^ m < a ^ n ↔ m < n := (zpow_right_strictMono ha).lt_iff_lt

variable (α)

@[to_additive zsmul_strictMono_right]
lemma zpow_strictMono_left (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]; exact one_lt_zpow' (one_lt_div'.2 hab) hn

@[to_additive zsmul_mono_right]
lemma zpow_mono_left (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn

variable {α}

@[to_additive (attr := gcongr)]
lemma zpow_le_zpow' (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_mono_left α hn h

@[to_additive (attr := gcongr)]
lemma zpow_lt_zpow' (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := zpow_strictMono_left α hn h

end OrderedCommGroup

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {n : ℤ} {a b : α}

@[to_additive] lemma zpow_le_zpow_iff' (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_strictMono_left α hn).le_iff_le

@[to_additive] lemma zpow_lt_zpow_iff' (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_strictMono_left α hn).lt_iff_lt

@[to_additive zsmul_right_injective
"See also `smul_right_injective`. TODO: provide a `NoZeroSMulDivisors` instance. We can't do
that here because importing that definition would create import cycles."]
lemma zpow_left_injective (hn : n ≠ 0) : Injective ((· ^ n) : α → α) := by
  obtain hn | hn := hn.lt_or_lt
  · refine fun a b (hab : a ^ n = b ^ n) ↦
      (zpow_strictMono_left _ <| Int.neg_pos_of_neg hn).injective ?_
    rw [zpow_neg, zpow_neg, hab]
  · exact (zpow_strictMono_left _ hn).injective

@[to_additive zsmul_right_inj]
lemma zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (zpow_left_injective hn).eq_iff

/-- Alias of `zpow_left_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive "Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`."]
lemma zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn

variable (α) in
/-- A nontrivial densely linear ordered commutative group can't be a cyclic group. -/
@[to_additive
  "A nontrivial densely linear ordered additive commutative group can't be a cyclic group."]
theorem not_isCyclic_of_denselyOrdered [DenselyOrdered α] [Nontrivial α] : ¬IsCyclic α := by
  intro h
  rcases exists_zpow_surjective α with ⟨a, ha⟩
  rcases lt_trichotomy a 1 with hlt | rfl | hlt
  · rcases exists_between hlt with ⟨b, hab, hb⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by omega
    rw [← one_lt_inv'] at hlt
    simp_rw [← zpow_lt_zpow_iff hlt]
    simp_all
  · rcases exists_ne (1 : α) with ⟨b, hb⟩
    simpa [hb.symm] using ha b
  · rcases exists_between hlt with ⟨b, hb, hba⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by omega
    simp_rw [← zpow_lt_zpow_iff hlt]
    simp_all

end LinearOrderedCommGroup
