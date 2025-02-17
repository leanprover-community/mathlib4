/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
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

@[to_additive zsmul_pos] lemma one_lt_zpow (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  simpa using zpow_right_strictMono ha hn

@[deprecated (since := "2024-11-13")] alias one_lt_zpow' := one_lt_zpow

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

@[deprecated (since := "2024-11-13")] alias zpow_mono_right := zpow_right_mono

@[to_additive (attr := gcongr) zsmul_le_zsmul_left]
lemma zpow_le_zpow_right (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono ha h

@[deprecated (since := "2024-11-13")] alias zpow_le_zpow := zpow_le_zpow_right

@[to_additive (attr := gcongr) zsmul_lt_zsmul_left]
lemma zpow_lt_zpow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_right_strictMono ha h

@[deprecated (since := "2024-11-13")] alias zpow_lt_zpow := zpow_lt_zpow_right

@[to_additive zsmul_le_zsmul_iff_left]
lemma zpow_le_zpow_iff_right (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono ha).le_iff_le

@[deprecated (since := "2024-11-13")] alias zpow_le_zpow_iff := zpow_le_zpow_iff_right

@[to_additive zsmul_lt_zsmul_iff_left]
lemma zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono ha).lt_iff_lt

@[deprecated (since := "2024-11-13")] alias zpow_lt_zpow_iff := zpow_lt_zpow_iff_right

variable (α)

@[to_additive zsmul_strictMono_right]
lemma zpow_left_strictMono (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]; exact one_lt_zpow (one_lt_div'.2 hab) hn

@[deprecated (since := "2024-11-13")] alias zpow_strictMono_left := zpow_left_strictMono

@[to_additive zsmul_mono_right]
lemma zpow_left_mono (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn

@[deprecated (since := "2024-11-13")] alias zpow_mono_left := zpow_left_mono

variable {α}

@[to_additive (attr := gcongr) zsmul_le_zsmul_right]
lemma zpow_le_zpow_left (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_left_mono α hn h

@[deprecated (since := "2024-11-13")] alias zpow_le_zpow' := zpow_le_zpow_left

@[to_additive (attr := gcongr) zsmul_lt_zsmul_right]
lemma zpow_lt_zpow_left (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := zpow_left_strictMono α hn h

@[deprecated (since := "2024-11-13")] alias zpow_lt_zpow' := zpow_lt_zpow_left

end OrderedCommGroup

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {n : ℤ} {a b : α}

@[to_additive eq_zero_of_neg_eq]
theorem eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
  match lt_trichotomy a 1 with
  | Or.inl h₁ =>
    have : 1 < a := h ▸ one_lt_inv_of_inv h₁
    absurd h₁ this.asymm
  | Or.inr (Or.inl h₁) => h₁
  | Or.inr (Or.inr h₁) =>
    have : a < 1 := h ▸ inv_lt_one'.mpr h₁
    absurd h₁ this.asymm

@[to_additive exists_zero_lt]
theorem exists_one_lt' [Nontrivial α] : ∃ a : α, 1 < a := by
  obtain ⟨y, hy⟩ := Decidable.exists_ne (1 : α)
  obtain h|h := hy.lt_or_lt
  · exact ⟨y⁻¹, one_lt_inv'.mpr h⟩
  · exact ⟨y, h⟩

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_noMaxOrder [Nontrivial α] : NoMaxOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a * y, lt_mul_of_one_lt_right' a hy⟩⟩

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_noMinOrder [Nontrivial α] : NoMinOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a / y, (div_lt_self_iff a).mpr hy⟩⟩

@[to_additive (attr := simp)]
theorem inv_le_self_iff : a⁻¹ ≤ a ↔ 1 ≤ a := by simp [inv_le_iff_one_le_mul']

@[to_additive (attr := simp)]
theorem inv_lt_self_iff : a⁻¹ < a ↔ 1 < a := by simp [inv_lt_iff_one_lt_mul]

@[to_additive (attr := simp)]
theorem le_inv_self_iff : a ≤ a⁻¹ ↔ a ≤ 1 := by simp [← not_iff_not]

@[to_additive (attr := simp)]
theorem lt_inv_self_iff : a < a⁻¹ ↔ a < 1 := by simp [← not_iff_not]

@[to_additive zsmul_le_zsmul_iff_right]
lemma zpow_le_zpow_iff_left (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_left_strictMono α hn).le_iff_le

@[deprecated (since := "2024-11-13")] alias zpow_le_zpow_iff' := zpow_le_zpow_iff_left

@[to_additive zsmul_lt_zsmul_iff_right]
lemma zpow_lt_zpow_iff_left (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_left_strictMono α hn).lt_iff_lt

@[deprecated (since := "2024-11-13")] alias zpow_lt_zpow_iff' := zpow_lt_zpow_iff_left

@[to_additive zsmul_right_injective
"See also `smul_right_injective`. TODO: provide a `NoZeroSMulDivisors` instance. We can't do
that here because importing that definition would create import cycles."]
lemma zpow_left_injective (hn : n ≠ 0) : Injective ((· ^ n) : α → α) := by
  obtain hn | hn := hn.lt_or_lt
  · refine fun a b (hab : a ^ n = b ^ n) ↦
      (zpow_left_strictMono _ <| Int.neg_pos_of_neg hn).injective ?_
    rw [zpow_neg, zpow_neg, hab]
  · exact (zpow_left_strictMono _ hn).injective

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

section NormNumLemmas

/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures. -/
variable [OrderedCommGroup α] {a b : α}

@[to_additive (attr := gcongr) neg_le_neg]
theorem inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ :=
  inv_le_inv_iff.mpr

@[to_additive (attr := gcongr) neg_lt_neg]
theorem inv_lt_inv' : a < b → b⁻¹ < a⁻¹ :=
  inv_lt_inv_iff.mpr

--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 :=
  inv_lt_one_iff_one_lt.mpr

--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 :=
  inv_le_one'.mpr

@[to_additive neg_nonneg_of_nonpos]
theorem one_le_inv_of_le_one : a ≤ 1 → 1 ≤ a⁻¹ :=
  one_le_inv'.mpr

end NormNumLemmas
