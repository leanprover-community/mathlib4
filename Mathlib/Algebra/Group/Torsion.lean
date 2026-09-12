/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.SelfInv
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Torsion-free monoids and groups

This file proves lemmas about torsion-free monoids.
A monoid `M` is *torsion-free* if `a ^ n = b ^ n` implies `a = b` for all non-zero natural numbers
`n` and all commuting `a b : M`.

## Main statements

* `isMulTorsionFree_iff_pow_left_injective`: A commutative monoid is torsion-free iff
  `· ^ n : M → M` is injective for all non-zero natural numbers `n`.
* `isMulTorsionFree_iff_eq_one_of_pow_eq_one`: A group is torsion-free iff it has no non-trivial
  element `a` such that `a ^ n = 1` for some non-zero natural number `n`.
-/

public section

open Function

variable {M G : Type*}

section Monoid
variable [Monoid M]

@[to_additive] instance Subsingleton.to_isMulTorsionFree [Subsingleton M] : IsMulTorsionFree M :=
  .of_pow_left_injective fun _ _ ↦ injective_of_subsingleton _

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

@[to_additive]
lemma Commute.eq_of_pow_eq_pow (hab : Commute a b) (hn : n ≠ 0) (habn : a ^ n = b ^ n) : a = b :=
  eq_of_pow_eq_pow_of_commute hn hab habn

@[to_additive AddCommute.nsmul_right_inj]
lemma Commute.pow_left_inj (hab : Commute a b) (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  ⟨hab.eq_of_pow_eq_pow hn, congrArg (· ^ n)⟩

@[to_additive nsmul_eq_zero_iff_right]
lemma pow_eq_one_iff_left (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  rw [← (Commute.one_right a).pow_left_inj hn, one_pow]

-- We want to use `IsAddTorsion.nsmul_eq_zero_iff` earlier than `smul_eq_zero`.
@[to_additive (attr := simp high)]
lemma pow_eq_one_iff : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [pow_eq_one_iff_left, *]

@[to_additive nsmul_eq_zero_iff_left]
lemma pow_eq_one_iff_right (ha : a ≠ 1) : a ^ n = 1 ↔ n = 0 := by simp [*]

/-- See `sq_eq_one_iff` for a version that holds in rings. -/
@[to_additive two_nsmul_eq_zero]
lemma sq_eq_one : a ^ 2 = 1 ↔ a = 1 := pow_eq_one_iff_left (by lia)

end Monoid

section CommMonoid
variable [CommMonoid M]

/-- A commutative monoid is torsion-free if and only if power by every non-zero `n : ℕ` is
injective. -/
@[to_additive isAddTorsionFree_iff_nsmul_right_injective
/-- An additive commutative monoid is torsion-free if and only if scalar multiplication by every
non-zero `n : ℕ` is injective. -/]
lemma isMulTorsionFree_iff_pow_left_injective :
    IsMulTorsionFree M ↔ ∀ ⦃n : ℕ⦄, n ≠ 0 → Injective fun a : M ↦ a ^ n where
  mp _ _ hn _ _ := (Commute.all _ _).eq_of_pow_eq_pow hn
  mpr := .of_pow_left_injective

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

@[to_additive nsmul_right_injective]
lemma pow_left_injective (hn : n ≠ 0) : Injective fun a : M ↦ a ^ n :=
  fun _ _ ↦ (Commute.all _ _).eq_of_pow_eq_pow hn

@[to_additive nsmul_right_inj]
lemma pow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (Commute.all _ _).pow_left_inj hn

@[to_additive (attr := deprecated (since := "2026-09-11")) IsAddTorsionFree.nsmul_right_injective]
protected alias IsMulTorsionFree.pow_left_injective := pow_left_injective

end CommMonoid

instance [AddCommMonoid M] [IsAddTorsionFree M] : Lean.Grind.NoNatZeroDivisors M where
  no_nat_zero_divisors _ _ _ hk habk := nsmul_right_injective hk habk

section Group
variable [Group G] {n : ℤ} {a b : G}

/-- A group is torsion-free if and only if it has no non-trivial element of finite order.

See also `isMulTorsionFree_iff_not_isOfFinOrder`. -/
@[to_additive
/-- An additive group is torsion-free if and only if it has no non-zero element of finite order.

See also `isAddTorsionFree_iff_not_isOfFinAddOrder`. -/]
lemma isMulTorsionFree_iff_eq_one_of_pow_eq_one :
    IsMulTorsionFree G ↔ ∀ ⦃n : ℕ⦄, n ≠ 0 → ∀ ⦃a : G⦄, a ^ n = 1 → a = 1 where
  mp _ _ hn _ := (pow_eq_one_iff_left hn).1
  mpr hG := ⟨fun n hn a b hab habn ↦ by
    rw [← div_eq_one]
    refine hG hn ?_
    rw [div_eq_mul_inv, (Commute.inv_right hab).mul_pow, inv_pow, habn, mul_inv_cancel]⟩

@[to_additive]
alias ⟨_, IsMulTorsionFree.of_eq_one_of_pow_eq_one⟩ := isMulTorsionFree_iff_eq_one_of_pow_eq_one

variable [IsMulTorsionFree G]

@[to_additive AddCommute.zsmul_right_inj]
lemma Commute.zpow_left_inj (hab : Commute a b) (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, zpow_natCast, hab.pow_left_inj (mod_cast hn)]
  · rw [zpow_neg, zpow_neg, inv_inj, zpow_natCast, zpow_natCast,
      hab.pow_left_inj (by simpa using hn)]

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_right]
lemma IsMulTorsionFree.zpow_eq_one_iff_left (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  rw [← (Commute.one_right a).zpow_left_inj hn, one_zpow]

-- We want to use `IsAddTorsion.zsmul_eq_zero_iff` earlier than `smul_eq_zero`.
@[to_additive (attr := simp high)]
lemma IsMulTorsionFree.zpow_eq_one_iff : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [zpow_eq_one_iff_left, *]

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_left]
lemma IsMulTorsionFree.zpow_eq_one_iff_right (ha : a ≠ 1) : a ^ n = 1 ↔ n = 0 := by simp [*]

@[to_additive] lemma self_eq_inv : a = a⁻¹ ↔ a = 1 := by rw [← sq_eq_one, sq, mul_eq_one_iff_eq_inv]
@[to_additive] lemma inv_eq_self : a⁻¹ = a ↔ a = 1 := by rw [eq_comm, self_eq_inv]
@[to_additive] lemma self_ne_inv : a ≠ a⁻¹ ↔ a ≠ 1 := self_eq_inv.ne
@[to_additive] lemma inv_ne_self : a⁻¹ ≠ a ↔ a ≠ 1 := inv_eq_self.ne

@[to_additive] lemma isSelfInv_iff_eq_one : IsSelfInv a ↔ a = 1 := inv_eq_self

end Group

section CommGroup
variable [CommGroup G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

@[to_additive zsmul_right_injective]
lemma zpow_left_injective (hn : n ≠ 0) : Injective fun a : G ↦ a ^ n :=
  fun _ _ ↦ ((Commute.all _ _).zpow_left_inj hn).1

@[to_additive zsmul_right_inj]
lemma zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (Commute.all _ _).zpow_left_inj hn

/-- Alias of `zpow_left_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive /-- Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'`
and `zsmul_lt_zsmul_iff'`. -/]
lemma zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn

end CommGroup
