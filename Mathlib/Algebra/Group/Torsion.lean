/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.SelfInv

/-!
# Torsion-free monoids and groups

This file proves lemmas about torsion-free monoids.
A monoid `M` is *torsion-free* if `n • · : M → M` is injective for all non-zero natural numbers `n`.
-/

public section

open Function

variable {M G : Type*}

section Monoid

instance [AddCommMonoid M] [IsAddTorsionFree M] : Lean.Grind.NoNatZeroDivisors M where
  no_nat_zero_divisors _ _ _ hk := IsAddTorsionFree.nsmul_right_injective hk (add_comm _ _)

variable [Monoid M]

@[to_additive]
instance [Subsingleton M] : HasUniqueRoots M where
  pow_left_injective _ _ _ _ _ := Subsingleton.elim _ _

section IsMulTorsionFree

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

@[to_additive]
lemma Commute.eq_of_pow_eq_pow (hab : Commute a b) (hn : n ≠ 0) (habn : a ^ n = b ^ n) : a = b :=
  eq_of_pow_eq_pow_of_commute hn hab habn

@[to_additive AddCommute.nsmul_right_inj]
lemma Commute.pow_left_inj (hab : Commute a b) (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  ⟨hab.eq_of_pow_eq_pow hn, congrArg (· ^ n)⟩

@[to_additive nsmul_eq_zero_iff_right]
lemma pow_eq_one_iff_left (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  simpa using (Commute.one_right a).pow_left_inj hn

-- We want to use `IsAddTorsion.nsmul_eq_zero_iff` earlier than `smul_eq_zero`.
@[to_additive (attr := simp high)]
lemma pow_eq_one_iff : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [pow_eq_one_iff_left, *]

@[to_additive nsmul_eq_zero_iff_left]
lemma pow_eq_one_iff_right (ha : a ≠ 1) : a ^ n = 1 ↔ n = 0 := by simp [*]

/-- See `sq_eq_one_iff` for a version that holds in rings. -/
@[to_additive two_nsmul_eq_zero]
lemma sq_eq_one : a ^ 2 = 1 ↔ a = 1 := pow_eq_one_iff_left (by lia)

end IsMulTorsionFree

section HasUniqueRoots

variable [HasUniqueRoots M] {n : ℕ} {a b : M}

@[to_additive nsmul_right_injective]
lemma pow_left_injective (hn : n ≠ 0) : Injective fun a : M ↦ a ^ n :=
  HasUniqueRoots.pow_left_injective hn

@[to_additive nsmul_right_inj]
lemma pow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  (pow_left_injective hn).eq_iff

end HasUniqueRoots

end Monoid

section Group

variable [Group G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

@[to_additive]
lemma Commute.eq_of_zpow_eq_zpow (hab : Commute a b) (hn : n ≠ 0) (habn : a ^ n = b ^ n) :
    a = b := by
  cases n
  · exact hab.eq_of_pow_eq_pow (by simpa using hn) (by simpa using habn)
  · exact hab.eq_of_pow_eq_pow (Nat.add_one_ne_zero _) (by simpa using habn)

@[to_additive AddCommute.zsmul_right_inj]
lemma Commute.zpow_left_inj (hab : Commute a b) (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  ⟨hab.eq_of_zpow_eq_zpow hn, congrArg (· ^ n)⟩

@[to_additive IsAddTorsionFree.zsmul_eq_zero_iff_right]
lemma IsMulTorsionFree.zpow_eq_one_iff_left (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  cases n <;> simp_all

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

variable [Group G] [HasUniqueRoots G] {n : ℤ} {a b : G}

@[to_additive zsmul_right_injective]
lemma zpow_left_injective (hn : n ≠ 0) : Injective fun a : G ↦ a ^ n := by
  cases n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natCast_ne_zero] at hn ⊢
    exact pow_left_injective hn
  · simp only [zpow_negSucc]
    exact inv_injective.comp (pow_left_injective (Nat.add_one_ne_zero _))

@[to_additive zsmul_right_inj]
lemma zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  (zpow_left_injective hn).eq_iff

/-- Alias of `zpow_left_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive /-- Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'`
and `zsmul_lt_zsmul_iff'`. -/]
lemma zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn

end CommGroup
