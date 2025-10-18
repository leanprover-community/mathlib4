/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Torsion-free monoids and groups

This file proves lemmas about torsion-free monoids.
A monoid `M` is *torsion-free* if `n • · : M → M` is injective for all non-zero natural numbers `n`.
-/

open Function

variable {M G : Type*}

section Monoid
variable [Monoid M]

instance [AddCommMonoid M] [IsAddTorsionFree M] : Lean.Grind.NoNatZeroDivisors M where
  no_nat_zero_divisors _ _ _ hk habk := IsAddTorsionFree.nsmul_right_injective hk habk

@[to_additive] instance Subsingleton.to_isMulTorsionFree [Subsingleton M] : IsMulTorsionFree M where
  pow_left_injective _ _ := injective_of_subsingleton _

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

@[to_additive nsmul_right_injective]
lemma pow_left_injective (hn : n ≠ 0) : Injective fun a : M ↦ a ^ n :=
  IsMulTorsionFree.pow_left_injective hn

@[to_additive nsmul_right_inj]
lemma pow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (pow_left_injective hn).eq_iff

@[to_additive]
lemma IsMulTorsionFree.pow_eq_one_iff (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 :=
  ⟨fun h ↦ by rwa [← pow_left_inj hn, one_pow], fun h ↦ by rw [h, one_pow]⟩

@[to_additive]
lemma IsMulTorsionFree.pow_eq_one_iff' (ha : a ≠ 1) : a ^ n = 1 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, pow_zero]⟩
  by_contra h'
  simpa [h] using (pow_left_injective h').ne ha

/-- See `sq_eq_one_iff` for a version that holds in rings. -/
@[to_additive two_nsmul_eq_zero]
lemma sq_eq_one : a ^ 2 = 1 ↔ a = 1 := IsMulTorsionFree.pow_eq_one_iff (by cutsat)

end Monoid

section Group
variable [Group G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

@[to_additive zsmul_right_injective]
lemma zpow_left_injective : ∀ {n : ℤ}, n ≠ 0 → Injective fun a : G ↦ a ^ n
  | (n + 1 : ℕ), _ => by
    simpa [← Int.natCast_one, ← Int.natCast_add] using pow_left_injective n.succ_ne_zero
  | .negSucc n, _ => by simpa using inv_injective.comp (pow_left_injective n.succ_ne_zero)

@[to_additive zsmul_right_inj]
lemma zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (zpow_left_injective hn).eq_iff

/-- Alias of `zpow_left_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive /-- Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'`
and `zsmul_lt_zsmul_iff'`. -/]
lemma zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn

@[to_additive] lemma self_eq_inv : a = a⁻¹ ↔ a = 1 := by rw [← sq_eq_one, sq, mul_eq_one_iff_eq_inv]
@[to_additive] lemma inv_eq_self : a⁻¹ = a ↔ a = 1 := by rw [eq_comm, self_eq_inv]
@[to_additive] lemma self_ne_inv : a ≠ a⁻¹ ↔ a ≠ 1 := self_eq_inv.ne
@[to_additive] lemma inv_ne_self : a⁻¹ ≠ a ↔ a ≠ 1 := inv_eq_self.ne

end Group
