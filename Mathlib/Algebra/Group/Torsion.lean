/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.MinImports
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Torsion-free monoids and groups

This file defines torsion-free monoids as those monoids `M` for which `n • · : M → M` is injective
for all non-zero natural number `n`.

## TODO

Replace `Monoid.IsTorsionFree`, which is mathematically incorrect for monoids which are not groups.
This probably means we also want to get rid of `NoZeroSMulDivisors`, which is mathematically
incorrect for the same reason.
-/

open Function

variable {M G : Type*}

variable (M) in
/-- A monoid is `R`-torsion-free if scalar multiplication by every non-zero element `a : R` is
injective. -/
@[mk_iff]
class IsAddTorsionFree [AddMonoid M] where
  protected nsmul_right_injective ⦃n : ℕ⦄ (hn : n ≠ 0) : Injective fun a : M ↦ n • a

section Monoid
variable [Monoid M]

variable (M) in
/-- A monoid is `R`-torsion-free if power by every non-zero element `a : R` is injective. -/
@[to_additive, mk_iff]
class IsMulTorsionFree where
  protected pow_left_injective ⦃n : ℕ⦄ (hn : n ≠ 0) : Injective fun a : M ↦ a ^ n

attribute [to_additive existing] isMulTorsionFree_iff

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

@[to_additive nsmul_right_injective]
lemma pow_left_injective (hn : n ≠ 0) : Injective fun a : M ↦ a ^ n :=
  IsMulTorsionFree.pow_left_injective hn

@[to_additive nsmul_right_inj]
lemma pow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (pow_left_injective hn).eq_iff

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
@[to_additive "Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`."]
lemma zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn

end Group
