/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.IsTorsionFree.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Basic properties of torsion free monoids

In this file we prove that in a torsion free left cancellative monoid,
`x^n` is injective in `n : ℕ`.

We also prove that in a torsion free group,
`x^n` is injective in `n : ℤ` for all `x` and is injective in `x` for all `n ≠ 0`.
-/

section LeftCancelMonoid

variable {M : Type*} [LeftCancelMonoid M] [IsMulTorsionFree M] {x : M} {m n : ℕ}

/-- Earlier, this name was used for what's now called `pow_right_injective₀`. -/
@[to_additive nsmul_left_injective]
theorem pow_right_injective (h : x ≠ 1) : Function.Injective fun n : ℕ ↦ x ^ n := by
  refine injective_of_lt_imp_ne fun k l hlt heq ↦ ?_
  rcases Nat.exists_eq_add_of_lt hlt with ⟨m, rfl⟩
  rw [Nat.add_assoc, pow_add, self_eq_mul_right, pow_eq_one_iff] at heq
  exact heq.elim h (by simp)

/-- Earlier, this name was used for what's now called `pow_right_inj₀`. -/
@[to_additive (attr := simp) nsmul_left_inj]
theorem pow_right_inj (h : x ≠ 1) : x ^ m = x ^ n ↔ m = n := (pow_right_injective h).eq_iff

end LeftCancelMonoid

section DivisionMonoid

variable {G : Type*} [DivisionMonoid G] [IsMulTorsionFree G] {x : G} {n : ℤ}

/-- In a division monoid without roots of unity, `x ^ n = 1` iff `x = 1` or `n = 0`.
The additive version is not a `simp` lemma, because it's a special case of `smul_eq_zero`. -/
@[to_additive, simp]
theorem zpow_eq_one_iff : x ^ n = 1 ↔ x = 1 ∨ n = 0 := by cases n <;> simp

@[to_additive zsmul_eq_one_iff_right]
theorem zpow_eq_one_iff_left (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by simp [hn]

end DivisionMonoid

section Group

variable {G : Type*} [Group G] [IsMulTorsionFree G] {x y : G} {m n : ℤ}

@[to_additive zsmul_left_injective]
theorem zpow_right_injective (hx : x ≠ 1) : Function.Injective fun n : ℤ ↦ x ^ n := by
  refine injective_of_lt_imp_ne fun k l hlt heq ↦ ?_
  rcases Int.lt.dest hlt with ⟨m, rfl⟩
  rw [zpow_add, self_eq_mul_right, zpow_natCast] at heq
  simp [hx] at heq

@[to_additive (attr := simp) zsmul_left_inj]
theorem zpow_right_inj (hx : x ≠ 1) : x ^ m = x ^ n ↔ m = n := (zpow_right_injective hx).eq_iff

end Group

section CommGroup

variable {G : Type*} [CommGroup G] [IsMulTorsionFree G] {x y : G} {n : ℤ}

@[to_additive zsmul_right_injective]
theorem zpow_left_injective (hn : n ≠ 0) : Function.Injective fun x : G ↦ x ^ n := by
  intro x y h
  rwa [← div_eq_one, ← div_zpow, zpow_eq_one_iff_left hn, div_eq_one] at h

@[to_additive zsmul_right_inj]
theorem zpow_left_inj (hn : n ≠ 0) : x ^ n = y ^ n ↔ x = y := (zpow_left_injective hn).eq_iff

@[to_additive (attr := deprecated (since := "2024-09-24"))]
alias zpow_eq_zpow_iff' := zpow_left_inj

@[to_additive (attr := simp)]
theorem zpow_eq_zpow_iff_eq_or_eq_zero : x ^ n = y ^ n ↔ x = y ∨ n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, zpow_left_inj hn]

end CommGroup
