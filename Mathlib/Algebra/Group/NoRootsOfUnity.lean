/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Monotone.Basic

section Monoid

variable {M : Type*} [Monoid M] [NoRootsOfUnity M ℕ] {x : M} {n : ℕ}

/-- In a monoid without roots of unity, `x ^ n = 1` iff `x = 1` or `n = 0`. -/
@[to_additive, simp]
theorem pow_eq_one : x ^ n = 1 ↔ x = 1 ∨ n = 0 := by
  refine ⟨fun h ↦ (NoRootsOfUnity.eq_zero_or_eq_one_of_pow_eq_one h).symm, ?_⟩
  rintro (rfl | rfl) <;> simp

end Monoid

section LeftCancelMonoid

variable {M : Type*} [LeftCancelMonoid M] [NoRootsOfUnity M ℕ] {x : M} {m n : ℕ}

@[to_additive nsmul_left_injective]
theorem pow_right_injective (h : x ≠ 1) : Function.Injective fun n : ℕ ↦ x ^ n := by
  refine injective_of_lt_imp_ne fun k l hlt heq ↦ ?_
  rcases Nat.exists_eq_add_of_lt hlt with ⟨m, rfl⟩
  rw [Nat.add_assoc, pow_add, self_eq_mul_right, pow_eq_one] at heq
  exact heq.elim h (by simp)

@[to_additive (attr := simp) nsmul_left_inj]
theorem pow_right_inj (h : x ≠ 1) : x ^ m = x ^ n ↔ m = n := (pow_right_injective h).eq_iff

end LeftCancelMonoid

variable {G : Type*} [Group G] [NoRootsOfUnity G ℕ] {x : G} {m n : ℤ}

@[to_additive zsmul_left_injective]
theorem zpow_right_injective (hx : x ≠ 1) : Function.Injective fun n : ℤ ↦ x ^ n := by
  refine injective_of_lt_imp_ne fun k l hlt heq ↦ ?_
  rcases Int.lt.dest hlt with ⟨m, rfl⟩
  rw [zpow_add, self_eq_mul_right, zpow_natCast] at heq
  exact (NoRootsOfUnity.eq_zero_or_eq_one_of_pow_eq_one heq).elim (by simp) hx

@[to_additive (attr := simp) zsmul_left_inj]
theorem zpow_right_inj (hx : x ≠ 1) : x ^ m = x ^ n ↔ m = n := (zpow_right_injective hx).eq_iff
