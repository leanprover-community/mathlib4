/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Monotone.Basic

section Monoid

variable {M : Type*} [Monoid M] [NoRootsOfUnity M ℕ] {x : M} {n : ℕ}

/-- In a monoid without roots of unity, `x ^ n = 1` iff `x = 1` or `n = 0`.

Earlier, this name was used for what's now called `pow_eq_one_iff_left`.
The additive version is not a `simp` lemma, because it's a special case of `smul_eq_zero`. -/
@[to_additive, simp]
theorem pow_eq_one_iff : x ^ n = 1 ↔ x = 1 ∨ n = 0 := by
  refine ⟨fun h ↦ (NoRootsOfUnity.eq_zero_or_eq_one_of_pow_eq_one h).symm, ?_⟩
  rintro (rfl | rfl) <;> simp

@[to_additive nsmul_eq_zero_iff_right]
theorem pow_eq_one_iff_left (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by simp [hn]

end Monoid

section LeftCancelMonoid

variable {M : Type*} [LeftCancelMonoid M] [NoRootsOfUnity M ℕ] {x : M} {m n : ℕ}

/-- Earlier, this name was used for what's now called `pow_right_injective₀`. -/
@[to_additive nsmul_left_injective]
theorem pow_right_injective (h : x ≠ 1) : Function.Injective fun n : ℕ ↦ x ^ n := by
  refine injective_of_lt_imp_ne fun k l hlt heq ↦ ?_
  rcases Nat.exists_eq_add_of_lt hlt with ⟨m, rfl⟩
  rw [Nat.add_assoc, pow_add, self_eq_mul_right, pow_eq_one_iff] at heq
  exact heq.elim h (by simp)

@[to_additive (attr := simp) nsmul_left_inj]
theorem pow_right_inj (h : x ≠ 1) : x ^ m = x ^ n ↔ m = n := (pow_right_injective h).eq_iff

end LeftCancelMonoid

section DivisionMonoid

variable {G : Type*} [DivisionMonoid G] [NoRootsOfUnity G ℕ] {x : G} {n : ℤ}

/-- In a division monoid without roots of unity, `x ^ n = 1` iff `x = 1` or `n = 0`.

The additive version is not a `simp` lemma, because it's a special case of `smul_eq_zero`. -/
@[to_additive, simp]
theorem zpow_eq_one_iff : x ^ n = 1 ↔ x = 1 ∨ n = 0 := by cases n <;> simp

@[to_additive zsmul_eq_one_iff_right]
theorem zpow_eq_one_iff_left (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by simp [hn]

end DivisionMonoid

section Group

variable {G : Type*} [Group G] [NoRootsOfUnity G ℕ] {x y : G} {m n : ℤ}

@[to_additive zsmul_left_injective]
theorem zpow_right_injective (hx : x ≠ 1) : Function.Injective fun n : ℤ ↦ x ^ n := by
  refine injective_of_lt_imp_ne fun k l hlt heq ↦ ?_
  rcases Int.lt.dest hlt with ⟨m, rfl⟩
  rw [zpow_add, self_eq_mul_right, zpow_natCast] at heq
  exact (NoRootsOfUnity.eq_zero_or_eq_one_of_pow_eq_one heq).elim (by simp) hx

@[to_additive (attr := simp) zsmul_left_inj]
theorem zpow_right_inj (hx : x ≠ 1) : x ^ m = x ^ n ↔ m = n := (zpow_right_injective hx).eq_iff

@[to_additive]
instance (priority := 500) NoRootsOfUnity.int_of_nat : NoRootsOfUnity G ℤ where
  eq_zero_or_eq_one_of_pow_eq_one := by rintro (n | n) x h <;> simpa [or_comm] using h

end Group

@[to_additive]
instance (priority := 500) NoRootsOfUnity.nat_of_int {G : Type*} [Group G] [NoRootsOfUnity G ℤ] :
    NoRootsOfUnity G ℕ where
  eq_zero_or_eq_one_of_pow_eq_one {c x} :=
    mod_cast eq_zero_or_eq_one_of_pow_eq_one (c := (c : ℤ)) (x := x)

section CommGroup

variable {G : Type*} [CommGroup G] [NoRootsOfUnity G ℕ] {x y : G} {n : ℤ}

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
