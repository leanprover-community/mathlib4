/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

#align_import algebra.char_p.char_and_card from "leanprover-community/mathlib"@"2fae5fd7f90711febdadf19c44dc60fae8834d1b"

/-!
# Characteristic and cardinality

We prove some results relating characteristic and cardinality of finite rings

## Tags
characteristic, cardinality, ring
-/


/-- A prime `p` is a unit in a commutative ring `R` of nonzero characteristic iff it does not divide
the characteristic. -/
theorem isUnit_iff_not_dvd_char_of_ringChar_ne_zero (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : ringChar R ≠ 0) : IsUnit (p : R) ↔ ¬p ∣ ringChar R := by
  have hch := CharP.cast_eq_zero R (ringChar R)
  -- ⊢ IsUnit ↑p ↔ ¬p ∣ ringChar R
  have hp : p.Prime := Fact.out
  -- ⊢ IsUnit ↑p ↔ ¬p ∣ ringChar R
  constructor
  -- ⊢ IsUnit ↑p → ¬p ∣ ringChar R
  · rintro h₁ ⟨q, hq⟩
    -- ⊢ False
    rcases IsUnit.exists_left_inv h₁ with ⟨a, ha⟩
    -- ⊢ False
    have h₃ : ¬ringChar R ∣ q := by
      rintro ⟨r, hr⟩
      rw [hr, ← mul_assoc, mul_comm p, mul_assoc] at hq
      nth_rw 1 [← mul_one (ringChar R)] at hq
      exact Nat.Prime.not_dvd_one hp ⟨r, mul_left_cancel₀ hR hq⟩
    have h₄ := mt (CharP.int_cast_eq_zero_iff R (ringChar R) q).mp
    -- ⊢ False
    apply_fun ((↑) : ℕ → R) at hq
    -- ⊢ False
    apply_fun (· * ·) a at hq
    -- ⊢ False
    rw [Nat.cast_mul, hch, mul_zero, ← mul_assoc, ha, one_mul] at hq
    -- ⊢ False
    norm_cast at h₄
    -- ⊢ False
    exact h₄ h₃ hq.symm
    -- 🎉 no goals
  · intro h
    -- ⊢ IsUnit ↑p
    rcases(hp.coprime_iff_not_dvd.mpr h).isCoprime with ⟨a, b, hab⟩
    -- ⊢ IsUnit ↑p
    apply_fun ((↑) : ℤ → R) at hab
    -- ⊢ IsUnit ↑p
    push_cast at hab
    -- ⊢ IsUnit ↑p
    rw [hch, mul_zero, add_zero, mul_comm] at hab
    -- ⊢ IsUnit ↑p
    exact isUnit_of_mul_eq_one (p : R) a hab
    -- 🎉 no goals
#align is_unit_iff_not_dvd_char_of_ring_char_ne_zero isUnit_iff_not_dvd_char_of_ringChar_ne_zero

/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
theorem isUnit_iff_not_dvd_char (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Finite R] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R :=
  isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p <| CharP.char_ne_zero_of_finite R (ringChar R)
#align is_unit_iff_not_dvd_char isUnit_iff_not_dvd_char

/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
theorem prime_dvd_char_iff_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime] :
    p ∣ ringChar R ↔ p ∣ Fintype.card R := by
  refine'
    ⟨fun h =>
      h.trans <|
        Int.coe_nat_dvd.mp <|
          (CharP.int_cast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp <| by
            exact_mod_cast CharP.cast_card_eq_zero R,
      fun h => _⟩
  by_contra h₀
  -- ⊢ False
  rcases exists_prime_addOrderOf_dvd_card p h with ⟨r, hr⟩
  -- ⊢ False
  have hr₁ := addOrderOf_nsmul_eq_zero r
  -- ⊢ False
  rw [hr, nsmul_eq_mul] at hr₁
  -- ⊢ False
  rcases IsUnit.exists_left_inv ((isUnit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩
  -- ⊢ False
  apply_fun (· * ·) u at hr₁
  -- ⊢ False
  rw [mul_zero, ← mul_assoc, hu, one_mul] at hr₁
  -- ⊢ False
  exact mt AddMonoid.addOrderOf_eq_one_iff.mpr (ne_of_eq_of_ne hr (Nat.Prime.ne_one Fact.out)) hr₁
  -- 🎉 no goals
#align prime_dvd_char_iff_dvd_card prime_dvd_char_iff_dvd_card

/-- A prime that does not divide the cardinality of a finite commutative ring `R`
is a unit in `R`. -/
theorem not_isUnit_prime_of_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) :=
  mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))
#align not_is_unit_prime_of_dvd_card not_isUnit_prime_of_dvd_card
