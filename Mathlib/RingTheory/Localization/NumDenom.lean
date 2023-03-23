/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.num_denom
! leanprover-community/mathlib commit 831c494092374cfe9f50591ed0ac81a25efc5b86
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer
import Mathbin.RingTheory.UniqueFactorizationDomain

/-!
# Numerator and denominator in a localization

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRing R] (M : Submonoid R) {S : Type _} [CommRing S]

variable [Algebra R S] {P : Type _} [CommRing P]

namespace IsFractionRing

open IsLocalization

section NumDenom

variable (A : Type _) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

variable {K : Type _} [Field K] [Algebra A K] [IsFractionRing A K]

theorem exists_reduced_fraction (x : K) :
    ∃ (a : A)(b : nonZeroDivisors A), (∀ {d}, d ∣ a → d ∣ b → IsUnit d) ∧ mk' K a b = x :=
  by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero
  refine' ⟨a', ⟨b', b'_nonzero⟩, @no_factor, _⟩
  refine' mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b_nonzero) _
  simp only [Subtype.coe_mk, RingHom.map_mul, Algebra.smul_def] at *
  erw [← hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩]
#align is_fraction_ring.exists_reduced_fraction IsFractionRing.exists_reduced_fraction

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def num (x : K) : A :=
  Classical.choose (exists_reduced_fraction A x)
#align is_fraction_ring.num IsFractionRing.num

/-- `f.num x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def denom (x : K) : nonZeroDivisors A :=
  Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))
#align is_fraction_ring.denom IsFractionRing.denom

theorem num_denom_reduced (x : K) {d} : d ∣ num A x → d ∣ denom A x → IsUnit d :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1
#align is_fraction_ring.num_denom_reduced IsFractionRing.num_denom_reduced

@[simp]
theorem mk'_num_denom (x : K) : mk' K (num A x) (denom A x) = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2
#align is_fraction_ring.mk'_num_denom IsFractionRing.mk'_num_denom

variable {A}

theorem num_mul_denom_eq_num_iff_eq {x y : K} :
    x * algebraMap A K (denom A y) = algebraMap A K (num A y) ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom])⟩
#align is_fraction_ring.num_mul_denom_eq_num_iff_eq IsFractionRing.num_mul_denom_eq_num_iff_eq

theorem num_mul_denom_eq_num_iff_eq' {x y : K} :
    y * algebraMap A K (denom A x) = algebraMap A K (num A x) ↔ x = y :=
  ⟨fun h => by simpa only [eq_comm, mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom])⟩
#align is_fraction_ring.num_mul_denom_eq_num_iff_eq' IsFractionRing.num_mul_denom_eq_num_iff_eq'

theorem num_mul_denom_eq_num_mul_denom_iff_eq {x y : K} :
    num A y * denom A x = num A x * denom A y ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_denom] using mk'_eq_of_eq' h, fun h => by rw [h]⟩
#align is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq IsFractionRing.num_mul_denom_eq_num_mul_denom_iff_eq

theorem eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
  num_mul_denom_eq_num_iff_eq'.mp (by rw [MulZeroClass.zero_mul, h, RingHom.map_zero])
#align is_fraction_ring.eq_zero_of_num_eq_zero IsFractionRing.eq_zero_of_num_eq_zero

theorem isInteger_of_isUnit_denom {x : K} (h : IsUnit (denom A x : A)) : IsInteger A x :=
  by
  cases' h with d hd
  have d_ne_zero : algebraMap A K (denom A x) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (denom A x).2
  use ↑d⁻¹ * Num A x
  refine' trans _ (mk'_num_denom A x)
  rw [map_mul, map_units_inv, hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul_assoc, mul_inv_cancel d_ne_zero, one_mul, mk'_spec']
#align is_fraction_ring.is_integer_of_is_unit_denom IsFractionRing.isInteger_of_isUnit_denom

theorem isUnit_denom_of_num_eq_zero {x : K} (h : num A x = 0) : IsUnit (denom A x : A) :=
  num_denom_reduced A x (h.symm ▸ dvd_zero _) dvd_rfl
#align is_fraction_ring.is_unit_denom_of_num_eq_zero IsFractionRing.isUnit_denom_of_num_eq_zero

end NumDenom

variable (S)

end IsFractionRing

