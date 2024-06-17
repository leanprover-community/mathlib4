/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.UniqueFactorizationDomain

#align_import ring_theory.localization.num_denom from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Numerator and denominator in a localization

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]

namespace IsFractionRing

open IsLocalization

section NumDen

variable (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

theorem exists_reduced_fraction (x : K) :
    ∃ (a : A) (b : nonZeroDivisors A), IsRelPrime a b ∧ mk' K a b = x := by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_nonZeroDivisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨_, b'_nonzero⟩ := mul_mem_nonZeroDivisors.mp b_nonzero
  refine ⟨a', ⟨b', b'_nonzero⟩, no_factor, ?_⟩
  refine mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b_nonzero) ?_
  simp only [Subtype.coe_mk, RingHom.map_mul, Algebra.smul_def] at *
  erw [← hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩]
#align is_fraction_ring.exists_reduced_fraction IsFractionRing.exists_reduced_fraction

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def num (x : K) : A :=
  Classical.choose (exists_reduced_fraction A x)
#align is_fraction_ring.num IsFractionRing.num

/-- `f.den x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def den (x : K) : nonZeroDivisors A :=
  Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))
#align is_fraction_ring.denom IsFractionRing.den

theorem num_den_reduced (x : K) : IsRelPrime (num A x) (den A x) :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1
#align is_fraction_ring.num_denom_reduced IsFractionRing.num_den_reduced

-- @[simp] -- Porting note: LHS reduces to give the simp lemma below
theorem mk'_num_den (x : K) : mk' K (num A x) (den A x) = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2
#align is_fraction_ring.mk'_num_denom IsFractionRing.mk'_num_den

@[simp]
theorem mk'_num_den' (x : K) : algebraMap A K (num A x) / algebraMap A K (den A x) = x := by
  rw [← mk'_eq_div]
  apply mk'_num_den

variable {A}

theorem num_mul_den_eq_num_iff_eq {x y : K} :
    x * algebraMap A K (den A y) = algebraMap A K (num A y) ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h ↦
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩
#align is_fraction_ring.num_mul_denom_eq_num_iff_eq IsFractionRing.num_mul_den_eq_num_iff_eq

theorem num_mul_den_eq_num_iff_eq' {x y : K} :
    y * algebraMap A K (den A x) = algebraMap A K (num A x) ↔ x = y :=
  ⟨fun h ↦ by simpa only [eq_comm, mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h ↦
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩
#align is_fraction_ring.num_mul_denom_eq_num_iff_eq' IsFractionRing.num_mul_den_eq_num_iff_eq'

theorem num_mul_den_eq_num_mul_den_iff_eq {x y : K} :
    num A y * den A x = num A x * den A y ↔ x = y :=
  ⟨fun h ↦ by simpa only [mk'_num_den] using mk'_eq_of_eq' (S := K) h, fun h ↦ by rw [h]⟩
#align is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq IsFractionRing.num_mul_den_eq_num_mul_den_iff_eq

theorem eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
  num_mul_den_eq_num_iff_eq'.mp (by rw [zero_mul, h, RingHom.map_zero])
#align is_fraction_ring.eq_zero_of_num_eq_zero IsFractionRing.eq_zero_of_num_eq_zero

theorem isInteger_of_isUnit_den {x : K} (h : IsUnit (den A x : A)) : IsInteger A x := by
  cases' h with d hd
  have d_ne_zero : algebraMap A K (den A x) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A x).2
  use ↑d⁻¹ * num A x
  refine _root_.trans ?_ (mk'_num_den A x)
  rw [map_mul, map_units_inv, hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul_assoc, mul_inv_cancel d_ne_zero, one_mul, mk'_spec']
#align is_fraction_ring.is_integer_of_is_unit_denom IsFractionRing.isInteger_of_isUnit_den

theorem isUnit_den_of_num_eq_zero {x : K} (h : num A x = 0) : IsUnit (den A x : A) :=
  num_den_reduced A x (h.symm ▸ dvd_zero _) dvd_rfl
#align is_fraction_ring.is_unit_denom_of_num_eq_zero IsFractionRing.isUnit_den_of_num_eq_zero

end NumDen

variable (S)

end IsFractionRing
