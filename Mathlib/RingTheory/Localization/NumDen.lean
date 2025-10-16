/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Numerator and denominator in a localization

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


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
  simp only [RingHom.map_mul, Algebra.smul_def] at *
  rw [← hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩]

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def num (x : K) : A :=
  Classical.choose (exists_reduced_fraction A x)

/-- `f.den x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def den (x : K) : nonZeroDivisors A :=
  Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))

theorem num_den_reduced (x : K) : IsRelPrime (num A x) (den A x) :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1

-- `@[simp]` normal form is called `mk'_num_den'`.
theorem mk'_num_den (x : K) : mk' K (num A x) (den A x) = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2

@[simp]
theorem mk'_num_den' (x : K) : algebraMap A K (num A x) / algebraMap A K (den A x) = x := by
  rw [← mk'_eq_div]
  apply mk'_num_den

variable {A}

theorem num_mul_den_eq_num_iff_eq {x y : K} :
    x * algebraMap A K (den A y) = algebraMap A K (num A y) ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h ↦
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩

theorem num_mul_den_eq_num_iff_eq' {x y : K} :
    y * algebraMap A K (den A x) = algebraMap A K (num A x) ↔ x = y :=
  ⟨fun h ↦ by simpa only [eq_comm, mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h ↦
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩

theorem num_mul_den_eq_num_mul_den_iff_eq {x y : K} :
    num A y * den A x = num A x * den A y ↔ x = y :=
  ⟨fun h ↦ by simpa only [mk'_num_den] using mk'_eq_of_eq' (S := K) h, fun h ↦ by rw [h]⟩

theorem eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
  (num_mul_den_eq_num_iff_eq' (A := A)).mp (by rw [zero_mul, h, RingHom.map_zero])

@[simp]
lemma num_zero : IsFractionRing.num A (0 : K) = 0 := by
  have := mk'_num_den' A (0 : K)
  simp only [div_eq_zero_iff] at this
  rcases this with h | h
  · exact FaithfulSMul.algebraMap_injective A K (by convert h; simp)
  · replace h : algebraMap A K (den A (0 : K)) = algebraMap A K 0 := by convert h; simp
    absurd FaithfulSMul.algebraMap_injective A K h
    apply nonZeroDivisors.coe_ne_zero

@[simp]
lemma num_eq_zero (x : K) : IsFractionRing.num A x = 0 ↔ x = 0 :=
  ⟨eq_zero_of_num_eq_zero, fun h ↦ h ▸ num_zero⟩

theorem isInteger_of_isUnit_den {x : K} (h : IsUnit (den A x : A)) : IsInteger A x := by
  obtain ⟨d, hd⟩ := h
  have d_ne_zero : algebraMap A K (den A x) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A x).2
  use ↑d⁻¹ * num A x
  refine _root_.trans ?_ (mk'_num_den A x)
  rw [map_mul, map_units_inv, hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul_assoc, mul_inv_cancel₀ d_ne_zero, one_mul, mk'_spec']

theorem isUnit_den_iff (x : K) : IsUnit (den A x : A) ↔ IsLocalization.IsInteger A x where
  mp := isInteger_of_isUnit_den
  mpr h := by
    have ⟨v, h⟩ := h
    apply IsRelPrime.isUnit_of_dvd (num_den_reduced A x).symm
    use v
    apply_fun algebraMap A K
    · simp only [map_mul, h]
      rw [mul_comm, ← div_eq_iff]
      · simp only [mk'_num_den']
      intro h
      replace h : algebraMap A K (den A x : A) = algebraMap A K 0 := by convert h; simp
      exact nonZeroDivisors.coe_ne_zero _ <| FaithfulSMul.algebraMap_injective A K h
    exact FaithfulSMul.algebraMap_injective A K

theorem isUnit_den_zero : IsUnit (den A (0 : K) : A) := by
  simp [isUnit_den_iff, IsLocalization.isInteger_zero]

lemma associated_den_num_inv (x : K) (hx : x ≠ 0) : Associated (den A x : A) (num A x⁻¹) :=
  associated_of_dvd_dvd
    (IsRelPrime.dvd_of_dvd_mul_right (IsFractionRing.num_den_reduced A x).symm <|
      dvd_of_mul_left_dvd (a := (den A x⁻¹ : A)) <| dvd_of_eq <|
      FaithfulSMul.algebraMap_injective A K <| Eq.symm <| eq_of_div_eq_one
      (by simp [mul_div_mul_comm, hx]))
    (IsRelPrime.dvd_of_dvd_mul_right (IsFractionRing.num_den_reduced A x⁻¹) <|
      dvd_of_mul_left_dvd (a := (num A x : A)) <| dvd_of_eq <|
      FaithfulSMul.algebraMap_injective A K <| eq_of_div_eq_one
      (by simp [mul_div_mul_comm, hx]))

lemma associated_num_den_inv (x : K) (hx : x ≠ 0) : Associated (num A x : A) (den A x⁻¹) := by
  have : Associated (num A x⁻¹⁻¹ : A) (den A x⁻¹) :=
    (associated_den_num_inv x⁻¹ (inv_ne_zero hx)).symm
  rw [inv_inv] at this
  exact this

end NumDen

end IsFractionRing
