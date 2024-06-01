/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.GroupTheory.MonoidLocalization
import Mathlib.RingTheory.Algebraic
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

#align_import ring_theory.localization.integral from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Integral and algebraic elements of a fraction field

## Implementation notes

See `RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]

open Polynomial

namespace IsLocalization

section IntegerNormalization

open Polynomial

variable [IsLocalization M S]

open scoped Classical

/-- `coeffIntegerNormalization p` gives the coefficients of the polynomial
`integerNormalization p` -/
noncomputable def coeffIntegerNormalization (p : S[X]) (i : ℕ) : R :=
  if hi : i ∈ p.support then
    Classical.choose
      (Classical.choose_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff))
        (p.coeff i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  else 0
#align is_localization.coeff_integer_normalization IsLocalization.coeffIntegerNormalization

theorem coeffIntegerNormalization_of_not_mem_support (p : S[X]) (i : ℕ) (h : coeff p i = 0) :
    coeffIntegerNormalization M p i = 0 := by
  simp only [coeffIntegerNormalization, h, mem_support_iff, eq_self_iff_true, not_true, Ne,
    dif_neg, not_false_iff]
#align is_localization.coeff_integer_normalization_of_not_mem_support IsLocalization.coeffIntegerNormalization_of_not_mem_support

theorem coeffIntegerNormalization_mem_support (p : S[X]) (i : ℕ)
    (h : coeffIntegerNormalization M p i ≠ 0) : i ∈ p.support := by
  contrapose h
  rw [Ne, Classical.not_not, coeffIntegerNormalization, dif_neg h]
#align is_localization.coeff_integer_normalization_mem_support IsLocalization.coeffIntegerNormalization_mem_support

/-- `integerNormalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
noncomputable def integerNormalization (p : S[X]) : R[X] :=
  ∑ i ∈ p.support, monomial i (coeffIntegerNormalization M p i)
#align is_localization.integer_normalization IsLocalization.integerNormalization

@[simp]
theorem integerNormalization_coeff (p : S[X]) (i : ℕ) :
    (integerNormalization M p).coeff i = coeffIntegerNormalization M p i := by
  simp (config := { contextual := true }) [integerNormalization, coeff_monomial,
    coeffIntegerNormalization_of_not_mem_support]
#align is_localization.integer_normalization_coeff IsLocalization.integerNormalization_coeff

theorem integerNormalization_spec (p : S[X]) :
    ∃ b : M, ∀ i, algebraMap R S ((integerNormalization M p).coeff i) = (b : R) • p.coeff i := by
  use Classical.choose (exist_integer_multiples_of_finset M (p.support.image p.coeff))
  intro i
  rw [integerNormalization_coeff, coeffIntegerNormalization]
  split_ifs with hi
  · exact
      Classical.choose_spec
        (Classical.choose_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff))
          (p.coeff i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  · rw [RingHom.map_zero, not_mem_support_iff.mp hi, smul_zero]
    -- Porting note: was `convert (smul_zero _).symm, ...`
#align is_localization.integer_normalization_spec IsLocalization.integerNormalization_spec

theorem integerNormalization_map_to_map (p : S[X]) :
    ∃ b : M, (integerNormalization M p).map (algebraMap R S) = (b : R) • p :=
  let ⟨b, hb⟩ := integerNormalization_spec M p
  ⟨b,
    Polynomial.ext fun i => by
      rw [coeff_map, coeff_smul]
      exact hb i⟩
#align is_localization.integer_normalization_map_to_map IsLocalization.integerNormalization_map_to_map

variable {R' : Type*} [CommRing R']

theorem integerNormalization_eval₂_eq_zero (g : S →+* R') (p : S[X]) {x : R'}
    (hx : eval₂ g x p = 0) : eval₂ (g.comp (algebraMap R S)) x (integerNormalization M p) = 0 :=
  let ⟨b, hb⟩ := integerNormalization_map_to_map M p
  _root_.trans (eval₂_map (algebraMap R S) g x).symm
    (by rw [hb, ← IsScalarTower.algebraMap_smul S (b : R) p, eval₂_smul, hx, mul_zero])
#align is_localization.integer_normalization_eval₂_eq_zero IsLocalization.integerNormalization_eval₂_eq_zero

theorem integerNormalization_aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalarTower R S R']
    (p : S[X]) {x : R'} (hx : aeval x p = 0) : aeval x (integerNormalization M p) = 0 := by
  rw [aeval_def, IsScalarTower.algebraMap_eq R S R',
    integerNormalization_eval₂_eq_zero _ (algebraMap _ _) _ hx]
#align is_localization.integer_normalization_aeval_eq_zero IsLocalization.integerNormalization_aeval_eq_zero

end IntegerNormalization

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {A K C : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
variable [CommRing C]

theorem integerNormalization_eq_zero_iff {p : K[X]} :
    integerNormalization (nonZeroDivisors A) p = 0 ↔ p = 0 := by
  refine Polynomial.ext_iff.trans (Polynomial.ext_iff.trans ?_).symm
  obtain ⟨⟨b, nonzero⟩, hb⟩ := integerNormalization_spec (nonZeroDivisors A) p
  constructor <;> intro h i
  · -- Porting note: avoided some defeq abuse
    rw [coeff_zero, ← to_map_eq_zero_iff (K := K), hb i, h i, coeff_zero, smul_zero]
  · have hi := h i
    rw [Polynomial.coeff_zero, ← @to_map_eq_zero_iff A _ K, hb i, Algebra.smul_def] at hi
    apply Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi)
    intro h
    apply mem_nonZeroDivisors_iff_ne_zero.mp nonzero
    exact to_map_eq_zero_iff.mp h
#align is_fraction_ring.integer_normalization_eq_zero_iff IsFractionRing.integerNormalization_eq_zero_iff

variable (A K C)

/-- An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
theorem isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} :
    IsAlgebraic A x ↔ IsAlgebraic K x := by
  constructor <;> rintro ⟨p, hp, px⟩
  · refine ⟨p.map (algebraMap A K), fun h => hp (Polynomial.ext fun i => ?_), ?_⟩
    · have : algebraMap A K (p.coeff i) = 0 :=
        _root_.trans (Polynomial.coeff_map _ _).symm (by simp [h])
      exact to_map_eq_zero_iff.mp this
    · exact (Polynomial.aeval_map_algebraMap K _ _).trans px
  · exact
      ⟨integerNormalization _ p, mt integerNormalization_eq_zero_iff.mp hp,
        integerNormalization_aeval_eq_zero _ p px⟩
#align is_fraction_ring.is_algebraic_iff IsFractionRing.isAlgebraic_iff

variable {A K C}

/-- A ring is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`.
-/
theorem comap_isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] :
    Algebra.IsAlgebraic A C ↔ Algebra.IsAlgebraic K C :=
  ⟨fun h => ⟨fun x => (isAlgebraic_iff A K C).mp (h.isAlgebraic x)⟩,
   fun h => ⟨fun x => (isAlgebraic_iff A K C).mpr (h.isAlgebraic x)⟩⟩
#align is_fraction_ring.comap_is_algebraic_iff IsFractionRing.comap_isAlgebraic_iff

end IsFractionRing

open IsLocalization

section IsIntegral

variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]
variable [Algebra R Rₘ] [IsLocalization M Rₘ]
variable [Algebra S Sₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable {M}

open Polynomial

theorem RingHom.isIntegralElem_localization_at_leadingCoeff {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S) (p : R[X]) (hf : p.eval₂ f x = 0) (M : Submonoid R)
    (hM : p.leadingCoeff ∈ M) {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ]
    [IsLocalization M Rₘ] [Algebra S Sₘ] [IsLocalization (M.map f : Submonoid S) Sₘ] :
    (map Sₘ f M.le_comap_map : Rₘ →+* _).IsIntegralElem (algebraMap S Sₘ x) := by
  by_cases triv : (1 : Rₘ) = 0
  · exact ⟨0, ⟨_root_.trans leadingCoeff_zero triv.symm, eval₂_zero _ _⟩⟩
  haveI : Nontrivial Rₘ := nontrivial_of_ne 1 0 triv
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (map_units Rₘ ⟨p.leadingCoeff, hM⟩)
  refine ⟨p.map (algebraMap R Rₘ) * C b, ⟨?_, ?_⟩⟩
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rwa [leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap R Rₘ)]
    refine fun hfp => zero_ne_one
      (_root_.trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1)
  · refine eval₂_mul_eq_zero_of_left _ _ _ ?_
    erw [eval₂_map, IsLocalization.map_comp, ← hom_eval₂ _ f (algebraMap S Sₘ) x]
    exact _root_.trans (congr_arg (algebraMap S Sₘ) hf) (RingHom.map_zero _)
#align ring_hom.is_integral_elem_localization_at_leading_coeff RingHom.isIntegralElem_localization_at_leadingCoeff

/-- Given a particular witness to an element being algebraic over an algebra `R → S`,
We can localize to a submonoid containing the leading coefficient to make it integral.
Explicitly, the map between the localizations will be an integral ring morphism -/
theorem is_integral_localization_at_leadingCoeff {x : S} (p : R[X]) (hp : aeval x p = 0)
    (hM : p.leadingCoeff ∈ M) :
    (map Sₘ (algebraMap R S)
            (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
          Rₘ →+* _).IsIntegralElem
      (algebraMap S Sₘ x) :=
  -- Porting note: added `haveI`
  haveI : IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ)
  (algebraMap R S).isIntegralElem_localization_at_leadingCoeff x p hp M hM
#align is_integral_localization_at_leading_coeff is_integral_localization_at_leadingCoeff

/-- If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension -/
theorem isIntegral_localization [Algebra.IsIntegral R S] :
    (map Sₘ (algebraMap R S)
          (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
        Rₘ →+* _).IsIntegral := by
  intro x
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (Algebra.algebraMapSubmonoid S M) x
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := isUnit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)
  refine @IsIntegral.of_mul_unit Rₘ _ _ _ (localizationAlgebra M S) x (algebraMap S Sₘ u) v' ?_ ?_
  · replace hv' := congr_arg (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) hv'
    rw [RingHom.map_mul, RingHom.map_one, ← RingHom.comp_apply _ (algebraMap R Rₘ)] at hv'
    -- Porting note: added argument
    erw [IsLocalization.map_comp
      (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map)] at hv'
    exact hv.2 ▸ hv'
  · obtain ⟨p, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    exact hx.symm ▸ is_integral_localization_at_leadingCoeff p hp.2 (hp.1.symm ▸ M.one_mem)
#align is_integral_localization isIntegral_localization

@[nolint unusedHavesSuffices] -- It claims the `have : IsLocalization` line is unnecessary,
                              -- but remove it and the proof won't work.
theorem isIntegral_localization' {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IsIntegral) (M : Submonoid R) :
    (map (Localization (M.map (f : R →* S))) f
          (M.le_comap_map : _ ≤ Submonoid.comap (f : R →* S) _) :
        Localization M →+* _).IsIntegral :=
  -- Porting note: added
  let _ := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid S M)
    (Localization (Submonoid.map (f : R →* S) M)) := Localization.isLocalization
  isIntegral_localization
#align is_integral_localization' isIntegral_localization'

variable (M)

theorem IsLocalization.scaleRoots_commonDenom_mem_lifts (p : Rₘ[X])
    (hp : p.leadingCoeff ∈ (algebraMap R Rₘ).range) :
    p.scaleRoots (algebraMap R Rₘ <| IsLocalization.commonDenom M p.support p.coeff) ∈
      Polynomial.lifts (algebraMap R Rₘ) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_scaleRoots]
  by_cases h₁ : n ∈ p.support
  on_goal 1 => by_cases h₂ : n = p.natDegree
  · rwa [h₂, Polynomial.coeff_natDegree, tsub_self, pow_zero, _root_.mul_one]
  · have : n + 1 ≤ p.natDegree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp _ h₁) h₂
    rw [← tsub_add_cancel_of_le (le_tsub_of_add_le_left this), pow_add, pow_one, mul_comm,
      _root_.mul_assoc, ← map_pow]
    change _ ∈ (algebraMap R Rₘ).range
    apply mul_mem
    · exact RingHom.mem_range_self _ _
    · rw [← Algebra.smul_def]
      exact ⟨_, IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, h₁⟩⟩
  · rw [Polynomial.not_mem_support_iff] at h₁
    rw [h₁, zero_mul]
    exact zero_mem (algebraMap R Rₘ).range
#align is_localization.scale_roots_common_denom_mem_lifts IsLocalization.scaleRoots_commonDenom_mem_lifts

theorem IsIntegral.exists_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S]
    (x : S) (hx : IsIntegral Rₘ x) : ∃ m : M, IsIntegral R (m • x) := by
  cases' subsingleton_or_nontrivial Rₘ with _ nontriv
  · haveI := (_root_.algebraMap Rₘ S).codomain_trivial
    exact ⟨1, Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  obtain ⟨p, hp₁, hp₂⟩ := hx
  -- Porting note: obtain doesn't support side goals
  have :=
    lifts_and_natDegree_eq_and_monic (IsLocalization.scaleRoots_commonDenom_mem_lifts M p ?_) ?_
  · obtain ⟨p', hp'₁, -, hp'₂⟩ := this
    refine ⟨IsLocalization.commonDenom M p.support p.coeff, p', hp'₂, ?_⟩
    rw [IsScalarTower.algebraMap_eq R Rₘ S, ← Polynomial.eval₂_map, hp'₁, Submonoid.smul_def,
      Algebra.smul_def, IsScalarTower.algebraMap_apply R Rₘ S]
    exact Polynomial.scaleRoots_eval₂_eq_zero _ hp₂
  · rw [hp₁.leadingCoeff]
    exact one_mem _
  · rwa [Polynomial.monic_scaleRoots_iff]
#align is_integral.exists_multiple_integral_of_is_localization IsIntegral.exists_multiple_integral_of_isLocalization

end IsIntegral

variable {A K : Type*} [CommRing A] [IsDomain A]

namespace IsIntegralClosure

variable (A)
variable {L : Type*} [Field K] [Field L] [Algebra A K] [Algebra A L] [IsFractionRing A K]
variable (C : Type*) [CommRing C] [IsDomain C] [Algebra C L] [IsIntegralClosure C A L]
variable [Algebra A C] [IsScalarTower A C L]

open Algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_algebraic [Algebra.IsAlgebraic A L]
    (inj : ∀ x, algebraMap A L x = 0 → x = 0) : IsFractionRing C L :=
  { map_units' := fun ⟨y, hy⟩ =>
      IsUnit.mk0 _
        (show algebraMap C L y ≠ 0 from fun h =>
          mem_nonZeroDivisors_iff_ne_zero.mp hy
            ((injective_iff_map_eq_zero (algebraMap C L)).mp (algebraMap_injective C A L) _ h))
    surj' := fun z =>
      let ⟨x, y, hy, hxy⟩ := exists_integral_multiple (Algebra.IsAlgebraic.isAlgebraic z) inj
      ⟨⟨mk' C (x : L) x.2, algebraMap _ _ y,
          mem_nonZeroDivisors_iff_ne_zero.mpr fun h =>
            hy (inj _ (by rw [IsScalarTower.algebraMap_apply A C L, h, RingHom.map_zero]))⟩,
        by
          simp only
          rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply A C L, hxy]⟩
    exists_of_eq := fun {x y} h => ⟨1, by simpa using algebraMap_injective C A L h⟩ }
#align is_integral_closure.is_fraction_ring_of_algebraic IsIntegralClosure.isFractionRing_of_algebraic

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_finite_extension [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] : IsFractionRing C L :=
  have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstanceAs (Algebra.IsAlgebraic K L))
  isFractionRing_of_algebraic A C
    fun _ hx =>
    IsFractionRing.to_map_eq_zero_iff.mp
      ((_root_.map_eq_zero <|
          algebraMap K L).mp <| (IsScalarTower.algebraMap_apply _ _ _ _).symm.trans hx)
#align is_integral_closure.is_fraction_ring_of_finite_extension IsIntegralClosure.isFractionRing_of_finite_extension

end IsIntegralClosure

namespace integralClosure

variable {L : Type*} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]

open Algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_algebraic [Algebra A L] [Algebra.IsAlgebraic A L]
    (inj : ∀ x, algebraMap A L x = 0 → x = 0) : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L) inj
#align integral_closure.is_fraction_ring_of_algebraic integralClosure.isFractionRing_of_algebraic

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_finite_extension [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
#align integral_closure.is_fraction_ring_of_finite_extension integralClosure.isFractionRing_of_finite_extension

end integralClosure

namespace IsFractionRing

variable (R S K)

/-- `S` is algebraic over `R` iff a fraction ring of `S` is algebraic over `R` -/
theorem isAlgebraic_iff' [Field K] [IsDomain R] [IsDomain S] [Algebra R K] [Algebra S K]
    [NoZeroSMulDivisors R K] [IsFractionRing S K] [IsScalarTower R S K] :
    Algebra.IsAlgebraic R S ↔ Algebra.IsAlgebraic R K := by
  simp only [Algebra.isAlgebraic_def]
  constructor
  · intro h x
    letI := FractionRing.liftAlgebra R K
    have := FractionRing.isScalarTower_liftAlgebra R K
    rw [IsFractionRing.isAlgebraic_iff R (FractionRing R) K, isAlgebraic_iff_isIntegral]
    obtain ⟨a : S, b, ha, rfl⟩ := @div_surjective S _ _ _ _ _ _ x
    obtain ⟨f, hf₁, hf₂⟩ := h b
    rw [div_eq_mul_inv]
    refine IsIntegral.mul ?_ ?_
    · rw [← isAlgebraic_iff_isIntegral]
      refine .tower_top_of_injective
        (NoZeroSMulDivisors.algebraMap_injective R (FractionRing R)) ?_
      exact .algebraMap (h a)
    · rw [← isAlgebraic_iff_isIntegral]
      use (f.map (algebraMap R (FractionRing R))).reverse
      constructor
      · rwa [Ne, Polynomial.reverse_eq_zero, ← Polynomial.degree_eq_bot,
          Polynomial.degree_map_eq_of_injective
            (NoZeroSMulDivisors.algebraMap_injective R (FractionRing R)),
          Polynomial.degree_eq_bot]
      · have : Invertible (algebraMap S K b) :=
          IsUnit.invertible
            (isUnit_of_mem_nonZeroDivisors
              (mem_nonZeroDivisors_iff_ne_zero.2 fun h =>
                nonZeroDivisors.ne_zero ha
                  ((injective_iff_map_eq_zero (algebraMap S K)).1
                    (NoZeroSMulDivisors.algebraMap_injective _ _) b h)))
        rw [Polynomial.aeval_def, ← invOf_eq_inv, Polynomial.eval₂_reverse_eq_zero_iff,
          Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq, ← Polynomial.aeval_def,
          Polynomial.aeval_algebraMap_apply, hf₂, RingHom.map_zero]
  · intro h x
    obtain ⟨f, hf₁, hf₂⟩ := h (algebraMap S K x)
    use f, hf₁
    rw [Polynomial.aeval_algebraMap_apply] at hf₂
    exact
      (injective_iff_map_eq_zero (algebraMap S K)).1 (NoZeroSMulDivisors.algebraMap_injective _ _) _
        hf₂
#align is_fraction_ring.is_algebraic_iff' IsFractionRing.isAlgebraic_iff'

open nonZeroDivisors

variable {S K}

/-- If the `S`-multiples of `a` are contained in some `R`-span, then `Frac(S)`-multiples of `a`
are contained in the equivalent `Frac(R)`-span. -/
theorem ideal_span_singleton_map_subset {L : Type*} [IsDomain R] [IsDomain S] [Field K] [Field L]
    [Algebra R K] [Algebra R L] [Algebra S L] [IsIntegralClosure S R L] [IsFractionRing S L]
    [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L] {a : S} {b : Set S}
    [Algebra.IsAlgebraic R L] (inj : Function.Injective (algebraMap R L))
    (h : (Ideal.span ({a} : Set S) : Set S) ⊆ Submodule.span R b) :
    (Ideal.span ({algebraMap S L a} : Set L) : Set L) ⊆ Submodule.span K (algebraMap S L '' b) := by
  intro x hx
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨y', z', rfl⟩ := IsLocalization.mk'_surjective S⁰ x'
  obtain ⟨y, z, hz0, yz_eq⟩ :=
    IsIntegralClosure.exists_smul_eq_mul inj y' (nonZeroDivisors.coe_ne_zero z')
  have injRS : Function.Injective (algebraMap R S) := by
    refine
      Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ algebraMap R S) from ?_)
    rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  have hz0' : algebraMap R S z ∈ S⁰ :=
    map_mem_nonZeroDivisors (algebraMap R S) injRS (mem_nonZeroDivisors_of_ne_zero hz0)
  have mk_yz_eq : IsLocalization.mk' L y' z' = IsLocalization.mk' L y ⟨_, hz0'⟩ := by
    rw [Algebra.smul_def, mul_comm _ y, mul_comm _ y'] at yz_eq
    exact IsLocalization.mk'_eq_of_eq (by rw [mul_comm _ y, mul_comm _ y', yz_eq])
  suffices hy : algebraMap S L (a * y) ∈ Submodule.span K ((algebraMap S L) '' b) by
    rw [mk_yz_eq, IsFractionRing.mk'_eq_div, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, div_eq_mul_inv, ← mul_assoc, mul_comm, ← map_inv₀, ←
      Algebra.smul_def, ← _root_.map_mul]
    exact (Submodule.span K _).smul_mem _ hy
  refine Submodule.span_subset_span R K _ ?_
  rw [Submodule.span_algebraMap_image_of_tower]
  -- Note: #8386 had to specify the value of `f` here:
  exact Submodule.mem_map_of_mem (f := LinearMap.restrictScalars _ _)
    (h (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩))
#align is_fraction_ring.ideal_span_singleton_map_subset IsFractionRing.ideal_span_singleton_map_subset

end IsFractionRing

lemma isAlgebraic_of_isLocalization {R} [CommRing R] (M : Submonoid R) (S) [CommRing S]
    [Nontrivial R] [Algebra R S] [IsLocalization M S] : Algebra.IsAlgebraic R S := by
  constructor
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective M x
  by_cases hs : (s : R) = 0
  · have := IsLocalization.mk'_spec S x s
    rw [hs, map_zero, mul_zero] at this
    exact ⟨X, X_ne_zero, by simp [IsLocalization.mk'_eq_mul_mk'_one x, ← this]⟩
  refine ⟨s • X - C x, ?_, ?_⟩
  · intro e; apply hs
    simpa only [coeff_sub, coeff_smul, coeff_X_one, coeff_C_succ, sub_zero, coeff_zero,
      ← Algebra.algebraMap_eq_smul_one, Submonoid.smul_def,
      Algebra.id.map_eq_id, RingHom.id_apply] using congr_arg (Polynomial.coeff · 1) e
  · simp only [map_sub, Algebra.smul_def, Submonoid.smul_def,
      map_mul, AlgHom.commutes, aeval_X, IsLocalization.mk'_spec', aeval_C, sub_self]

open nonZeroDivisors in
lemma isAlgebraic_of_isFractionRing {R S} (K L) [CommRing R] [CommRing S] [Field K] [CommRing L]
    [Algebra R S] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R S L]
    [IsScalarTower R K L] [IsFractionRing S L]
    [Algebra.IsIntegral R S] : Algebra.IsAlgebraic K L := by
  constructor
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective S⁰ x
  apply IsIntegral.isAlgebraic
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  apply RingHom.IsIntegralElem.mul
  · apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral x
  · show IsIntegral _ _
    rw [← isAlgebraic_iff_isIntegral, ← IsAlgebraic.invOf_iff, isAlgebraic_iff_isIntegral]
    apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral (s : S)
