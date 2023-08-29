/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Data.Polynomial.Lifts
import Mathlib.GroupTheory.MonoidLocalization
import Mathlib.RingTheory.Algebraic
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.NonZeroDivisors

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

open BigOperators Polynomial

namespace IsLocalization

section IntegerNormalization

open Polynomial

variable [IsLocalization M S]

open Classical

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
  simp only [coeffIntegerNormalization, h, mem_support_iff, eq_self_iff_true, not_true, Ne.def,
    dif_neg, not_false_iff]
#align is_localization.coeff_integer_normalization_of_not_mem_support IsLocalization.coeffIntegerNormalization_of_not_mem_support

theorem coeffIntegerNormalization_mem_support (p : S[X]) (i : ℕ)
    (h : coeffIntegerNormalization M p i ≠ 0) : i ∈ p.support := by
  contrapose h
  -- ⊢ ¬coeffIntegerNormalization M p i ≠ 0
  rw [Ne.def, Classical.not_not, coeffIntegerNormalization, dif_neg h]
  -- 🎉 no goals
#align is_localization.coeff_integer_normalization_mem_support IsLocalization.coeffIntegerNormalization_mem_support

/-- `integerNormalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
noncomputable def integerNormalization (p : S[X]) : R[X] :=
  ∑ i in p.support, monomial i (coeffIntegerNormalization M p i)
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
  -- ⊢ ∀ (i : ℕ), ↑(algebraMap R S) (coeff (integerNormalization M p) i) = ↑(choose …
  intro i
  -- ⊢ ↑(algebraMap R S) (coeff (integerNormalization M p) i) = ↑(choose (_ : ∃ b,  …
  rw [integerNormalization_coeff, coeffIntegerNormalization]
  -- ⊢ ↑(algebraMap R S) (if hi : i ∈ support p then choose (_ : IsInteger R (↑(cho …
  split_ifs with hi -- Porting note: didn't remove the ifs
  -- ⊢ ↑(algebraMap R S) (if hi : i ∈ support p then choose (_ : IsInteger R (↑(cho …
  · rw [dif_pos hi]
    -- ⊢ ↑(algebraMap R S) (choose (_ : IsInteger R (↑(choose (_ : ∃ b, ∀ (a : S), a  …
    exact
      Classical.choose_spec
        (Classical.choose_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff))
          (p.coeff i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  · rw [dif_neg hi]
    -- ⊢ ↑(algebraMap R S) 0 = ↑(choose (_ : ∃ b, ∀ (a : S), a ∈ Finset.image (coeff  …
    rw [RingHom.map_zero, not_mem_support_iff.mp hi, smul_zero]
    -- 🎉 no goals
    -- Porting note: was `convert (smul_zero _).symm, ...`
#align is_localization.integer_normalization_spec IsLocalization.integerNormalization_spec

theorem integerNormalization_map_to_map (p : S[X]) :
    ∃ b : M, (integerNormalization M p).map (algebraMap R S) = (b : R) • p :=
  let ⟨b, hb⟩ := integerNormalization_spec M p
  ⟨b,
    Polynomial.ext fun i => by
      rw [coeff_map, coeff_smul]
      -- ⊢ ↑(algebraMap R S) (coeff (integerNormalization M p) i) = ↑b • coeff p i
      exact hb i⟩
      -- 🎉 no goals
#align is_localization.integer_normalization_map_to_map IsLocalization.integerNormalization_map_to_map

variable {R' : Type*} [CommRing R']

theorem integerNormalization_eval₂_eq_zero (g : S →+* R') (p : S[X]) {x : R'}
    (hx : eval₂ g x p = 0) : eval₂ (g.comp (algebraMap R S)) x (integerNormalization M p) = 0 :=
  let ⟨b, hb⟩ := integerNormalization_map_to_map M p
  _root_.trans (eval₂_map (algebraMap R S) g x).symm
    (by rw [hb, ← IsScalarTower.algebraMap_smul S (b : R) p, eval₂_smul, hx, mul_zero])
        -- 🎉 no goals
#align is_localization.integer_normalization_eval₂_eq_zero IsLocalization.integerNormalization_eval₂_eq_zero

theorem integerNormalization_aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalarTower R S R']
    (p : S[X]) {x : R'} (hx : aeval x p = 0) : aeval x (integerNormalization M p) = 0 := by
  rw [aeval_def, IsScalarTower.algebraMap_eq R S R', integerNormalization_eval₂_eq_zero _ _ _ hx]
  -- 🎉 no goals
#align is_localization.integer_normalization_aeval_eq_zero IsLocalization.integerNormalization_aeval_eq_zero

end IntegerNormalization

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {A K C : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

variable [CommRing C]

theorem integerNormalization_eq_zero_iff {p : K[X]} :
    integerNormalization (nonZeroDivisors A) p = 0 ↔ p = 0 := by
  refine' Polynomial.ext_iff.trans (Polynomial.ext_iff.trans _).symm
  -- ⊢ (∀ (n : ℕ), coeff p n = coeff 0 n) ↔ ∀ (n : ℕ), coeff (integerNormalization  …
  obtain ⟨⟨b, nonzero⟩, hb⟩ := integerNormalization_spec (nonZeroDivisors A) p
  -- ⊢ (∀ (n : ℕ), coeff p n = coeff 0 n) ↔ ∀ (n : ℕ), coeff (integerNormalization  …
  constructor <;> intro h i
  -- ⊢ (∀ (n : ℕ), coeff p n = coeff 0 n) → ∀ (n : ℕ), coeff (integerNormalization  …
                  -- ⊢ coeff (integerNormalization (nonZeroDivisors A) p) i = coeff 0 i
                  -- ⊢ coeff p i = coeff 0 i
  · -- Porting note: avoided some defeq abuse
    rw [coeff_zero, ← to_map_eq_zero_iff (K := K), hb i, h i, coeff_zero, smul_zero]
    -- 🎉 no goals
  · have hi := h i
    -- ⊢ coeff p i = coeff 0 i
    rw [Polynomial.coeff_zero, ← @to_map_eq_zero_iff A _ K, hb i, Algebra.smul_def] at hi
    -- ⊢ coeff p i = coeff 0 i
    apply Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi)
    -- ⊢ ¬↑(algebraMap A K) ↑{ val := b, property := nonzero } = 0
    intro h
    -- ⊢ False
    apply mem_nonZeroDivisors_iff_ne_zero.mp nonzero
    -- ⊢ b = 0
    exact to_map_eq_zero_iff.mp h
    -- 🎉 no goals
#align is_fraction_ring.integer_normalization_eq_zero_iff IsFractionRing.integerNormalization_eq_zero_iff

variable (A K C)

/-- An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
theorem isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} :
    IsAlgebraic A x ↔ IsAlgebraic K x := by
  constructor <;> rintro ⟨p, hp, px⟩
  -- ⊢ IsAlgebraic A x → IsAlgebraic K x
                  -- ⊢ IsAlgebraic K x
                  -- ⊢ IsAlgebraic A x
  · refine' ⟨p.map (algebraMap A K), fun h => hp (Polynomial.ext fun i => _), _⟩
    -- ⊢ coeff p i = coeff 0 i
    · have : algebraMap A K (p.coeff i) = 0 :=
        _root_.trans (Polynomial.coeff_map _ _).symm (by simp [h])
      exact to_map_eq_zero_iff.mp this
      -- 🎉 no goals
    · exact (Polynomial.aeval_map_algebraMap K _ _).trans px
      -- 🎉 no goals
  · exact
      ⟨integerNormalization _ p, mt integerNormalization_eq_zero_iff.mp hp,
        integerNormalization_aeval_eq_zero _ p px⟩
#align is_fraction_ring.is_algebraic_iff IsFractionRing.isAlgebraic_iff

variable {A K C}

/-- A ring is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`.
-/
theorem comap_isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] :
    Algebra.IsAlgebraic A C ↔ Algebra.IsAlgebraic K C :=
  ⟨fun h x => (isAlgebraic_iff A K C).mp (h x), fun h x => (isAlgebraic_iff A K C).mpr (h x)⟩
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
  -- ⊢ IsIntegralElem (IsLocalization.map Sₘ f (_ : M ≤ Submonoid.comap f (Submonoi …
  · exact ⟨0, ⟨_root_.trans leadingCoeff_zero triv.symm, eval₂_zero _ _⟩⟩
    -- 🎉 no goals
  haveI : Nontrivial Rₘ := nontrivial_of_ne 1 0 triv
  -- ⊢ IsIntegralElem (IsLocalization.map Sₘ f (_ : M ≤ Submonoid.comap f (Submonoi …
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (map_units Rₘ ⟨p.leadingCoeff, hM⟩)
  -- ⊢ IsIntegralElem (IsLocalization.map Sₘ f (_ : M ≤ Submonoid.comap f (Submonoi …
  refine' ⟨p.map (algebraMap R Rₘ) * C b, ⟨_, _⟩⟩
  -- ⊢ Monic (Polynomial.map (algebraMap R Rₘ) p * ↑C b)
  · refine' monic_mul_C_of_leadingCoeff_mul_eq_one _
    -- ⊢ leadingCoeff (Polynomial.map (algebraMap R Rₘ) p) * b = 1
    rwa [leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap R Rₘ)]
    -- ⊢ ↑(algebraMap R Rₘ) (leadingCoeff p) ≠ 0
    refine' fun hfp => zero_ne_one
      (_root_.trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1)
  · refine' eval₂_mul_eq_zero_of_left _ _ _ _
    -- ⊢ eval₂ (IsLocalization.map Sₘ f (_ : M ≤ Submonoid.comap f (Submonoid.map f M …
    erw [eval₂_map, IsLocalization.map_comp, ← hom_eval₂ _ f (algebraMap S Sₘ) x]
    -- ⊢ ↑(algebraMap S Sₘ) (eval₂ f x p) = 0
    exact _root_.trans (congr_arg (algebraMap S Sₘ) hf) (RingHom.map_zero _)
    -- 🎉 no goals
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
theorem isIntegral_localization (H : Algebra.IsIntegral R S) :
    (map Sₘ (algebraMap R S)
          (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
        Rₘ →+* _).IsIntegral := by
  intro x
  -- ⊢ RingHom.IsIntegralElem (IsLocalization.map Sₘ (algebraMap R S) (_ : M ≤ Subm …
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (Algebra.algebraMapSubmonoid S M) x
  -- ⊢ RingHom.IsIntegralElem (IsLocalization.map Sₘ (algebraMap R S) (_ : M ≤ Subm …
  obtain ⟨v, hv⟩ := hu
  -- ⊢ RingHom.IsIntegralElem (IsLocalization.map Sₘ (algebraMap R S) (_ : M ≤ Subm …
  obtain ⟨v', hv'⟩ := isUnit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)
  -- ⊢ RingHom.IsIntegralElem (IsLocalization.map Sₘ (algebraMap R S) (_ : M ≤ Subm …
  refine'
    @isIntegral_of_isIntegral_mul_unit Rₘ _ _ _ (localizationAlgebra M S) x (algebraMap S Sₘ u) v' _
      _
  · replace hv' := congr_arg (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) hv'
    -- ⊢ ↑(algebraMap Rₘ Sₘ) v' * ↑(algebraMap S Sₘ) u = 1
    rw [RingHom.map_mul, RingHom.map_one, ← RingHom.comp_apply _ (algebraMap R Rₘ)] at hv'
    -- ⊢ ↑(algebraMap Rₘ Sₘ) v' * ↑(algebraMap S Sₘ) u = 1
    -- Porting note: added argument
    erw [IsLocalization.map_comp
      (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map)] at hv'
    exact hv.2 ▸ hv'
    -- 🎉 no goals
  · obtain ⟨p, hp⟩ := H s
    -- ⊢ IsIntegral Rₘ (x * ↑(algebraMap S Sₘ) u)
    exact hx.symm ▸ is_integral_localization_at_leadingCoeff p hp.2 (hp.1.symm ▸ M.one_mem)
    -- 🎉 no goals
#align is_integral_localization isIntegral_localization

theorem isIntegral_localization' {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IsIntegral) (M : Submonoid R) :
    (map (Localization (M.map (f : R →* S))) f
          (M.le_comap_map : _ ≤ Submonoid.comap (f : R →* S) _) :
        Localization M →+* _).IsIntegral :=
  -- Porting note: added
  letI := f.toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S M)
    (Localization (Submonoid.map (f : R →* S) M)) := Localization.isLocalization
  isIntegral_localization hf
#align is_integral_localization' isIntegral_localization'

variable (M)

theorem IsLocalization.scaleRoots_commonDenom_mem_lifts (p : Rₘ[X])
    (hp : p.leadingCoeff ∈ (algebraMap R Rₘ).range) :
    p.scaleRoots (algebraMap R Rₘ <| IsLocalization.commonDenom M p.support p.coeff) ∈
      Polynomial.lifts (algebraMap R Rₘ) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  -- ⊢ ∀ (n : ℕ), coeff (scaleRoots p (↑(algebraMap R Rₘ) ↑(commonDenom M (support  …
  intro n
  -- ⊢ coeff (scaleRoots p (↑(algebraMap R Rₘ) ↑(commonDenom M (support p) (coeff p …
  rw [Polynomial.coeff_scaleRoots]
  -- ⊢ coeff p n * ↑(algebraMap R Rₘ) ↑(commonDenom M (support p) (coeff p)) ^ (nat …
  by_cases h₁ : n ∈ p.support
  -- ⊢ coeff p n * ↑(algebraMap R Rₘ) ↑(commonDenom M (support p) (coeff p)) ^ (nat …
  by_cases h₂ : n = p.natDegree
  · rwa [h₂, Polynomial.coeff_natDegree, tsub_self, pow_zero, _root_.mul_one]
    -- 🎉 no goals
  · have : n + 1 ≤ p.natDegree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp _ h₁) h₂
    -- ⊢ coeff p n * ↑(algebraMap R Rₘ) ↑(commonDenom M (support p) (coeff p)) ^ (nat …
    rw [← tsub_add_cancel_of_le (le_tsub_of_add_le_left this), pow_add, pow_one, mul_comm,
      _root_.mul_assoc, ← map_pow]
    change _ ∈ (algebraMap R Rₘ).range
    -- ⊢ ↑(algebraMap R Rₘ) (↑(commonDenom M (support p) (coeff p)) ^ (natDegree p -  …
    apply mul_mem
    -- ⊢ ↑(algebraMap R Rₘ) (↑(commonDenom M (support p) (coeff p)) ^ (natDegree p -  …
    · exact RingHom.mem_range_self _ _
      -- 🎉 no goals
    · rw [← Algebra.smul_def]
      -- ⊢ ↑(commonDenom M (support p) (coeff p)) • coeff p n ∈ RingHom.range (algebraM …
      exact ⟨_, IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, h₁⟩⟩
      -- 🎉 no goals
  · rw [Polynomial.not_mem_support_iff] at h₁
    -- ⊢ coeff p n * ↑(algebraMap R Rₘ) ↑(commonDenom M (support p) (coeff p)) ^ (nat …
    rw [h₁, zero_mul]
    -- ⊢ 0 ∈ Set.range ↑(algebraMap R Rₘ)
    exact zero_mem (algebraMap R Rₘ).range
    -- 🎉 no goals
#align is_localization.scale_roots_common_denom_mem_lifts IsLocalization.scaleRoots_commonDenom_mem_lifts

theorem IsIntegral.exists_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S]
    (x : S) (hx : IsIntegral Rₘ x) : ∃ m : M, IsIntegral R (m • x) := by
  cases' subsingleton_or_nontrivial Rₘ with _ nontriv <;> skip
  -- ⊢ ∃ m, IsIntegral R (m • x)
                                                          -- ⊢ ∃ m, IsIntegral R (m • x)
                                                          -- ⊢ ∃ m, IsIntegral R (m • x)
  · haveI := (_root_.algebraMap Rₘ S).codomain_trivial
    -- ⊢ ∃ m, IsIntegral R (m • x)
    exact ⟨1, Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
    -- 🎉 no goals
  obtain ⟨p, hp₁, hp₂⟩ := hx
  -- ⊢ ∃ m, IsIntegral R (m • x)
  -- Porting note: obtain doesn't support side goals
  have :=
    lifts_and_natDegree_eq_and_monic (IsLocalization.scaleRoots_commonDenom_mem_lifts M p ?_) ?_
  obtain ⟨p', hp'₁, -, hp'₂⟩ := this
  · refine' ⟨IsLocalization.commonDenom M p.support p.coeff, p', hp'₂, _⟩
    -- ⊢ eval₂ (_root_.algebraMap R S) (commonDenom M (support p) (coeff p) • x) p' = 0
    rw [IsScalarTower.algebraMap_eq R Rₘ S, ← Polynomial.eval₂_map, hp'₁, Submonoid.smul_def,
      Algebra.smul_def, IsScalarTower.algebraMap_apply R Rₘ S]
    exact Polynomial.scaleRoots_eval₂_eq_zero _ hp₂
    -- 🎉 no goals
  · rw [hp₁.leadingCoeff]
    -- ⊢ 1 ∈ RingHom.range (_root_.algebraMap R Rₘ)
    exact one_mem _
    -- 🎉 no goals
  · rwa [Polynomial.monic_scaleRoots_iff]
    -- 🎉 no goals
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
theorem isFractionRing_of_algebraic (alg : IsAlgebraic A L)
    (inj : ∀ x, algebraMap A L x = 0 → x = 0) : IsFractionRing C L :=
  { map_units' := fun ⟨y, hy⟩ =>
      IsUnit.mk0 _
        (show algebraMap C L y ≠ 0 from fun h =>
          mem_nonZeroDivisors_iff_ne_zero.mp hy
            ((injective_iff_map_eq_zero (algebraMap C L)).mp (algebraMap_injective C A L) _ h))
    surj' := fun z =>
      let ⟨x, y, hy, hxy⟩ := exists_integral_multiple (alg z) inj
      ⟨⟨mk' C (x : L) x.2, algebraMap _ _ y,
          mem_nonZeroDivisors_iff_ne_zero.mpr fun h =>
            hy (inj _ (by rw [IsScalarTower.algebraMap_apply A C L, h, RingHom.map_zero]))⟩,
                          -- 🎉 no goals
        by
          simp only
          -- ⊢ z * ↑(algebraMap C L) (↑(algebraMap A C) y) = ↑(algebraMap C L) (mk' C ↑x (_ …
          rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply A C L, hxy]⟩
          -- 🎉 no goals
    eq_iff_exists' := fun {x y} =>
      ⟨fun h => ⟨1, by simpa using algebraMap_injective C A L h⟩, fun ⟨c, hc⟩ =>
                       -- 🎉 no goals
        congr_arg (algebraMap _ L) (mul_left_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp c.2) hc)⟩ }
#align is_integral_closure.is_fraction_ring_of_algebraic IsIntegralClosure.isFractionRing_of_algebraic

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_finite_extension [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] : IsFractionRing C L :=
  isFractionRing_of_algebraic A C
    (IsFractionRing.comap_isAlgebraic_iff.mpr (isAlgebraic_of_finite K L)) fun _ hx =>
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
theorem isFractionRing_of_algebraic [Algebra A L] (alg : IsAlgebraic A L)
    (inj : ∀ x, algebraMap A L x = 0 → x = 0) : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L) alg inj
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
  simp only [Algebra.IsAlgebraic]
  -- ⊢ (∀ (x : S), IsAlgebraic R x) ↔ ∀ (x : K), IsAlgebraic R x
  constructor
  -- ⊢ (∀ (x : S), IsAlgebraic R x) → ∀ (x : K), IsAlgebraic R x
  · intro h x
    -- ⊢ IsAlgebraic R x
    rw [IsFractionRing.isAlgebraic_iff R (FractionRing R) K, isAlgebraic_iff_isIntegral]
    -- ⊢ IsIntegral (FractionRing R) x
    obtain ⟨a : S, b, ha, rfl⟩ := @div_surjective S _ _ _ _ _ _ x
    -- ⊢ IsIntegral (FractionRing R) (↑(algebraMap S K) a / ↑(algebraMap S K) b)
    obtain ⟨f, hf₁, hf₂⟩ := h b
    -- ⊢ IsIntegral (FractionRing R) (↑(algebraMap S K) a / ↑(algebraMap S K) b)
    rw [div_eq_mul_inv]
    -- ⊢ IsIntegral (FractionRing R) (↑(algebraMap S K) a * (↑(algebraMap S K) b)⁻¹)
    refine' isIntegral_mul _ _
    -- ⊢ IsIntegral (FractionRing R) (↑(algebraMap S K) a)
    · rw [← isAlgebraic_iff_isIntegral]
      -- ⊢ IsAlgebraic (FractionRing R) (↑(algebraMap S K) a)
      refine'
        _root_.isAlgebraic_of_larger_base_of_injective
          (NoZeroSMulDivisors.algebraMap_injective R (FractionRing R)) _
      exact isAlgebraic_algebraMap_of_isAlgebraic (h a)
      -- 🎉 no goals
    · rw [← isAlgebraic_iff_isIntegral]
      -- ⊢ IsAlgebraic (FractionRing R) (↑(algebraMap S K) b)⁻¹
      use (f.map (algebraMap R (FractionRing R))).reverse
      -- ⊢ reverse (Polynomial.map (algebraMap R (FractionRing R)) f) ≠ 0 ∧ ↑(aeval (↑( …
      constructor
      -- ⊢ reverse (Polynomial.map (algebraMap R (FractionRing R)) f) ≠ 0
      · rwa [Ne.def, Polynomial.reverse_eq_zero, ← Polynomial.degree_eq_bot,
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
    -- ⊢ IsAlgebraic R x
    obtain ⟨f, hf₁, hf₂⟩ := h (algebraMap S K x)
    -- ⊢ IsAlgebraic R x
    use f, hf₁
    -- ⊢ ↑(aeval x) f = 0
    rw [Polynomial.aeval_algebraMap_apply] at hf₂
    -- ⊢ ↑(aeval x) f = 0
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
    (alg : Algebra.IsAlgebraic R L) (inj : Function.Injective (algebraMap R L))
    (h : (Ideal.span ({a} : Set S) : Set S) ⊆ Submodule.span R b) :
    (Ideal.span ({algebraMap S L a} : Set L) : Set L) ⊆ Submodule.span K (algebraMap S L '' b) := by
  intro x hx
  -- ⊢ x ∈ ↑(Submodule.span K (↑(algebraMap S L) '' b))
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton.mp hx
  -- ⊢ ↑(algebraMap S L) a * x' ∈ ↑(Submodule.span K (↑(algebraMap S L) '' b))
  obtain ⟨y', z', rfl⟩ := IsLocalization.mk'_surjective S⁰ x'
  -- ⊢ ↑(algebraMap S L) a * mk' L y' z' ∈ ↑(Submodule.span K (↑(algebraMap S L) '' …
  obtain ⟨y, z, hz0, yz_eq⟩ :=
    IsIntegralClosure.exists_smul_eq_mul alg inj y' (nonZeroDivisors.coe_ne_zero z')
  have injRS : Function.Injective (algebraMap R S) := by
    refine'
      Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ algebraMap R S) from _)
    rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  have hz0' : algebraMap R S z ∈ S⁰ :=
    map_mem_nonZeroDivisors (algebraMap R S) injRS (mem_nonZeroDivisors_of_ne_zero hz0)
  have mk_yz_eq : IsLocalization.mk' L y' z' = IsLocalization.mk' L y ⟨_, hz0'⟩ := by
    rw [Algebra.smul_def, mul_comm _ y, mul_comm _ y'] at yz_eq
    exact IsLocalization.mk'_eq_of_eq (by rw [mul_comm _ y, mul_comm _ y', yz_eq])
  suffices hy : algebraMap S L (a * y) ∈ Submodule.span K ((algebraMap S L) '' b)
  -- ⊢ ↑(algebraMap S L) a * mk' L y' z' ∈ ↑(Submodule.span K (↑(algebraMap S L) '' …
  · rw [mk_yz_eq, IsFractionRing.mk'_eq_div, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, div_eq_mul_inv, ← mul_assoc, mul_comm, ← map_inv₀, ←
      Algebra.smul_def, ← _root_.map_mul]
    exact (Submodule.span K _).smul_mem _ hy
    -- 🎉 no goals
  refine' Submodule.span_subset_span R K _ _
  -- ⊢ ↑(algebraMap S L) (a * y) ∈ ↑(Submodule.span R (↑(algebraMap S L) '' b))
  rw [Submodule.span_algebraMap_image_of_tower]
  -- ⊢ ↑(algebraMap S L) (a * y) ∈ ↑(Submodule.map (↑R (Algebra.linearMap S L)) (Su …
  exact Submodule.mem_map_of_mem (h (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩))
  -- 🎉 no goals
#align is_fraction_ring.ideal_span_singleton_map_subset IsFractionRing.ideal_span_singleton_map_subset

end IsFractionRing
