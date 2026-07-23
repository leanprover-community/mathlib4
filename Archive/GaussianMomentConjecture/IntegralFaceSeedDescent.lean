/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.FaceSeedDescent
import Archive.GaussianMomentConjecture.IntegralRelations
import Archive.GaussianMomentConjecture.IntegralTorusSpecialization
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Integral lowest-face seed descent to finite characteristic

This module replaces the rational lifted face seed by its integral model and
then applies universal integral torus specialization.  The resulting finite
field point preserves every integral polynomial zero relation of the original
complex support-coefficient point.  In particular, all positive integral
Wick-moment relations remain zero, while the selected lowest-face seed remains
nonzero.
-/

open MvPolynomial Finset

namespace GMC2.IntegralFaceSeedDescent

noncomputable section

/-- The integral face constant-term seed, renamed from the exact face to the
full support of `P`. -/
def liftedFaceSeedInt
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (m0 : ℕ) :
    MvPolynomial ↥P.support ℤ :=
  MvPolynomial.rename (GMC2.FaceSeedDescent.faceToSupport hsubset)
    (GMC2.IntegralRelations.constantTermRelationInt
      (fun s : ↥F ↦ GMC2.charge s) m0)

/-- Evaluation of the integral lifted seed is evaluation of the face seed on
the restricted coefficient family. -/
theorem aeval_liftedFaceSeedInt
    {R : Type*} [CommRing R] [Algebra ℤ R]
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (m0 : ℕ)
    (coefficient : ↥P.support → R) :
    MvPolynomial.aeval coefficient (liftedFaceSeedInt P F hsubset m0) =
      MvPolynomial.aeval
        (coefficient ∘ GMC2.FaceSeedDescent.faceToSupport hsubset)
        (GMC2.IntegralRelations.constantTermRelationInt
          (fun s : ↥F ↦ GMC2.charge s) m0) := by
  exact MvPolynomial.aeval_rename _ _ _

/-- **Integral lowest-face seed descent.**

Under the explicit one-variable DvdK input, a positive moment-null polynomial
that is not charge-one-sided yields exact rational face data and a finite-field
torus point on its exact support.  The point has prime characteristic, all
coordinates remain nonzero, every integral zero relation of the original
complex coefficient point is preserved, every positive integral moment
relation vanishes, and the integral lifted face seed remains nonzero. -/
theorem exists_finite_field_moment_point_seed
    (hDvdK : GMC2.DvdKInterface.DvdK1)
    (P : MvPolynomial (Fin 2) ℂ)
    (hnull : ∀ m : ℕ, 1 ≤ m → GMC2.E (P ^ m) = 0)
    (hP : ¬GMC2.ChargeOneSided P) :
    ∃ lambda delta : ℚ, ∃ F : Finset (Fin 2 →₀ ℕ), ∃ m0 : ℕ,
      ∃ hsubset : F ⊆ P.support,
        1 ≤ m0 ∧
        (∀ s ∈ P.support,
          delta ≤ GMC2.radialExponentQ s - lambda * GMC2.chargeQ s) ∧
        (∀ s, s ∈ F ↔ s ∈ P.support ∧
          GMC2.radialExponentQ s - lambda * GMC2.chargeQ s = delta) ∧
        ∃ (A : Subalgebra ℤ ℂ) (D : GMC2.IntegralSpecialization.ResidueData A)
          (w : ↥P.support → D.ResidueField),
          D.p.Prime ∧
          CharP D.ResidueField D.p ∧
          Finite D.ResidueField ∧
          IsField D.ResidueField ∧
          (∀ i, IsUnit (w i)) ∧
          (∀ i, w i ≠ 0) ∧
          (∀ f : MvPolynomial ↥P.support ℤ,
            MvPolynomial.aeval (fun s : ↥P.support ↦ P.coeff s) f = 0 →
              MvPolynomial.aeval w f = 0) ∧
          (∀ m : ℕ, 1 ≤ m →
            MvPolynomial.aeval w
              (GMC2.IntegralRelations.momentRelationInt
                (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) m) = 0) ∧
          MvPolynomial.aeval w (liftedFaceSeedInt P F hsubset m0) ≠ 0 := by
  classical
  obtain ⟨lambda, delta, F, m0, hm0, hsubset, hlower, hface, hseed⟩ :=
    GMC2.FaceSeed.exists_nonzero_lowest_face_seed hDvdK P hP
  let coefficient : ↥P.support → ℂ := fun s ↦ P.coeff s
  have hcoefficient : ∀ s, coefficient s ≠ 0 := by
    intro s
    simpa only [coefficient, MvPolynomial.mem_support_iff] using s.property
  have hfaceModelBridge :
      MvPolynomial.aeval
          (coefficient ∘ GMC2.FaceSeedDescent.faceToSupport hsubset)
          (GMC2.IntegralRelations.constantTermRelationInt
            (fun s : ↥F ↦ GMC2.charge s) m0) =
        MvPolynomial.aeval
          (coefficient ∘ GMC2.FaceSeedDescent.faceToSupport hsubset)
          (GMC2.ConstantTermRelations.constantTermRelation
            (fun s : ↥F ↦ GMC2.charge s) m0) := by
    rw [GMC2.IntegralRelations.aeval_constantTermRelationInt,
      GMC2.ConstantTermRelations.aeval_constantTermRelation]
  have hseedInt :
      MvPolynomial.aeval coefficient
        (liftedFaceSeedInt P F hsubset m0) ≠ 0 := by
    rw [aeval_liftedFaceSeedInt]
    rw [hfaceModelBridge]
    simpa [coefficient, GMC2.FaceSeedDescent.faceToSupport,
      Function.comp_def] using hseed
  have hmomentInt : ∀ m : ℕ, 1 ≤ m →
      MvPolynomial.aeval coefficient
        (GMC2.IntegralRelations.momentRelationInt
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) m) = 0 := by
    intro m hm
    rw [← GMC2.IntegralRelations.E_indexedPolynomial_pow_eq_aeval_momentRelationInt]
    rw [GMC2.SupportDescent.indexedPolynomial_support_eq]
    exact hnull m hm
  obtain ⟨A, D, w, hp, hchar, hfinite, hfield,
      hunit, hnonzero, huniversal, hseedFinite⟩ :=
    GMC2.IntegralTorusSpecialization.exists_finite_field_torus_specialization
      coefficient hcoefficient (liftedFaceSeedInt P F hsubset m0) hseedInt
  refine ⟨lambda, delta, F, m0, hsubset, hm0, hlower, hface,
    A, D, w, hp, hchar, hfinite, hfield, hunit, hnonzero, ?_, ?_, hseedFinite⟩
  · intro f hf
    exact huniversal f hf
  · intro m hm
    exact huniversal _ (hmomentInt m hm)

end

end GMC2.IntegralFaceSeedDescent

