/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.FaceSeed
import Archive.GaussianMomentConjecture.SupportDescent
import Archive.GaussianMomentConjecture.TorusDescent
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Number-field descent preserving a nonzero lowest-face seed

This module composes the exact lowest-face DvdK seed with the universal
rational moment relations and torus specialization.  The face polynomial is
renamed from variables indexed by the face `F` to variables indexed by the
full support of `P`; adjoining the inverse of its nonzero complex value then
ensures that the number-field specialization preserves the seed.
-/

open MvPolynomial Finset

namespace GMC2.FaceSeedDescent

noncomputable section

local instance : Algebra ℚ ℂ := (Rat.castHom ℂ).toAlgebra

/-- Inclusion of an exact face into the full support, retaining the membership
proof needed by the target subtype. -/
def faceToSupport
    {P : MvPolynomial (Fin 2) ℂ} {F : Finset (Fin 2 →₀ ℕ)}
    (hsubset : F ⊆ P.support) : ↥F → ↥P.support :=
  fun s ↦ ⟨s, hsubset s.property⟩

/-- The face constant-term polynomial, regarded as a polynomial in all exact
support coefficients by renaming along the face inclusion. -/
def liftedFaceSeed
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (m0 : ℕ) :
    MvPolynomial ↥P.support ℚ :=
  MvPolynomial.rename (faceToSupport hsubset)
    (GMC2.ConstantTermRelations.constantTermRelation
      (fun s : ↥F ↦ GMC2.charge s) m0)

/-- Evaluating the lifted seed on support coefficients is exactly the same as
evaluating the original face seed on the restricted coefficient family. -/
theorem aeval_liftedFaceSeed
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (m0 : ℕ)
    (coefficient : ↥P.support → R) :
    MvPolynomial.aeval coefficient (liftedFaceSeed P F hsubset m0) =
      MvPolynomial.aeval (coefficient ∘ faceToSupport hsubset)
        (GMC2.ConstantTermRelations.constantTermRelation
          (fun s : ↥F ↦ GMC2.charge s) m0) := by
  exact MvPolynomial.aeval_rename _ _ _

/-- **Lowest-face seed preserving descent.**  Under the explicit one-variable
DvdK input, a moment-null polynomial which is not charge-one-sided has an
exact rational lowest face and a positive nonzero face seed.  Its exact
support coefficient point specializes to a torus point over a number field
which still satisfies every positive universal moment relation and at which
the lifted seed remains nonzero. -/
theorem exists_numberField_moment_point_preserving_lowest_face_seed
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
        ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K),
          Module.Finite ℚ K ∧
            ∃ coefficientK : ↥P.support → K,
              (∀ i, coefficientK i ≠ 0) ∧
              (∀ m : ℕ,
                MvPolynomial.aeval coefficientK
                  (GMC2.MomentRelations.momentRelation
                    (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) (m + 1)) = 0) ∧
              MvPolynomial.aeval coefficientK
                (liftedFaceSeed P F hsubset m0) ≠ 0 := by
  obtain ⟨lambda, delta, F, m0, hm0, hsubset, hlower, hface, hseed⟩ :=
    GMC2.FaceSeed.exists_nonzero_lowest_face_seed hDvdK P hP

  let coefficient : ↥P.support → ℂ := fun s ↦ P.coeff s
  have hcoefficient : ∀ s, coefficient s ≠ 0 := by
    intro s
    simpa only [coefficient, MvPolynomial.mem_support_iff] using s.property

  have hmoment : ∀ m : ℕ,
      MvPolynomial.aeval coefficient
        (GMC2.MomentRelations.momentRelation
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) (m + 1)) = 0 := by
    intro m
    calc
      MvPolynomial.aeval coefficient
          (GMC2.MomentRelations.momentRelation
            (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) (m + 1)) =
        GMC2.E
          ((GMC2.MomentTransport.indexedPolynomial
            (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) coefficient) ^ (m + 1)) :=
        (GMC2.MomentTransport.E_indexedPolynomial_pow_eq_aeval_momentRelation
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) coefficient (m + 1)).symm
      _ = GMC2.E (P ^ (m + 1)) := by
        rw [GMC2.SupportDescent.indexedPolynomial_support_eq]
      _ = 0 := hnull (m + 1) (by omega)

  have hseedLifted :
      MvPolynomial.aeval coefficient (liftedFaceSeed P F hsubset m0) ≠ 0 := by
    rw [aeval_liftedFaceSeed]
    simp only [coefficient, faceToSupport, Function.comp_def]
    convert hseed using 2 <;> rfl

  obtain ⟨K, fieldK, algebraK, hfinite, coefficientK,
      hcoefficientK, hmomentK, hseedK⟩ :=
    GMC2.TorusDescent.exists_numberField_torus_point_preserving_nonzero_of_complex_relations
      (fun m : ℕ ↦
        GMC2.MomentRelations.momentRelation
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) (m + 1))
      (liftedFaceSeed P F hsubset m0)
      coefficient hcoefficient hmoment hseedLifted
  exact ⟨lambda, delta, F, m0, hsubset, hm0, hlower, hface,
    K, fieldK, algebraK, hfinite, coefficientK,
    hcoefficientK, hmomentK, hseedK⟩

end

end GMC2.FaceSeedDescent

