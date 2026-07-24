/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKInterface
import Archive.GaussianMomentConjecture.FaceDictionary
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Nonzero DvdK seed on the rational lowest face

Assuming the explicitly named one-variable DvdK input, this module composes
the exact-support lowest face, collision-free charge projection, and the
universal constant-term relation.  The result is the nonzero face polynomial
value `Q` used by the Frobenius amplification.
-/

open MvPolynomial Finset

namespace GMC2.FaceSeed

/-- The pair of integer coordinates determines a `Fin 2` Finsupp exactly. -/
theorem exponentPair_injective :
    Function.Injective
      (fun s : Fin 2 →₀ ℕ =>
        (GMC2.FaceDictionary.exponentA s,
          GMC2.FaceDictionary.exponentB s)) := by
  intro s t h
  have hzero : s 0 = t 0 := by
    have hz := congrArg Prod.fst h
    simp only [GMC2.FaceDictionary.exponentA] at hz
    exact_mod_cast hz
  have hone : s 1 = t 1 := by
    have ho := congrArg Prod.snd h
    simp only [GMC2.FaceDictionary.exponentB] at ho
    exact_mod_cast ho
  apply Finsupp.ext
  intro i
  fin_cases i
  · simpa using hzero
  · simpa using hone

/-- A straddling predicate on a face Finset becomes the same predicate on its
subtype indexed by `Finset.univ`. -/
theorem chargesStraddleZero_subtype
    (F : Finset (Fin 2 →₀ ℕ))
    (hF : GMC2.LowestFaceExistence.ChargesStraddleZero F GMC2.chargeQ) :
    GMC2.LowestFaceExistence.ChargesStraddleZero
      (Finset.univ : Finset ↥F)
      (fun s : ↥F => (GMC2.charge s : ℚ)) := by
  rcases hF with hzero | ⟨hminus, hplus⟩
  · left
    obtain ⟨s, hs, hq⟩ := hzero
    refine ⟨⟨s, hs⟩, Finset.mem_univ _, ?_⟩
    simpa [GMC2.chargeQ] using hq
  · right
    constructor
    · obtain ⟨s, hs, hq⟩ := hminus
      refine ⟨⟨s, hs⟩, Finset.mem_univ _, ?_⟩
      simpa [GMC2.chargeQ] using hq
    · obtain ⟨s, hs, hq⟩ := hplus
      refine ⟨⟨s, hs⟩, Finset.mem_univ _, ?_⟩
      simpa [GMC2.chargeQ] using hq

/-- **Lowest-face DvdK seed.**  A failure of one-sidedness produces an exact
face `F` and a positive level `m₀` at which the face constant-term relation is
nonzero.  Charge injectivity is proved, not assumed. -/
theorem exists_nonzero_lowest_face_seed
    (hDvdK : GMC2.DvdKInterface.DvdK1)
    (P : MvPolynomial (Fin 2) ℂ) (hP : ¬GMC2.ChargeOneSided P) :
    ∃ lambda delta : ℚ, ∃ F : Finset (Fin 2 →₀ ℕ), ∃ m0 : ℕ,
      1 ≤ m0 ∧
      F ⊆ P.support ∧
      (∀ s ∈ P.support,
        delta ≤ GMC2.radialExponentQ s - lambda * GMC2.chargeQ s) ∧
      (∀ s, s ∈ F ↔ s ∈ P.support ∧
        GMC2.radialExponentQ s - lambda * GMC2.chargeQ s = delta) ∧
      MvPolynomial.aeval (fun s : ↥F => P.coeff s)
        (GMC2.ConstantTermRelations.constantTermRelation
          (fun s : ↥F => GMC2.charge s) m0) ≠ 0 := by
  obtain ⟨lambda, delta, F, hsubset, hlower, hface, hstraddle⟩ :=
    GMC2.exists_rational_lowest_face_finset P hP
  have hfaceTilted : ∀ s ∈ F,
      GMC2.FrobeniusFace.tiltedHeight
        GMC2.FaceDictionary.exponentA GMC2.FaceDictionary.exponentB lambda s = delta := by
    intro s hs
    rw [GMC2.FaceDictionary.tiltedHeight_eq]
    exact (hface s).mp hs |>.2
  have hchargeInjective :
      Function.Injective (fun s : ↥F => GMC2.charge s) := by
    simpa only [GMC2.FaceDictionary.charge_eq] using
      (GMC2.FrobeniusFace.charge_injective_on_face
        GMC2.FaceDictionary.exponentA GMC2.FaceDictionary.exponentB
        lambda delta F exponentPair_injective hfaceTilted)
  have hcoeff : ∀ s : ↥F, P.coeff s ≠ 0 := by
    intro s
    have hsSupport : (s : Fin 2 →₀ ℕ) ∈ P.support := hsubset s.property
    simpa only [MvPolynomial.mem_support_iff] using hsSupport
  obtain ⟨m0, hm0, hseed⟩ :=
    GMC2.DvdKInterface.exists_nonzero_face_seed hDvdK ↥F
      (fun s : ↥F => GMC2.charge s) (fun s : ↥F => P.coeff s)
      hchargeInjective hcoeff (chargesStraddleZero_subtype F hstraddle)
  exact ⟨lambda, delta, F, m0, hm0, hsubset, hlower, hface, hseed⟩

end GMC2.FaceSeed
