/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKFrame
import Archive.GaussianMomentConjecture.DvdKTranspose
import Archive.GaussianMomentConjecture.DvdKWeierstrass
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.LaurentSeries

/-!
# The connector `φ(Φ_weier) = PhiFrame` — the transpose meets the frame

The transpose `φ` (GMC2.DvdKTranspose) carries the Weierstrass world `F⟦t⟧⟦x⟧` into frame
`(F⸨x⸩)⟦t⟧`.  This module proves it carries `Φ_weier = xᴹ − t·R` to `PhiFrame`, so that `φ(Φ = P·h)`
gives the frame factorization `PhiFrame = φ(P)·φ(h)` feeding `GMC2.DvdKHderiv.hderiv_of_frame`.
-/

open PowerSeries GMC2.DvdKTranspose GMC2.DvdKFrame

namespace GMC2.DvdKConnector

variable {F : Type*} [Field F]

theorem phi_R_map (R : Polynomial F) :
    phi ((R.map (algebraMap F (PowerSeries F)) : PowerSeries (PowerSeries F)))
      = PowerSeries.C (Polynomial.aeval (HahnSeries.single (1 : ℤ) (1 : F)) R) := by
  have key : (phi.comp (Polynomial.coeToPowerSeries.ringHom)).comp
        (Polynomial.mapRingHom (algebraMap F (PowerSeries F)))
      = (PowerSeries.C (R := LaurentSeries F)).comp
          (Polynomial.aeval (HahnSeries.single (1 : ℤ) (1 : F))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Polynomial.aeval_C]
      rw [show (algebraMap F (PowerSeries F)) a = PowerSeries.C a from rfl, phi_C_C,
        LaurentSeries.algebraMap_apply]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Polynomial.aeval_X, phi_X]
  have h := DFunLike.congr_fun key R
  simpa only [RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.coeToPowerSeries.ringHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h

/-- **The connector: `φ(Φ_weier) = PhiFrame`.** -/
theorem phi_Phi (R : Polynomial F) (M : ℕ) :
    phi (GMC2.DvdKWeierstrass.Phi R M)
      = PhiFrame (Polynomial.aeval (HahnSeries.single (1 : ℤ) (1 : F)) R) M := by
  rw [GMC2.DvdKWeierstrass.Phi, PhiFrame, map_sub, map_pow, phi_X, map_mul, phi_C_X, phi_R_map,
    ← map_pow, HahnSeries.single_pow, one_pow]

/-- **Rl-canonicalization.** The two frame representations of `R` coincide: mapping the polynomial
`R` into `LaurentSeries F` through `F⟦t⟧` (`ofPowerSeries ∘ coe`, `Rl R`) equals evaluating at the
Laurent variable `single 1 1` (`aeval`, this connector's form). Both are `∑ Rₙ · (single 1 1)ⁿ`. So
the two `phi_Phi` proofs (`GMC2.DvdKConnector.phi_Phi`, `GMC2.DvdKTransposeAssembly.phi_Phi`) are
one statement. -/
theorem ofPowerSeries_coe_eq_aeval (R : Polynomial F) :
    HahnSeries.ofPowerSeries ℤ F (R : PowerSeries F)
      = Polynomial.aeval (HahnSeries.single (1 : ℤ) (1 : F)) R := by
  have hext : (HahnSeries.ofPowerSeries ℤ F).comp Polynomial.coeToPowerSeries.ringHom
      = ((Polynomial.aeval (HahnSeries.single (1 : ℤ) (1 : F)) :
          Polynomial F →ₐ[F] LaurentSeries F)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [Polynomial.coeToPowerSeries.ringHom, HahnSeries.ofPowerSeries_C,
        LaurentSeries.algebraMap_apply]
    · simp [Polynomial.coeToPowerSeries.ringHom, HahnSeries.ofPowerSeries_X]
  simpa [Polynomial.coeToPowerSeries.ringHom] using RingHom.congr_fun hext R

end GMC2.DvdKConnector
