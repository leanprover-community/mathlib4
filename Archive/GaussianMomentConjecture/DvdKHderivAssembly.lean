/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKConnector
import Archive.GaussianMomentConjecture.DvdKFrameExtraction
import Archive.GaussianMomentConjecture.DvdKFrameHSide
import Archive.GaussianMomentConjecture.DvdKHderiv
import Archive.GaussianMomentConjecture.DvdKTranspose
import Archive.GaussianMomentConjecture.DvdKWeierstrass
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.LogDeriv

/-!
# `hderiv` assembly through the transpose: plugging in the frame-leg lemmas

The `hderiv` assembly `GMC2.DvdKHderiv.hderiv_of_frame` takes five per-object inputs on the frame
factors `Pfr, hfr`. Through transpose `phi = map(ofPowerSeries) ∘ tauHom`, the Weierstrass unit's
image `hfr = phi Wu` is *definitionally* `map ofPowerSeries (tau Wu)` — exactly the disk form of the
h-side lemma. So the two analytic inputs `ha` and `hF1` are discharged here by

* `GMC2.DvdKFrameHSide.xCoeff0_logDeriv_map_ofPowerSeries` (the `h`-side, leg (a)), and
* `GMC2.DvdKFrameExtraction.xCoeff0_xM_div_PhiFrame_eq_one_of_vanish` (the `F = D_m` / `F = 1`
  extraction),

leaving `hderiv` reduced to exactly the **concrete transpose glue** (`hfact = phi(Φ)=PhiFrame`,
`Pfr`'s monic/unit data, the `xCoeff0 hfr` unit, and the polynomial-to-frame moment transport
`hvanish`) — the analytic lane. When those land, `hderiv` (and hence GMC(2)) closes with no new
analysis.
-/

open PowerSeries

namespace GMC2.DvdKHderivAssembly

variable {F : Type*} [Field F]

/-- **`hderiv` through the transpose.** For the transported Weierstrass unit `hfr = phi Wu` and a
distinguished frame factor `Pfr`, given the concrete transpose glue — the factorization `hfact`,
`Pfr` a unit with `xCoeff0(logDeriv Pfr)=0` (the (c) degree lemma), `xCoeff0(phi Wu)` a unit, and
the vanishing of every positive frame moment `(Rlᵐ).coeff(M·m)` — the `t`-derivative of
`xCoeff0(phi Wu) = h(0,t)` vanishes. The h-side `ha` and the `F=1` input `hF1` are supplied
internally by the frame-leg lemmas. -/
theorem hderiv_via_transpose (Rl : LaurentSeries F) (M : ℕ)
    (Wu : PowerSeries (PowerSeries F)) (hWu : IsUnit Wu)
    (Pfr : PowerSeries (LaurentSeries F))
    (hfact : GMC2.DvdKFrame.PhiFrame Rl M = Pfr * GMC2.DvdKTranspose.phi Wu)
    (hPu : IsUnit Pfr)
    (hc : GMC2.DvdKFrame.xCoeff0 (PowerSeries.logDeriv Pfr) = 0)
    (hg : IsUnit (GMC2.DvdKFrame.xCoeff0 (GMC2.DvdKTranspose.phi Wu)))
    (hvanish : ∀ m : ℕ, 1 ≤ m → (Rl ^ m).coeff ((M : ℤ) * m) = 0) :
    PowerSeries.derivative _ (GMC2.DvdKFrame.xCoeff0 (GMC2.DvdKTranspose.phi Wu)) = 0 := by
  have hphi : GMC2.DvdKTranspose.phi Wu
      = PowerSeries.map (HahnSeries.ofPowerSeries ℤ F) (GMC2.DvdKTranspose.tau Wu) := by
    rw [GMC2.DvdKTranspose.phi, RingHom.comp_apply]; rfl
  have hHu : IsUnit (GMC2.DvdKTranspose.tau Wu) := by
    have h := hWu.map GMC2.DvdKTranspose.tauHom
    rwa [show GMC2.DvdKTranspose.tauHom Wu = GMC2.DvdKTranspose.tau Wu from rfl] at h
  rw [hphi] at hfact hg ⊢
  exact GMC2.DvdKHderiv.hderiv_of_frame Rl M Pfr _ hfact hPu
    (hHu.map (PowerSeries.map (HahnSeries.ofPowerSeries ℤ F)))
    hc
    (GMC2.DvdKFrameHSide.xCoeff0_logDeriv_map_ofPowerSeries hHu)
    hg
    (GMC2.DvdKFrameExtraction.xCoeff0_xM_div_PhiFrame_eq_one_of_vanish Rl M hvanish)

/-- **`hderiv` on the concrete Weierstrass unit.** With the bridge `xCoeff0(phi Wu) = unitCoeff0`
(the frame's constant-in-`x` coefficient equals Weierstrass `h(0,t)`), `hderiv_via_transpose`
becomes the literal DvdK statement `d_t(unitCoeff0) = 0`. -/
theorem hderiv_of_transpose_glue (Rl : LaurentSeries F) (M : ℕ)
    (Wu : PowerSeries (PowerSeries F)) (hWu : IsUnit Wu)
    (Pfr : PowerSeries (LaurentSeries F))
    (hfact : GMC2.DvdKFrame.PhiFrame Rl M = Pfr * GMC2.DvdKTranspose.phi Wu)
    (hPu : IsUnit Pfr)
    (hc : GMC2.DvdKFrame.xCoeff0 (PowerSeries.logDeriv Pfr) = 0)
    (hg : IsUnit (GMC2.DvdKFrame.xCoeff0 (GMC2.DvdKTranspose.phi Wu)))
    (hvanish : ∀ m : ℕ, 1 ≤ m → (Rl ^ m).coeff ((M : ℤ) * m) = 0)
    (unitCoeff0 : PowerSeries F)
    (hbridge : GMC2.DvdKFrame.xCoeff0 (GMC2.DvdKTranspose.phi Wu) = unitCoeff0) :
    PowerSeries.derivative _ unitCoeff0 = 0 := by
  rw [← hbridge]
  exact hderiv_via_transpose Rl M Wu hWu Pfr hfact hPu hc hg hvanish

/-- **`hfact` for the concrete Weierstrass objects** — discharged by composing connector `phi_Phi`
(`phi(Φ)=PhiFrame`) with the Weierstrass factorization `Φ = ↑smallRootFactor · h`. Supplies the unit
`Wu` and the factorization `PhiFrame = phi(↑smallRootFactor) · phi Wu` that `hderiv_via_transpose`
consumes, so `hfact` is no longer a free hypothesis for the concrete run. -/
theorem phiFrame_eq_phi_smallRootFactor_mul (R : Polynomial F) (M : ℕ) :
    ∃ Wu : PowerSeries (PowerSeries F), IsUnit Wu ∧
      GMC2.DvdKFrame.PhiFrame (Polynomial.aeval (HahnSeries.single (1 : ℤ) (1 : F)) R) M
        = GMC2.DvdKTranspose.phi ((GMC2.DvdKWeierstrass.smallRootFactor R M : (PowerSeries F)⟦X⟧))
          * GMC2.DvdKTranspose.phi Wu := by
  obtain ⟨h, hu, hfeq⟩ := GMC2.DvdKWeierstrass.phi_eq_smallRootFactor_mul R M
  exact ⟨h, hu, by rw [← GMC2.DvdKConnector.phi_Phi, hfeq, map_mul]⟩

/-! ## Remaining connector: the R→Rl moment transport (specified, for HahnSeries frame)

`phi_Phi` fixes the frame `Rl = aeval (single 1 1) R`. The one remaining hypothesis of
`hderiv_via_transpose` not yet discharged is `hvanish`. It reduces to the coefficient-preservation
fact `(aeval (single 1 1) P).coeff (k : ℤ) = P.coeff k` (the `aeval (single 1 1)` embedding
`Polynomial F → F⸨x⸩` preserves coefficients at natural indices), giving
`((aeval (single 1 1) R)^m).coeff(M·m) = (R^m).coeff(M·m) = D_m`; then `generatingFunction_eq_one`
supplies the polynomial vanishing `D_m = 0`. This is a pure HahnSeries-single computation (no
analysis), left to the transpose owner to match the frame's exact coercion conventions. -/

end GMC2.DvdKHderivAssembly

