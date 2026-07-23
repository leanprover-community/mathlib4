/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKMultiplicativeClosing
import Archive.GaussianMomentConjecture.DvdKWeierstrass
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

set_option linter.minImports true

/-!
# `hconst` discharged: the Weierstrass unit of `Φ = Xᴹ − t·R` is `1` at the origin

`GMC2.DvdKMultiplicativeClosing.smallRootFactor_coeff0_eq_of_derivative_vanishes` closes the
multiplicative the small-root product identity crux (`Π = c·t`) modulo two hypotheses on the
Weierstrass unit `h`:

* `hconst : constantCoeff_t(h(0,t)) = 1` — the origin normalization, and
* `hderiv : d_t(h(0,t)) = 0` — the deep `[x⁰]`-Laurent log-derivative identity under `D_m = 0`.

This module **discharges `hconst` unconditionally** (kernel-pure, no `CharZero` needed).  It is
elementary: reducing `Φ = P·h` modulo `t` (applying the ring hom `PowerSeries.map (constantCoeff)`,
which kills the `−t·R` term and, since `P` is distinguished, sends `P ↦ xᴹ` and `Φ ↦ xᴹ`) gives
`xᴹ = xᴹ · (h mod t)` in `F⟦x⟧`, a domain, so `h mod t = 1`; the `x`-constant term is `h(0,0) = 1`.

Consequently the entire multiplicative route is kernel-pure **modulo exactly `hderiv`** — the single
remaining analytic input (the `[x⁰]` derivative identity), the shared valuation crux.
-/

open PowerSeries GMC2.DvdKWeierstrass

namespace GMC2.DvdKUnitOrigin

variable {F : Type*} [Field F]

/-- `Φ mod t = xᴹ` via the ring hom `constantCoeff : F⟦t⟧ → F` (reduce the inner `t`). -/
theorem map_constantCoeff_Phi (R : Polynomial F) (M : ℕ) :
    PowerSeries.map (PowerSeries.constantCoeff (R := F)) (Phi R M) = PowerSeries.X ^ M := by
  have hX : PowerSeries.constantCoeff (R := F) (PowerSeries.X : PowerSeries F) = 0 :=
    PowerSeries.constantCoeff_X
  rw [Phi, map_sub, map_pow, PowerSeries.map_X, map_mul, PowerSeries.map_C, hX, map_zero,
    zero_mul, sub_zero]

/-- The distinguished small-root factor `P` also reduces to `xᴹ` mod `t` (its lower coefficients lie
in the maximal ideal `(t)`, its leading coefficient is `1`). -/
theorem map_constantCoeff_smallRootFactor (R : Polynomial F) (M : ℕ) :
    PowerSeries.map (PowerSeries.constantCoeff (R := F))
        ((smallRootFactor R M : (PowerSeries F)⟦X⟧)) = PowerSeries.X ^ M := by
  have hdist : (smallRootFactor R M).IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries F)) :=
    PowerSeries.isDistinguishedAt_weierstrassDistinguished (phi_residue_ne_zero R M)
  have hdeg := smallRootFactor_natDegree R M
  ext n
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe]
  rcases lt_trichotomy n M with hlt | heq | hgt
  · have hmem : (smallRootFactor R M).coeff n ∈ IsLocalRing.maximalIdeal (PowerSeries F) :=
      hdist.mem (by rw [hdeg]; exact hlt)
    have h0 : PowerSeries.constantCoeff (R := F) ((smallRootFactor R M).coeff n) = 0 := by
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton] at hmem
      exact PowerSeries.X_dvd_iff.mp hmem
    rw [h0, PowerSeries.coeff_X_pow, if_neg (by omega)]
  · rw [heq]
    have hlc : (smallRootFactor R M).coeff M = 1 := by
      have hm := smallRootFactor_monic R M
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at hm
      exact hm
    rw [hlc, map_one, PowerSeries.coeff_X_pow, if_pos rfl]
  · have h0 : (smallRootFactor R M).coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hgt)
    rw [h0, map_zero, PowerSeries.coeff_X_pow, if_neg (by omega)]

/-- **`hconst`, discharged.**  The Weierstrass unit's value at the origin is `1`:
`constantCoeff_t(constantCoeff_x h) = 1`.  From `Φ = P·h`, reduce mod `t` and cancel `xᴹ` in the
domain `F⟦x⟧`. -/
theorem unitCoeff0_constantCoeff_eq_one (R : Polynomial F) (M : ℕ) :
    PowerSeries.constantCoeff (R := F)
        (GMC2.DvdKMultiplicativeClosing.unitCoeff0 R M) = 1 := by
  have H := PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (phi_residue_ne_zero R M)
  have hEq : Phi R M = (smallRootFactor R M : (PowerSeries F)⟦X⟧)
      * PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M) := H.eq_mul
  have hmul := congrArg (PowerSeries.map (PowerSeries.constantCoeff (R := F))) hEq
  rw [map_mul, map_constantCoeff_Phi R M, map_constantCoeff_smallRootFactor R M] at hmul
  have hXne : (PowerSeries.X ^ M : F⟦X⟧) ≠ 0 := pow_ne_zero M PowerSeries.X_ne_zero
  have hΨh : PowerSeries.map (PowerSeries.constantCoeff (R := F))
      (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M)) = 1 :=
    (mul_left_cancel₀ hXne (by rw [mul_one]; exact hmul)).symm
  calc PowerSeries.constantCoeff (R := F) (GMC2.DvdKMultiplicativeClosing.unitCoeff0 R M)
      = PowerSeries.coeff (R := F) 0 (PowerSeries.map (PowerSeries.constantCoeff (R := F))
          (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M))) := by
        rw [GMC2.DvdKMultiplicativeClosing.unitCoeff0, PowerSeries.coeff_map,
          PowerSeries.coeff_zero_eq_constantCoeff]
    _ = 1 := by rw [hΨh]; simp

/-- **The multiplicative the small-root product identity crux, reduced to `hderiv` alone.** With
`hconst` now discharged (`unitCoeff0_constantCoeff_eq_one`), the small-root factor's constant
coefficient is `−t·r₀`, hence `Π = (−1)ᴹ P.coeff 0 = c·t`, given only the log-derivative identity
`d_t(h(0,t)) = 0` (`hderiv`). So the entire multiplicative route is kernel-pure modulo exactly
`hderiv`. -/
theorem smallRootFactor_coeff0_eq_of_derivative_vanishes' [CharZero F]
    (R : Polynomial F) (M : ℕ) (hM : 1 ≤ M)
    (hderiv : PowerSeries.derivative _ (GMC2.DvdKMultiplicativeClosing.unitCoeff0 R M) = 0) :
    (smallRootFactor R M).coeff 0
      = - PowerSeries.X * (algebraMap F (PowerSeries F)) (R.coeff 0) :=
  GMC2.DvdKMultiplicativeClosing.smallRootFactor_coeff0_eq_of_derivative_vanishes R M hM
    (unitCoeff0_constantCoeff_eq_one R M) hderiv

end GMC2.DvdKUnitOrigin

