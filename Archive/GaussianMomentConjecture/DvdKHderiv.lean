/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKFrame
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.LogDeriv

/-!
# The `hderiv` assembly in the frame: reduced to the degree lemma (c) + the h-side (a)

Building on `DvdKFrame`, this closes the DvdK log-derivative lemma `hderiv` (`d_t(h(0,t)) = 0`
under `D_m = 0`) up to two frame-local inputs.  The whole thing rests on:

* **`master_identity`** (pure frame algebra, NO hypotheses): `t · xCoeff0(logDeriv Φ) = 1 − F`,
  where `F := xCoeff0(x^M/Φ)` is the DvdK generating function. Proof: `d_t Φ = −R`, so
  `logDeriv Φ = −R/Φ`, and `x^M = Φ + t·R` gives `t·xCoeff0(−R/Φ) = 1 − F`
  (`xCoeff0_xM_div_PhiFrame`).
* **`hderiv_of_frame`**: with `Φ = P·h` (units), `xCoeff0(logDeriv P) = 0` (the degree lemma (c)),
  `xCoeff0(logDeriv h) = g'/g` for `g := xCoeff0 h` a unit (the h-side (a)), and `F = 1` (the DvdK
  vanishing, `generatingFunction_eq_one`), the master identity forces `t·g' = 0`, hence
  `g' = 0` (`t` a non-zero-divisor) — i.e. `hderiv` (with `g = xCoeff0 h = unitCoeff0`).

So `hderiv` is now reduced to exactly: the frame factorization `Φ = P·h`, the degree lemma (c), and
the h-side (a) — all frame-local, no residues/Puiseux/valued fields.
-/

open PowerSeries GMC2.DvdKFrame

namespace GMC2.DvdKHderiv

variable {F : Type*} [Field F]

/-- `d_t(X) = 1` in the frame. -/
theorem derivative_X_eq_one :
    PowerSeries.derivative _ (PowerSeries.X : PowerSeries (LaurentSeries F)) = 1 := by
  ext n
  rw [PowerSeries.coeff_derivative]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [PowerSeries.coeff_X, if_neg (by omega), PowerSeries.coeff_one, if_neg (by omega)]; simp

/-- `d_t Φ = −R` in the frame (`Φ = x^M − t·R`, with `x^M`, `R` constant in `t`). -/
theorem derivative_PhiFrame (Rl : LaurentSeries F) (M : ℕ) :
    PowerSeries.derivative _ (PhiFrame Rl M) = - PowerSeries.C Rl := by
  show (PowerSeries.derivative (LaurentSeries F)) (PhiFrame Rl M) = - PowerSeries.C Rl
  rw [PhiFrame, map_sub, PowerSeries.derivative_C, zero_sub, Derivation.leibniz,
    PowerSeries.derivative_C, PowerSeries.derivative_X, smul_zero, zero_add, smul_eq_mul, mul_one]

/-- **The master identity** (pure frame algebra, no hypotheses):
`t · xCoeff0(logDeriv Φ) = 1 − F`, `F := xCoeff0(x^M/Φ)`. -/
theorem master_identity (Rl : LaurentSeries F) (M : ℕ) :
    PowerSeries.X * xCoeff0 (PowerSeries.logDeriv (PhiFrame Rl M))
      = 1 - xCoeff0 (PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : F)) ^ M)
          * Ring.inverse (PhiFrame Rl M)) := by
  have hb := xCoeff0_xM_div_PhiFrame Rl M
  have hld : PowerSeries.logDeriv (PhiFrame Rl M)
      = - PowerSeries.C Rl * Ring.inverse (PhiFrame Rl M) := by
    rw [PowerSeries.logDeriv, derivative_PhiFrame]
  rw [hld, neg_mul, map_neg, mul_neg, hb]
  ring

/-- **The `hderiv` assembly, modulo (a), (c), and the frame factorization.**  Given `Φ = P·h`
(units), the degree lemma (c) `xCoeff0(logDeriv P) = 0`, the h-side (a)
`xCoeff0(logDeriv h) = g'/g` with `g := xCoeff0 h` a unit, and `F = 1`, we get `derivative g = 0`
— i.e. `hderiv` (`g = xCoeff0 h = unitCoeff0`). -/
theorem hderiv_of_frame (Rl : LaurentSeries F) (M : ℕ)
    (Pfr hfr : PowerSeries (LaurentSeries F))
    (hfact : PhiFrame Rl M = Pfr * hfr) (hPu : IsUnit Pfr) (hhu : IsUnit hfr)
    (hc : xCoeff0 (PowerSeries.logDeriv Pfr) = 0)
    (ha : xCoeff0 (PowerSeries.logDeriv hfr)
        = PowerSeries.derivative _ (xCoeff0 hfr) * Ring.inverse (xCoeff0 hfr))
    (hg : IsUnit (xCoeff0 hfr))
    (hF1 : xCoeff0 (PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : F)) ^ M)
        * Ring.inverse (PhiFrame Rl M)) = 1) :
    PowerSeries.derivative _ (xCoeff0 hfr) = 0 := by
  have hstar : xCoeff0 (PowerSeries.logDeriv (PhiFrame Rl M))
      = PowerSeries.derivative _ (xCoeff0 hfr) * Ring.inverse (xCoeff0 hfr) := by
    rw [hfact, xCoeff0_logDeriv_mul hPu hhu, hc, ha, zero_add]
  have hmaster := master_identity Rl M
  rw [hstar, hF1, sub_self] at hmaster
  have hg1 : PowerSeries.X * (PowerSeries.derivative _ (xCoeff0 hfr)
      * Ring.inverse (xCoeff0 hfr)) * (xCoeff0 hfr) = 0 := by rw [hmaster]; ring
  rw [mul_assoc, mul_assoc, Ring.inverse_mul_cancel _ hg, mul_one] at hg1
  exact (mul_eq_zero.mp hg1).resolve_left PowerSeries.X_ne_zero

end GMC2.DvdKHderiv

