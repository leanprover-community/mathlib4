/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKFrame
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option linter.minImports true

/-!
# DvdK `hderiv`, leg (c): the coefficient-extraction `xCoeff0(logDeriv Φ)`

Builds on `DvdKFrame` (`(LaurentSeries F)⟦t⟧` frame).  This module supplies the
**extraction leg** of the `hderiv` identity: computing `logDeriv Φ` (`= −R/Φ`) in closed form and
reading off its `[x⁰]`.

The key algebra (this section, general over any `CommRing`): the geometric inverse
`(1 − w·X)⁻¹ = ∑ wⁿ Xⁿ`, which is **not in Mathlib** in this form.  Then, in the frame,
`Φ = C(xᴹ)·(1 − X·C(w))` with `w = Rl·x⁻ᴹ`, so `logDeriv Φ = −mk (n ↦ wⁿ⁺¹)`, whose `xCoeff0`
is `−mk (n ↦ (Rlⁿ⁺¹).coeff (M·(n+1)))` — the DvdK moments `D_{m}` (Check A).
-/

open PowerSeries

namespace GMC2.DvdKFrameExtraction

/-! The geometric inverse `(1 - w * X)⁻¹ = ∑ wⁿ Xⁿ` used below is
`PowerSeries.inverse_one_sub_C_mul_X`. -/


/-! ## The frame extraction leg (c): `xCoeff0(−R/Φ)` is the DvdK moment series

Using the geometric inverse, `Φ = C(xᴹ)·(1 − C(w)·X)` with `w = Rl·x⁻ᴹ`, so the honest inverse is
`Φ⁻¹ = C(x⁻ᴹ)·∑ wⁿ Xⁿ`.  Then `C(Rl)·Φ⁻¹ = ∑ wⁿ⁺¹ Xⁿ`, and applying `xCoeff0` reads off the DvdK
moments `(Rlⁿ⁺¹).coeff (M·(n+1))` — the generating-function series `∑_{m≥1} D_m tᵐ⁻¹`. This is
frame input (2) `[x⁰](−R/Φ) = −∑ D_m tᵐ⁻¹`, the piece their `xCoeff0_xM_div_PhiFrame`
was left needing. -/

section FrameExtraction

open GMC2.DvdKFrame

variable {F : Type*} [Field F]

/-- **Honest inverse of the frame `Φ` via the geometric series.** `Φ⁻¹ = C(x⁻ᴹ)·∑ wⁿ Xⁿ`, where
`w = Rl·x⁻ᴹ` (`x⁻ᴹ = HahnSeries.single (−M) 1`). Built from `Φ = C(xᴹ)·(1 − C(w)·X)` and
`PowerSeries.inverse_one_sub_C_mul_X`. -/
theorem inverse_PhiFrame (Rl : LaurentSeries F) (M : ℕ) :
    Ring.inverse (PhiFrame Rl M)
      = C (HahnSeries.single (-(M:ℤ)) 1)
        * mk (fun n => (Rl * HahnSeries.single (-(M:ℤ)) (1:F)) ^ n) := by
  have hΦ : IsUnit (PhiFrame Rl M) := isUnit_PhiFrame Rl M
  set w : LaurentSeries F := Rl * HahnSeries.single (-(M:ℤ)) 1 with hw
  have hxx : (HahnSeries.single (1:ℤ) (1:F)) ^ M * HahnSeries.single (-(M:ℤ)) 1 = 1 := by
    rw [HahnSeries.single_pow, one_pow, HahnSeries.single_mul_single, one_mul, nsmul_eq_mul,
      mul_one]
    norm_num
  have hfac : PhiFrame Rl M * C (HahnSeries.single (-(M:ℤ)) (1:F)) = 1 - C w * X := by
    have e1 : C ((HahnSeries.single (1:ℤ) (1:F)) ^ M) * C (HahnSeries.single (-(M:ℤ)) (1:F))
        = 1 := by
      rw [← map_mul, hxx, map_one]
    rw [PhiFrame, sub_mul, e1, mul_assoc, ← map_mul, ← hw]; ring
  have hprod :
      PhiFrame Rl M * (C (HahnSeries.single (-(M:ℤ)) (1:F)) * mk (fun n => w ^ n)) = 1 := by
    rw [← mul_assoc, hfac, PowerSeries.one_sub_C_mul_X_mul_mk_pow_eq_one]
  calc Ring.inverse (PhiFrame Rl M)
      = Ring.inverse (PhiFrame Rl M) *
          (PhiFrame Rl M * (C (HahnSeries.single (-(M:ℤ)) (1:F)) * mk (fun n => w ^ n))) := by
        rw [hprod, mul_one]
    _ = (Ring.inverse (PhiFrame Rl M) * PhiFrame Rl M) *
          (C (HahnSeries.single (-(M:ℤ)) (1:F)) * mk (fun n => w ^ n)) := by ring
    _ = C (HahnSeries.single (-(M:ℤ)) (1:F)) * mk (fun n => w ^ n) := by
        rw [Ring.inverse_mul_cancel _ hΦ, one_mul]

/-- **Leg (c): the DvdK moment extraction.** `xCoeff0 (C Rl · Φ⁻¹) = ∑_{n} (Rlⁿ⁺¹).coeff(M(n+1)) tⁿ`
— the generating function `(F(t)−1)/t` of the DvdK moments `D_{n+1} = (Rlⁿ⁺¹).coeff(M(n+1))`. -/
theorem xCoeff0_CRl_mul_inverse_PhiFrame (Rl : LaurentSeries F) (M : ℕ) :
    xCoeff0 (C Rl * Ring.inverse (PhiFrame Rl M))
      = mk (fun n => (Rl ^ (n + 1)).coeff ((M : ℤ) * (n + 1))) := by
  set w : LaurentSeries F := Rl * HahnSeries.single (-(M:ℤ)) 1 with hw
  -- `C Rl · Φ⁻¹ = ∑ wⁿ⁺¹ Xⁿ`
  have hstep : C Rl * Ring.inverse (PhiFrame Rl M) = mk (fun n => w ^ (n + 1)) := by
    rw [inverse_PhiFrame, ← mul_assoc, ← map_mul, ← hw]
    ext n
    rw [coeff_C_mul, coeff_mk, coeff_mk, pow_succ']
  rw [hstep]
  ext n
  rw [coeff_xCoeff0, coeff_mk, coeff_mk]
  -- `(wⁿ⁺¹).coeff 0 = (Rlⁿ⁺¹).coeff (M(n+1))`
  have hexp : (n + 1) • (-(M:ℤ)) = -(M:ℤ) * (n + 1) := by rw [nsmul_eq_mul]; push_cast; ring
  have hwpow : w ^ (n + 1) = Rl ^ (n + 1) * HahnSeries.single (-(M:ℤ) * (n + 1)) 1 := by
    rw [hw, mul_pow, HahnSeries.single_pow, one_pow, hexp]
  rw [hwpow, mul_comm (Rl ^ (n + 1)) _,
    show (0 : ℤ) = (M : ℤ) * (n + 1) + -(M:ℤ) * (n + 1) by ring,
    HahnSeries.coeff_single_mul_add, one_mul]

/-- **The frame generating function is the moment series.** Composing `xCoeff0_xM_div_PhiFrame`
(`xᴹ/Φ = 1 + t·(R/Φ)`) with leg (c), the frame `F := xCoeff0(xᴹ/Φ)` equals `∑_m (Rlᵐ).coeff(M·m) tᵐ`
— the DvdK moment generating function `∑ D_m tᵐ` (`D_0 = 1`). -/
theorem xCoeff0_xM_div_PhiFrame_eq_moments (Rl : LaurentSeries F) (M : ℕ) :
    xCoeff0 (C ((HahnSeries.single (1:ℤ) (1:F)) ^ M) * Ring.inverse (PhiFrame Rl M))
      = mk (fun m => (Rl ^ m).coeff ((M : ℤ) * m)) := by
  rw [xCoeff0_xM_div_PhiFrame, xCoeff0_CRl_mul_inverse_PhiFrame]
  ext m
  cases m with
  | zero => simp [HahnSeries.coeff_one]
  | succ k => simp [coeff_succ_X_mul]

/-- **F = 1 in the frame under DvdK vanishing (discharges `hderiv_of_frame`'s `hF1`).**  If every
positive frame moment `(Rlᵐ).coeff(M·m)` (`m ≥ 1`) vanishes, then `xCoeff0(xᴹ/Φ) = 1`. -/
theorem xCoeff0_xM_div_PhiFrame_eq_one_of_vanish (Rl : LaurentSeries F) (M : ℕ)
    (hvanish : ∀ m : ℕ, 1 ≤ m → (Rl ^ m).coeff ((M : ℤ) * m) = 0) :
    xCoeff0 (C ((HahnSeries.single (1:ℤ) (1:F)) ^ M) * Ring.inverse (PhiFrame Rl M)) = 1 := by
  rw [xCoeff0_xM_div_PhiFrame_eq_moments]
  ext m
  cases m with
  | zero => simp [HahnSeries.coeff_one]
  | succ k =>
    rw [coeff_mk, coeff_one, if_neg (Nat.succ_ne_zero k)]
    exact hvanish (k + 1) (by omega)

end FrameExtraction

end GMC2.DvdKFrameExtraction

