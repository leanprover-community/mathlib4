/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.RingTheory.LaurentSeries

/-!
# The transpose hom `φ : (PowerSeries F)⟦X⟧ → PowerSeries (LaurentSeries F)`

The sole remaining glue of the whole GMC(2)/hderiv formalization is mapping the Weierstrass factors
`P, h` of `Φ = xᴹ − t·R` (living in `F⟦t⟧⟦x⟧`) into frame `(F⸨x⸩)⟦t⟧`.  This module
builds that ring hom from scratch (no Mathlib nested-power-series curry iso exists):

* **`tau`** — the swap of nested power-series variables `F⟦t⟧⟦x⟧ → F⟦x⟧⟦t⟧`, `(τf)`'s `(t^a,x^b)`
  coefficient is `f`'s `(x^b,t^a)` coefficient. It is a ring hom; multiplicativity is the double-sum
  reorder `Finset.sum_comm` on the two convolution antidiagonals (`tau_mul`).
* **`phi := map (HahnSeries.ofPowerSeries) ∘ tauHom`** — post-composing the coefficient inclusion
  `F⟦x⟧ ↪ F⸨x⸩` lands in the frame.  `phi X = C(single 1 1)` = the frame's `x` (`phi_X`).

Because `phi` sends the `x`-power-series `h` into the `x`-support-`≥0` part of the frame with the
right `x⁰`-coefficient, it supplies exactly the `Φ = P·h` factorization and `xCoeff0(h)=unitCoeff0`
that `GMC2.DvdKHderiv.hderiv_of_frame`'s `(a)` needs.
-/

open PowerSeries

namespace GMC2.DvdKTranspose

variable {F : Type*} [Field F]

/-- The swap of nested power-series variables `τ : F⟦t⟧⟦X⟧ → F⟦X⟧⟦t⟧`:
`(τ f)`'s `(t^a, X^b)` coefficient is `f`'s `(X^b, t^a)` coefficient. -/
noncomputable def tau (f : PowerSeries (PowerSeries F)) : PowerSeries (PowerSeries F) :=
  PowerSeries.mk fun k => PowerSeries.mk fun n =>
    PowerSeries.coeff (R := F) k (PowerSeries.coeff (R := PowerSeries F) n f)

@[simp] theorem coeff_coeff_tau (f : PowerSeries (PowerSeries F)) (a b : ℕ) :
    PowerSeries.coeff (R := F) b (PowerSeries.coeff (R := PowerSeries F) a (tau f))
      = PowerSeries.coeff (R := F) a (PowerSeries.coeff (R := PowerSeries F) b f) := by
  simp [tau, PowerSeries.coeff_mk]

theorem tau_add (f g : PowerSeries (PowerSeries F)) : tau (f + g) = tau f + tau g := by
  refine PowerSeries.ext fun a => PowerSeries.ext fun b => ?_
  simp [coeff_coeff_tau]

theorem tau_one : tau (1 : PowerSeries (PowerSeries F)) = 1 := by
  refine PowerSeries.ext fun a => PowerSeries.ext fun b => ?_
  rw [coeff_coeff_tau]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [PowerSeries.coeff_one, PowerSeries.coeff_zero_eq_constantCoeff, ha, hb]

theorem tau_mul (f g : PowerSeries (PowerSeries F)) : tau (f * g) = tau f * tau g := by
  refine PowerSeries.ext fun a => PowerSeries.ext fun b => ?_
  rw [coeff_coeff_tau]
  simp only [PowerSeries.coeff_mul, map_sum, coeff_coeff_tau]
  exact Finset.sum_comm


theorem tau_zero : tau (0 : PowerSeries (PowerSeries F)) = 0 := by
  refine PowerSeries.ext fun a => PowerSeries.ext fun b => ?_
  simp [coeff_coeff_tau]

/-- The swap bundled as a ring hom. -/
noncomputable def tauHom : PowerSeries (PowerSeries F) →+* PowerSeries (PowerSeries F) where
  toFun := tau
  map_one' := tau_one
  map_mul' := tau_mul
  map_zero' := tau_zero
  map_add' := tau_add

/-- The transpose `φ : (PowerSeries F)⟦X⟧ → PowerSeries (LaurentSeries F)`. -/
noncomputable def phi : PowerSeries (PowerSeries F) →+* PowerSeries (LaurentSeries F) :=
  (PowerSeries.map (HahnSeries.ofPowerSeries ℤ F)).comp tauHom

theorem tau_X : tau (PowerSeries.X : PowerSeries (PowerSeries F))
    = PowerSeries.C (PowerSeries.X : PowerSeries F) := by
  refine PowerSeries.ext fun a => PowerSeries.ext fun b => ?_
  rw [coeff_coeff_tau]
  by_cases hb : b = 1 <;> by_cases ha : a = 0 <;>
    simp [PowerSeries.coeff_X, PowerSeries.coeff_C, PowerSeries.coeff_one, ha, hb]

theorem phi_X : phi (PowerSeries.X : PowerSeries (PowerSeries F))
    = PowerSeries.C (HahnSeries.single (1 : ℤ) (1 : F)) := by
  rw [phi, RingHom.comp_apply, show tauHom (PowerSeries.X : PowerSeries (PowerSeries F))
    = PowerSeries.C (PowerSeries.X : PowerSeries F) from tau_X, PowerSeries.map_C,
    HahnSeries.ofPowerSeries_X]

/-- `τ(C t) = t` (the inner-`t` constant becomes the outer `t`). -/
theorem tau_C_X : tau (PowerSeries.C (PowerSeries.X : PowerSeries F))
    = (PowerSeries.X : PowerSeries (PowerSeries F)) := by
  refine PowerSeries.ext fun a => PowerSeries.ext fun b => ?_
  rw [coeff_coeff_tau]
  by_cases ha : a = 1 <;> by_cases hb : b = 0 <;>
    simp [PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_one, ha, hb]

/-- `φ(C t) = t` (the frame's `t`). -/
theorem phi_C_X : phi (PowerSeries.C (PowerSeries.X : PowerSeries F))
    = (PowerSeries.X : PowerSeries (LaurentSeries F)) := by
  rw [phi, RingHom.comp_apply, show tauHom (PowerSeries.C (PowerSeries.X : PowerSeries F))
    = PowerSeries.X from tau_C_X, PowerSeries.map_X]

/-- `φ(C(C a)) = C(HahnSeries.C a)` (double constant ↦ frame constant). -/
theorem phi_C_C (a : F) :
    phi (PowerSeries.C (PowerSeries.C a : PowerSeries F))
      = PowerSeries.C (HahnSeries.C a : LaurentSeries F) := by
  have htau : tau (PowerSeries.C (PowerSeries.C a : PowerSeries F))
      = PowerSeries.C (PowerSeries.C a) := by
    refine PowerSeries.ext fun k => PowerSeries.ext fun n => ?_
    rw [coeff_coeff_tau]
    by_cases hk : k = 0 <;> by_cases hn : n = 0 <;>
      simp [PowerSeries.coeff_C, PowerSeries.coeff_zero_eq_constantCoeff, hk, hn]
  rw [phi, RingHom.comp_apply, show tauHom (PowerSeries.C (PowerSeries.C a : PowerSeries F))
    = PowerSeries.C (PowerSeries.C a) from htau, PowerSeries.map_C]
  exact congrArg PowerSeries.C (HahnSeries.ofPowerSeries_C a)

end GMC2.DvdKTranspose
