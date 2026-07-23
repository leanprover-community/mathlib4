/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Closing the DvdK identity in characteristic zero

Over a characteristic-zero field a power series with vanishing formal derivative is constant. This
is `PowerSeries.derivative.ext`; the wrappers here package it in the shape the DvdK argument
consumes.

## Role in GMC(2)/DvdK

This is the **char-0 back half** of the exp/log-free route to the last DvdK identity
`h(0,t) = exp(-∑ D_m tᵐ/m)`.  Viewing `Φ = Xᴹ − t·R` in `(F⟦t⟧)⟦X⟧`, the Weierstrass factorization
`Φ = P·h` () and the `[X⁰]`-Laurent log-derivative identity give
`d_t(h.coeff₀) / h.coeff₀ = -∑_{m≥1} D_m t^{m-1}` in `F⟦t⟧`.  Under the DvdK vanishing hypothesis
`D_m = 0 ∀ m ≥ 1` (`generatingFunction_eq_one` supplies `F(t)=1`), the right side is `0`, so
`d_t(h.coeff₀) = 0`.  `eq_one_of_derivative_eq_zero` then turns this — with `h.coeff₀(0) = 1` — into
`h.coeff₀ = 1` **without any exp/log or Puiseux**, purely by "zero derivative ⟹ constant in char 0".
`factorCoeff0_eq_of_unit_eq_one` performs the final trivial substitution
`P.coeff 0 = [X⁰]Φ = -(t·r₀)`, giving `Π = (-1)ᴹ P.coeff 0 = c·t`.

The module is frame-agnostic: it consumes the log-derivative output (`derivative g = 0`) as a
hypothesis, so it composes with the `[X⁰]`-Laurent frame and touches no Weierstrass internals.
-/

open PowerSeries

namespace GMC2.DvdKCharZeroClosing

variable {F : Type*} [Field F] [CharZero F]

/-- Over a characteristic-zero field, a power series with vanishing formal derivative equals the
constant series at its constant term. -/
theorem eq_C_of_derivative_eq_zero {f : PowerSeries F} (hf : derivative _ f = 0) :
    f = C (constantCoeff f) :=
  derivative.ext (by rw [hf, derivative_C]) (by rw [constantCoeff_C])

/-- **Assembly wrapper (exp/log-free DvdK closing).**  The constant-in-`X` coefficient
`g = h.coeff₀ : F⟦t⟧` of the Weierstrass unit: if its `t`-derivative vanishes (the log-derivative
identity under `D_m = 0`) and its value at `t = 0` is `1`, then `g = 1` — no exp/log, no Puiseux. -/
theorem eq_one_of_derivative_eq_zero {g : PowerSeries F}
    (hg0 : constantCoeff g = 1) (hderiv : derivative _ g = 0) : g = 1 := by
  rw [eq_C_of_derivative_eq_zero hderiv, hg0, map_one]

omit [CharZero F] in
/-- **Final closing step both DvdK routes consume.**  With the Weierstrass unit's constant-in-`X`
coefficient collapsed to `1`, the small-root factor's constant-in-`X` coefficient `P₀` equals the
`[X⁰]` of `Φ = Xᴹ − t·R`.  Stated frame-agnostically: from `P₀ · g = rhs` and `g = 1`, get
`P₀ = rhs`.  (With `rhs = -(t·r₀)` this is `P.coeff 0 = -(t·r₀)`, hence `Π = (-1)ᴹ P₀ = c·t`.) -/
theorem factorCoeff0_eq_of_unit_eq_one {P₀ g rhs : PowerSeries F}
    (hg : g = 1) (hfact : P₀ * g = rhs) : P₀ = rhs := by
  rwa [hg, mul_one] at hfact

end GMC2.DvdKCharZeroClosing

