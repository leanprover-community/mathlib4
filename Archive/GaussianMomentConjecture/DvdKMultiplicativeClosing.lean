/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKCharZeroClosing
import Archive.GaussianMomentConjecture.DvdKWeierstrass
import Mathlib

set_option linter.minImports true

/-!
# the small-root product identity closed on the Weierstrass objects, modulo the single derivative identity (exp/log-free)

This wires the **char-0 back half** (`DvdKCharZeroClosing`) onto **algebraic front
half** (`DvdKWeierstrass`) to close the multiplicative DvdK crux (the small-root product identity) on the concrete
Weierstrass factorization `Φ = P·h`, *without* exp, log, Puiseux, or a Fredholm-determinant.

`coeff_zero_smallRootFactor_mul_unit` established
`P.coeff 0 · h(0,t) = −t·r₀` (`h(0,t) := constantCoeff_x (weierstrassUnit Φ)`), so the multiplicative
crux is exactly the scalar identity `h(0,t) = 1`.  The char-0 lemma
`eq_one_of_derivative_eq_zero` turns `h(0,t) = 1` into the **exp/log-free** pair

* `hconst : (h(0,t))(t=0) = 1`  — the Weierstrass unit's value at the origin, and
* `hderiv : d_t(h(0,t)) = 0`     — the log-derivative identity under the DvdK vanishing `D_m = 0`.

Then `factorCoeff0_eq_of_unit_eq_one` gives `P.coeff 0 = −t·r₀`, hence
`Π = (−1)ᴹ P.coeff 0 = (−1)^{M+1} r₀ · t = c·t`.

So the entire multiplicative route is now kernel-pure **modulo exactly `hderiv`** — the `[X⁰]`-Laurent
log-derivative identity `d_t(h(0,t))/h(0,t) = −∑_{m≥1} D_m t^{m-1}` (root-free, frame lane) — plus the normalization `hconst`, which is a direct consequence of the distinguished
factor `P ≡ Xᴹ mod t` (so `h ≡ 1 mod t`).  No exp/log/Fredholm-det is needed to finish.
-/

open PowerSeries GMC2DvdKWeierstrass

namespace GMC2DvdKMultiplicativeClosing

variable {F : Type*} [Field F] [CharZero F]

/-- Abbreviation: `h(0,t)`, the `x`-constant term of the Weierstrass unit of `Φ = Xᴹ − t·R`,
an element of `F⟦t⟧`. -/
noncomputable def unitCoeff0 (R : Polynomial F) (M : ℕ) : PowerSeries F :=
  PowerSeries.constantCoeff (R := PowerSeries F)
    (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M))

/-- **The multiplicative DvdK crux (the small-root product identity), closed exp/log-free modulo the derivative identity.**
Given the Weierstrass unit's origin value `h(0,0) = 1` (`hconst`) and the vanishing of its
`t`-derivative `d_t(h(0,t)) = 0` (`hderiv`, the log-derivative identity under `D_m = 0`), the
small-root factor's constant coefficient is `P.coeff 0 = −t·r₀`.  Hence
`Π = (−1)ᴹ P.coeff 0 = c·t` with `c = (−1)^{M+1} r₀`.  No exp, log, Puiseux, or Fredholm determinant. -/
theorem smallRootFactor_coeff0_eq_of_derivative_vanishes
    (R : Polynomial F) (M : ℕ) (hM : 1 ≤ M)
    (hconst : PowerSeries.constantCoeff (R := F) (unitCoeff0 R M) = 1)
    (hderiv : PowerSeries.derivative _ (unitCoeff0 R M) = 0) :
    (smallRootFactor R M).coeff 0
      = - PowerSeries.X * (algebraMap F (PowerSeries F)) (R.coeff 0) :=
  GMC2DvdKCharZeroClosing.factorCoeff0_eq_of_unit_eq_one
    (GMC2DvdKCharZeroClosing.eq_one_of_derivative_eq_zero hconst hderiv)
    (coeff_zero_smallRootFactor_mul_unit R M hM)

end GMC2DvdKMultiplicativeClosing

