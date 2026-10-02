/-
Copyright (c) 2026 Seiichi Manyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seiichi Manyama
-/
module

import Mathlib.RingTheory.PowerSeries.LagrangeInversion
import Mathlib.Data.ZMod.Basic

/-! # Tests for Lagrange inversion over arbitrary commutative rings -/

open PowerSeries

section CommRing

variable {R : Type*} [CommRing R] {P Y : R⟦X⟧}
variable (hY : Y = X * P.subst Y)

example (H : R⟦X⟧) : coeff 1 (H.subst Y) = (d⁄dX H * P).coeff 0 := by
  simpa using lagrange_burmann_coeff hY 0 H

example (n : ℕ) : n • (Y ^ 0).coeff n = 0 := by
  simpa using lagrange_inversion_coeff_pow hY n 0

end CommRing

-- Natural-number multiplication is not injective in these coefficient rings.
example {P Y : PowerSeries (ZMod 2)} (hY : Y = X * P.subst Y)
    (n : ℕ) (H : PowerSeries (ZMod 2)) :
    (n + 1) • coeff (n + 1) (H.subst Y) = (d⁄dX H * P ^ (n + 1)).coeff n :=
  lagrange_burmann_coeff hY n H

example {P Y : PowerSeries (ZMod 6)} (hY : Y = X * P.subst Y) (n k : ℕ) :
    (n + k) • (Y ^ k).coeff (n + k) = k • (P ^ (n + k)).coeff n :=
  lagrange_inversion_coeff_pow hY n k

example {P Y : PowerSeries ℚ} (hY : Y = X * P.subst Y) (n : ℕ) (H : PowerSeries ℚ) :
    coeff (n + 1) (H.subst Y) = (d⁄dX H * P ^ (n + 1)).coeff n / (n + 1) :=
  lagrange_burmann_coeff_div hY n H

example {P Y : PowerSeries ℚ} (hY : Y = X * P.subst Y) (n : ℕ) :
    Y.coeff (n + 1) = (P ^ (n + 1)).coeff n / (n + 1) :=
  lagrange_inversion_coeff hY n
