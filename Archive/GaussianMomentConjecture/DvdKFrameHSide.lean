/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKFrame
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.PowerSeries.LogDeriv

set_option linter.minImports true

/-!
# The `hderiv` h-side (a): `[x⁰](h_t/h) = g_t/g` on the disk

The last-but-one open input to `hderiv`, discharged via one structural idea (reflection
the disk/annulus split):

**`xCoeff0` is a ring homomorphism on the disk subring `F⟦x⟧⟦t⟧`** (the constant-`x` term of a
product of *power* series is the product of constant terms — false for Laurent series, verified:
`1 + t(x+x⁻¹)` breaks it). The Weierstrass unit `h` is a genuine power series in `x`, so it lives on
the disk, and the h-side is just **`logDeriv` commuting with a ring homomorphism**.

* `PowerSeries.map_logDeriv` (general, reusable — Mathlib gap):
  `map ψ (logDeriv u) = logDeriv (map ψ u)` for any ring hom `ψ` and unit `u`, from `map_derivative`
  + ring homs preserving unit inverses.
* `xCoeff0_map_ofPowerSeries`: `[x⁰] ∘ ofPowerSeries = constantCoeff`, i.e. on the disk `xCoeff0` is
  the ring hom `map constantCoeff`.
* `xCoeff0_logDeriv_map_ofPowerSeries` = `hderiv_of_frame` hypothesis `ha`, for
  `hfr = map ofPowerSeries H` (the form the transpose delivers).
-/

open PowerSeries

namespace GMC2.DvdKFrameHSide

/-! The general facts that `PowerSeries.map` commutes with the formal derivative and with
`logDeriv` on units are `PowerSeries.map_derivative` and `PowerSeries.map_logDeriv`. -/


/-! ## Disk specialization: `xCoeff0` on `F⟦x⟧⟦t⟧` is the ring hom `map constantCoeff`

On the **disk subring** `F⟦x⟧⟦t⟧ ↪ F⸨x⸩⟦t⟧` (image of `map (ofPowerSeries ℤ F)`), `xCoeff0` is the
ring homomorphism `map constantCoeff` — because `[x⁰]` is multiplicative on *power* series (false on
Laurent series, e.g. `1 + t(x+x⁻¹)`). The Weierstrass unit lands here, so the h-side is
`PowerSeries.map_logDeriv` twice. -/

section Disk

variable {F : Type*} [Field F]

/-- **`[x⁰]` on the disk subring is `constantCoeff`.** -/
theorem xCoeff0_map_ofPowerSeries (H : PowerSeries (PowerSeries F)) :
    GMC2.DvdKFrame.xCoeff0 (PowerSeries.map (HahnSeries.ofPowerSeries ℤ F) H)
      = PowerSeries.map (PowerSeries.constantCoeff (R := F)) H := by
  ext k
  rw [GMC2.DvdKFrame.coeff_xCoeff0, coeff_map, coeff_map]
  simpa using HahnSeries.ofPowerSeries_apply_coeff (PowerSeries.coeff k H) 0

/-- **The h-side (a), on the disk.** For a unit `H : F⟦x⟧⟦t⟧`, with `hfr = map ofPowerSeries H` (the
form the transpose delivers), `xCoeff0(logDeriv hfr) = g_t · g⁻¹` with `g = xCoeff0 hfr`. Exactly
`GMC2.DvdKHderiv.hderiv_of_frame`'s hypothesis `ha`. -/
theorem xCoeff0_logDeriv_map_ofPowerSeries {H : PowerSeries (PowerSeries F)} (hH : IsUnit H) :
    GMC2.DvdKFrame.xCoeff0 (PowerSeries.logDeriv (PowerSeries.map (HahnSeries.ofPowerSeries ℤ F) H))
      = derivative _ (GMC2.DvdKFrame.xCoeff0 (PowerSeries.map (HahnSeries.ofPowerSeries ℤ F) H))
        * Ring.inverse
            (GMC2.DvdKFrame.xCoeff0 (PowerSeries.map (HahnSeries.ofPowerSeries ℤ F) H)) := by
  simp only [xCoeff0_map_ofPowerSeries]
  rw [← PowerSeries.map_logDeriv (HahnSeries.ofPowerSeries ℤ F) hH, xCoeff0_map_ofPowerSeries,
    PowerSeries.map_logDeriv (PowerSeries.constantCoeff (R := F)) hH, PowerSeries.logDeriv]

end Disk

end GMC2.DvdKFrameHSide

