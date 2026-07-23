/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKWeierstrass
import Mathlib

set_option linter.minImports true

/-!
# The bridge divisibility: the Weierstrass distinguished factor divides `Φ` in the polynomial ring

The frame bridge needs `smallRootFactor R M ∣ Φ` as **polynomials** over `PowerSeries F` (so that,
mapped to the algebraic closure of `LaurentSeries F`, the small-root packet is a sub-multiset of `Φ`'s
roots).  This is *not* the trivial power-series divisibility over the fraction field (where the
distinguished factor becomes a unit); it is the genuine polynomial factorization, obtained from
Mathlib's Weierstrass **division uniqueness** (`IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`) applied
to the two divisions of `Φ` by the monic `smallRootFactor`: the Weierstrass factorization
`Φ = ↑P·h` (remainder `0`) and the ordinary polynomial division (remainder `Φ %ₘ P`).  Uniqueness forces
`Φ %ₘ P = 0`.  No valuation on the algebraic closure.
-/

open Polynomial

namespace GMC2FrameBridgeDvd

variable {F : Type*} [Field F]

/-- The polynomial (over `PowerSeries F`) whose coercion into `(PowerSeries F)⟦X⟧` is Weierstrass `Φ = xᴹ − t·R`. -/
noncomputable def PhiPoly (R : Polynomial F) (M : ℕ) : (PowerSeries F)[X] :=
  X ^ M - C (PowerSeries.X) * R.map (algebraMap F (PowerSeries F))

/-- The coercion of `PhiPoly` is the Weierstrass power series `Φ`. -/
theorem coe_PhiPoly (R : Polynomial F) (M : ℕ) :
    ((PhiPoly R M : Polynomial (PowerSeries F)) : PowerSeries (PowerSeries F))
      = GMC2DvdKWeierstrass.Phi R M := by
  rw [PhiPoly, GMC2DvdKWeierstrass.Phi]
  push_cast
  ring

/-- **The bridge divisibility.**  The Weierstrass distinguished factor `smallRootFactor R M` divides
`Φ = PhiPoly R M` in the *polynomial* ring `(PowerSeries F)[X]`.  Proof: the Weierstrass factorization
`↑Φ = ↑P·h` and the ordinary monic division `Φ = P·(Φ/ₘP) + (Φ%ₘP)` are two Weierstrass divisions of
`↑Φ` by `↑P`; uniqueness (`IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`, `F[[t]]` Hausdorff) forces
`Φ %ₘ P = 0`. -/
theorem smallRootFactor_dvd_PhiPoly (R : Polynomial F) (M : ℕ) :
    GMC2DvdKWeierstrass.smallRootFactor R M ∣ PhiPoly R M := by
  set P := GMC2DvdKWeierstrass.smallRootFactor R M with hPdef
  have hPmonic : P.Monic := GMC2DvdKWeierstrass.smallRootFactor_monic R M
  have hPnat : P.natDegree = M := GMC2DvdKWeierstrass.smallRootFactor_natDegree R M
  have hPdist : P.IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries F)) :=
    PowerSeries.isDistinguishedAt_weierstrassDistinguished
      (GMC2DvdKWeierstrass.phi_residue_ne_zero R M)
  have H : PowerSeries.IsWeierstrassDivisorAt (↑P : PowerSeries (PowerSeries F))
      (IsLocalRing.maximalIdeal (PowerSeries F)) := hPdist.isWeierstrassDivisorAt'
  obtain ⟨h, -, hfact⟩ := GMC2DvdKWeierstrass.phi_eq_smallRootFactor_mul R M
  rw [← coe_PhiPoly] at hfact
  -- the order of `↑P` reduced mod the maximal ideal is `M`
  have hord : ((↑P : PowerSeries (PowerSeries F)).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries F)))).order.toNat = M := by
    rw [← Polynomial.polynomial_map_coe, hPdist.map_eq_X_pow, hPnat, Polynomial.coe_pow, Polynomial.coe_X,
      PowerSeries.order_X_pow, ENat.toNat_coe]
  -- degree conditions
  have hr0 : (0 : Polynomial (PowerSeries F)).degree
      < ((↑P : PowerSeries (PowerSeries F)).map
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries F)))).order.toNat := by
    rw [hord, Polynomial.degree_zero]; exact WithBot.bot_lt_coe M
  have hr1 : (PhiPoly R M %ₘ P).degree
      < ((↑P : PowerSeries (PowerSeries F)).map
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries F)))).order.toNat := by
    rw [hord]
    have hPdeg : P.degree = (M : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hPmonic.ne_zero, hPnat]
    rw [← hPdeg]; exact Polynomial.degree_modByMonic_lt _ hPmonic
  -- the two divisions agree; uniqueness forces the remainder to vanish
  have hheq : (↑P : PowerSeries (PowerSeries F)) * h + ↑(0 : Polynomial (PowerSeries F))
      = ↑P * ↑(PhiPoly R M /ₘ P) + ↑(PhiPoly R M %ₘ P) := by
    rw [Polynomial.coe_zero, add_zero, ← hfact]
    conv_lhs => rw [← Polynomial.modByMonic_add_div (PhiPoly R M) P]
    push_cast; ring
  have huniq := H.eq_of_mul_add_eq_mul_add hr0 hr1 hheq
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hPmonic).mp huniq.2.symm

end GMC2FrameBridgeDvd

