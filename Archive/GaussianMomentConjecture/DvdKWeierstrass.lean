/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib

set_option linter.minImports true

/-!
# Obstacle (ii) of the small-root product identity via Mathlib's Weierstrass preparation

The last gap in the GMC(2)/DvdK proof (the orbit-product argument route) is the small-root product identity, whose obstacle (ii)
 is the construction of the **small-root factor** of
`Φ = x^M − t·R(x)` — the degree-`M` distinguished polynomial `P` (`P ≡ x^M mod t`) with
`Φ = P · h`, `h` a unit.  This was originally estimated as manual monic-M-th-root Hensel + a
`(t)`-adic fixed-point iteration ("the next substantial piece", months-scale).

**This file shows Mathlib already has it.**  View `Φ` as a power series in `x` over the
complete local ring `A = F[[t]]`; its residue image is `x^M ≠ 0`, so
`PowerSeries.exists_isWeierstrassFactorization` produces exactly the distinguished factor `P`
and the unit `h`.  The only missing instance — `IsAdicComplete (maximalIdeal A) A` — is
assembled from `PowerSeries.maximalIdeal_eq_span_X` plus the `(X)`-adic completeness instance
Mathlib already provides (the same instance used for obstacle (i)).

So obstacle (ii) is **not** months of manual Hensel; it is a direct Mathlib appeal, kernel-pure.

Conventions: `A = PowerSeries F = F[[t]]` (inner variable `t = PowerSeries.X`); `Φ ∈ A⟦X⟧`
is a power series in `x = X` (outer).  `Φ = x^M − t·R(x)` with `R : F[X]` embedded as
`R.map (algebraMap F A)`.
-/

open PowerSeries

namespace GMC2DvdKWeierstrass

noncomputable section

variable {F : Type*} [Field F]

/-- The instance that unlocks Weierstrass preparation over `F[[t]]`: `F[[t]]` is complete for
its maximal ideal, because that ideal is `(X)` and `F[[t]]` is `(X)`-adically complete. -/
instance : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries F)) (PowerSeries F) := by
  rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance

/-- `Φ = x^M − t·R(x)` as a power series in `x = X` over `A = F[[t]]`. -/
def Phi (R : Polynomial F) (M : ℕ) : (PowerSeries F)⟦X⟧ :=
  (PowerSeries.X) ^ M
    - (PowerSeries.C (PowerSeries.X : PowerSeries F))
        * ((R.map (algebraMap F (PowerSeries F))) : (PowerSeries F)⟦X⟧)

/-- The residue image of `Φ` (mod `t`) is `x^M`: the `−t·R` term dies because `residue t = 0`. -/
theorem map_residue_Phi (R : Polynomial F) (M : ℕ) :
    PowerSeries.map (IsLocalRing.residue (PowerSeries F)) (Phi R M) = PowerSeries.X ^ M := by
  have hX : IsLocalRing.residue (PowerSeries F) (PowerSeries.X) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl
  rw [Phi, map_sub, map_pow, PowerSeries.map_X, map_mul, PowerSeries.map_C, hX, map_zero,
    zero_mul, sub_zero]

/-- The residue image of `Φ` is nonzero (`= x^M`), the hypothesis for Weierstrass preparation. -/
theorem phi_residue_ne_zero (R : Polynomial F) (M : ℕ) :
    PowerSeries.map (IsLocalRing.residue (PowerSeries F)) (Phi R M) ≠ 0 := by
  rw [map_residue_Phi]; exact pow_ne_zero M PowerSeries.X_ne_zero

/-- **Obstacle (ii), kernel-pure.**  `Φ = x^M − t·R(x)` admits a Weierstrass factorization:
`Φ = P · h` where `P` is a distinguished polynomial (monic, `≡ x^M mod t`) and `h` is a unit
power series.  `P` is the small-root factor; `Π = (−1)^M · P.coeff 0` is the small-root product.
Obtained directly from Mathlib's Weierstrass preparation theorem. -/
theorem phi_weierstrass (R : Polynomial F) (M : ℕ) :
    ∃ f h, (Phi R M).IsWeierstrassFactorization f h :=
  PowerSeries.exists_isWeierstrassFactorization (phi_residue_ne_zero R M)

/-- The **small-root factor** `P` of `Φ`: the distinguished polynomial in its Weierstrass
factorization.  Monic, `P ≡ x^M mod t`, and `Φ = P · (unit)`. -/
def smallRootFactor (R : Polynomial F) (M : ℕ) : Polynomial (PowerSeries F) :=
  PowerSeries.weierstrassDistinguished (Phi R M) (phi_residue_ne_zero R M)

/-- `P` has degree **exactly `M`** — there are exactly `M` small roots, so
`Π = (−1)^M · P.coeff 0` has `t`-valuation `1`. -/
theorem smallRootFactor_natDegree (R : Polynomial F) (M : ℕ) :
    (smallRootFactor R M).natDegree = M := by
  have H := PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (phi_residue_ne_zero R M)
  rw [smallRootFactor, H.natDegree_eq_toNat_order_map, map_residue_Phi, PowerSeries.order_X_pow,
    ENat.toNat_coe]

/-- `P` is monic. -/
theorem smallRootFactor_monic (R : Polynomial F) (M : ℕ) : (smallRootFactor R M).Monic :=
  (PowerSeries.isDistinguishedAt_weierstrassDistinguished (phi_residue_ne_zero R M)).monic

/-- `Φ = P · h` with `h` a unit: the small-root factor divides `Φ`. -/
theorem phi_eq_smallRootFactor_mul (R : Polynomial F) (M : ℕ) :
    ∃ h, IsUnit h ∧ Phi R M = (smallRootFactor R M : (PowerSeries F)⟦X⟧) * h := by
  have H := PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (phi_residue_ne_zero R M)
  exact ⟨_, H.isUnit, H.eq_mul⟩

/-- The `x`-constant term of `Φ` is `−t·r₀` (`r₀ = R.coeff 0`, the lowest coefficient). -/
theorem constantCoeff_Phi (R : Polynomial F) (M : ℕ) (hM : 1 ≤ M) :
    PowerSeries.constantCoeff (R := PowerSeries F) (Phi R M)
      = - PowerSeries.X * (algebraMap F (PowerSeries F)) (R.coeff 0) := by
  have hcR : PowerSeries.constantCoeff (R := PowerSeries F)
      ((R.map (algebraMap F (PowerSeries F))) : (PowerSeries F)⟦X⟧)
      = (algebraMap F (PowerSeries F)) (R.coeff 0) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, Polynomial.coeff_map]
  rw [Phi, map_sub, map_pow, map_mul, PowerSeries.constantCoeff_X,
    zero_pow (by omega : M ≠ 0), PowerSeries.constantCoeff_C, hcR]
  ring

/-- **The multiplicative the small-root product identity crux reduces to a single scalar identity.**
From `Φ = P·h` (Weierstrass), taking the `x`-constant term gives
`P.coeff 0 · h(0) = −t·r₀`, where `h(0) := constantCoeff h` is a unit of `F[[t]]` (`= 1 mod t`).
Hence the small-root product `Π = (−1)^M·P.coeff 0` satisfies `Π · h(0) = c·t` with
`c = (−1)^{M+1} r₀`, so **`Π = c·t ⟺ h(0,t) = 1`**.  This isolates the sole remaining analytic
input as exactly `h(0,t) = 1` under `D_m = 0` (equivalently `h(0,t) = exp(−∑ D_m tᵐ/m)`). -/
theorem coeff_zero_smallRootFactor_mul_unit (R : Polynomial F) (M : ℕ) (hM : 1 ≤ M) :
    (smallRootFactor R M).coeff 0
      * PowerSeries.constantCoeff (R := PowerSeries F)
          (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M))
      = - PowerSeries.X * (algebraMap F (PowerSeries F)) (R.coeff 0) := by
  have H := PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (phi_residue_ne_zero R M)
  have key := congrArg (PowerSeries.constantCoeff (R := PowerSeries F)) H.eq_mul
  rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_Phi R M hM] at key
  exact key.symm

end


end GMC2DvdKWeierstrass
