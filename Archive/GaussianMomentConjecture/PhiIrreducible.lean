/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib

set_option linter.minImports true

/-!
# Irreducibility of `Φ = X^M − t·R(X)` over `F(t)` — the transitivity input to the orbit-product argument

For `R ∈ F[X]` with `R(0) ≠ 0`, the polynomial `Φ = X^M − t·R(X)` is irreducible over `F(t)`, so its
Galois group acts transitively on its roots (`Polynomial.Gal.galAction_isPretransitive`) — the input
consumed by the orbit-product core (`OrbitProduct`).

Strategy (Gauss): `Φ` is *linear* in `t` over `F[X]`, with coprime coefficients `X^M` and `−R`
(coprime because `X ∤ R`, i.e. `R(0) ≠ 0`), hence irreducible in `F[X][t]`.  This module proves that
first step (`phi_t_irreducible`); the transport across the `F[X][t] ≅ F[t][X]` swap and Gauss to
`F(t)[X]` is the remaining step.
-/

open Polynomial

namespace GMC2PhiIrreducible

variable {F : Type*} [Field F]

/-- `X^M` and `R` are relatively prime in `F[X]` when `R(0) ≠ 0` (so `X ∤ R`). -/
theorem isRelPrime_X_pow_R (R : F[X]) (M : ℕ) (hR0 : R.coeff 0 ≠ 0) :
    IsRelPrime ((X : F[X]) ^ M) R := by
  have hXR : IsCoprime (X : F[X]) R :=
    (prime_X.coprime_iff_not_dvd).mpr (by rw [Polynomial.X_dvd_iff]; exact hR0)
  exact (hXR.pow_left).isRelPrime

/-- **`Φ` is irreducible as a linear polynomial in `t` over `F[X]`.**  Here the outer variable `X` of
`F[X][t]` plays the role of `t`; `Φ = C(Xᴹ) − C(R)·t`. -/
theorem phi_t_irreducible (R : F[X]) (M : ℕ) (hR0 : R.coeff 0 ≠ 0) :
    Irreducible
      (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X : Polynomial (Polynomial F)) := by
  have hRne : R ≠ 0 := fun h => hR0 (by rw [h]; simp)
  have hrw : (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X : Polynomial (Polynomial F))
      = Polynomial.C (-R) * X + Polynomial.C ((X : F[X]) ^ M) := by
    simp only [map_neg]; ring
  rw [hrw]
  apply Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff
  · -- degree of the linear form `C(-R)·X + C(Xᴹ)` is 1
    rw [Polynomial.degree_linear (neg_ne_zero.mpr hRne)]
  · -- coeff 0 = Xᴹ, coeff 1 = −R, and these are relatively prime
    have hc0 : (Polynomial.C (-R) * X + Polynomial.C ((X : F[X]) ^ M) :
        Polynomial (Polynomial F)).coeff 0 = (X : F[X]) ^ M := by
      rw [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_zero, mul_zero, zero_add]
    have hc1 : (Polynomial.C (-R) * X + Polynomial.C ((X : F[X]) ^ M) :
        Polynomial (Polynomial F)).coeff 1 = -R := by
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one,
        Polynomial.coeff_C, if_neg (by norm_num : ¬ ((1 : ℕ) = 0)), add_zero]
    rw [hc0, hc1]
    exact (isRelPrime_X_pow_R R M hR0).neg_right

/-- The swapped polynomial `swap Φ = map C (Xᴹ) − map C R · C X` in `F[X][Y]`, now with the outer
variable `Y` playing the role of the DvdK variable and the inner `F[X]` playing `F[t]` (`t = X`). -/
theorem swap_phi_eq (R : F[X]) (M : ℕ) :
    Polynomial.Bivariate.swap
        (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X : Polynomial (Polynomial F))
      = Polynomial.map Polynomial.C ((X : F[X]) ^ M)
        - Polynomial.map Polynomial.C R * Polynomial.C X := by
  rw [map_sub, map_mul, Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_C,
    Polynomial.Bivariate.swap_Y]

/-- **`Φ = X^M − t·R(X)` is irreducible over `F(t)`.**  Gauss: `swap Φ` is primitive over `F[t]` (its
`Yᴹ`-coefficient `1 − C(r_M)·t` and `Y⁰`-coefficient `−C(r₀)·t` are coprime, since `r₀ ≠ 0` and `t`
is coprime to `1 − C(r_M)·t`), and irreducible (transported from `phi_t_irreducible`); so its image
over `F(t)` is irreducible.  This is the transitivity input to `Polynomial.Gal.galAction_isPretransitive`. -/
theorem phi_irreducible_ratfunc (R : F[X]) (M : ℕ) (hM : 1 ≤ M) (hR0 : R.coeff 0 ≠ 0) :
    Irreducible (Polynomial.map (algebraMap (Polynomial F) (RatFunc F))
      (Polynomial.Bivariate.swap
        (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X : Polynomial (Polynomial F)))) := by
  have hirr_swap : Irreducible (Polynomial.Bivariate.swap
      (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X : Polynomial (Polynomial F))) :=
    (MulEquiv.irreducible_iff
        (Polynomial.Bivariate.swap (R := F)).toRingEquiv.toMulEquiv).mpr
      (phi_t_irreducible R M hR0)
  -- coefficients of `swap Φ` (in `F[X]`, the base ring of Gauss)
  have cM : (Polynomial.Bivariate.swap
      (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X : Polynomial (Polynomial F))).coeff M
      = 1 - Polynomial.C (R.coeff M) * X := by
    rw [swap_phi_eq, Polynomial.coeff_sub, Polynomial.coeff_mul_C, Polynomial.coeff_map,
      Polynomial.coeff_map, Polynomial.coeff_X_pow, if_pos rfl, map_one]
  have c0 : (Polynomial.Bivariate.swap
      (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X : Polynomial (Polynomial F))).coeff 0
      = - (Polynomial.C (R.coeff 0) * X) := by
    rw [swap_phi_eq, Polynomial.coeff_sub, Polynomial.coeff_mul_C, Polynomial.coeff_map,
      Polynomial.coeff_map, Polynomial.coeff_X_pow, if_neg (by omega : ¬ ((0 : ℕ) = M)), map_zero,
      zero_sub]
  -- primitivity
  have hprim : (Polynomial.Bivariate.swap
      (Polynomial.C ((X : F[X]) ^ M) - Polynomial.C R * X : Polynomial (Polynomial F))).IsPrimitive := by
    intro r hr
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
    have hrM : r ∣ (1 - Polynomial.C (R.coeff M) * X) := cM ▸ hr M
    have hr0 : r ∣ (Polynomial.C (R.coeff 0) * X) := by
      have := hr 0; rw [c0] at this; exact (dvd_neg).mp this
    -- r₀ is a unit, so r ∣ X
    have hunit : IsUnit (Polynomial.C (R.coeff 0)) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hR0)
    have hrX : r ∣ (X : F[X]) := (hunit.dvd_mul_left).mp hr0
    -- r ∣ X and r ∣ (1 - C r_M X) ⟹ r ∣ 1
    have hr1 : r ∣ (1 : F[X]) := by
      have hb : r ∣ Polynomial.C (R.coeff M) * X := hrX.mul_left _
      have := dvd_add hrM hb
      simpa using this
    exact isUnit_of_dvd_one hr1
  exact (hprim.irreducible_iff_irreducible_map_fraction_map).mp hirr_swap

end GMC2PhiIrreducible

