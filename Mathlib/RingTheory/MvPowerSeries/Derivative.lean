/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Formal partial derivatives of multivariate power series

This file defines `MvPowerSeries.pderiv R i`, the formal partial derivative of a multivariate
power series with respect to variable `i`, as a
`Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R)`.

See also `PowerSeries.derivative` for the univariate setting.

## Main definitions

- `MvPowerSeries.pderiv R i`: the formal partial derivative with respect to `i`, as a derivation.

## Main results

- `MvPowerSeries.coeff_pderiv`: coefficient formula
  `coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1)`.
- `MvPowerSeries.pderiv_coe`: compatibility with `MvPolynomial.pderiv`.
- `MvPowerSeries.trunc_pderiv`: truncation commutes with partial differentiation.
- `MvPowerSeries.pderiv.ext`: a power series is determined by its constant term and its partial
  derivatives.
- `MvPowerSeries.pderiv_pow`: power rule.
- `MvPowerSeries.pderiv_inv`, `MvPowerSeries.pderiv_inv'`: derivative of an inverse.

-/

@[expose] public section

namespace MvPowerSeries

open MvPolynomial Finsupp

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/-- The underlying function of the formal partial derivative with respect to variable `i`.
This is packaged as a derivation in `MvPowerSeries.pderiv`. -/
noncomputable def pderivFun (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ coeff (d + single i 1) f * (d i + 1)

theorem coeff_pderivFun {i : σ} (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (f.pderivFun i) = coeff (d + single i 1) f * (d i + 1) := by
  rfl

theorem pderivFun_add {i : σ} (f g : MvPowerSeries σ R) :
    pderivFun i (f + g) = pderivFun i f + pderivFun i g := by
  ext
  rw [coeff_pderivFun, map_add, map_add, coeff_pderivFun, coeff_pderivFun, add_mul]

theorem pderivFun_C {i : σ} (r : R) : pderivFun i (C r) = 0 := by
  ext n
  rw [coeff_pderivFun, coeff_add_single_C, zero_mul, (coeff n).map_zero]

theorem pderivFun_one {i : σ} : pderivFun i (1 : MvPowerSeries σ R) = 0 := by
  rw [← map_one C, pderivFun_C (1 : R)]

end Semiring

section CommSemiring

variable [CommSemiring R]

private theorem pderivFun_coe {i : σ} (f : MvPolynomial σ R) :
    (f : MvPowerSeries σ R).pderivFun i = f.pderiv i := by
  ext
  rw [coeff_pderivFun, coeff_coe, coeff_coe, coeff_pderiv]

private theorem trunc_pderivFun [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    trunc R n (pderivFun i f) = pderiv i (trunc R (n + single i 1) f) := by
  ext
  rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_pderivFun, coeff_pderiv, coeff_trunc, if_pos (add_lt_add_left h _)]
  · rw [coeff_pderiv, coeff_trunc, if_neg ((add_lt_add_iff_right _).not.mpr h), zero_mul]

-- A special case of `pderivFun_mul`, used in its proof.
private theorem pderivFun_coe_mul_coe {i : σ} (f g : MvPolynomial σ R) :
    pderivFun i (f * g : MvPowerSeries σ R) = f * pderiv i g + g * pderiv i f := by
  rw [← coe_mul, pderivFun_coe, pderiv_mul, add_comm, mul_comm _ g, ← coe_mul, ← coe_mul,
    MvPolynomial.coe_add]

private theorem pderivFun_mul {i : σ} (f g : MvPowerSeries σ R) :
    pderivFun i (f * g) = f • g.pderivFun i + g • f.pderivFun i := by
  classical
  ext n
  have h₁ : n < n + single i 1 := lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₂ : n + single i 1 < n + single i 1 + single i 1 :=
    lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₃ : n < n + single i 1 + single i 1 := lt_trans h₁ h₂
  rw [coeff_pderivFun, map_add, ← coeff_trunc_mul_trunc_eq_coeff_mul _ _ _ h₂, smul_eq_mul,
    smul_eq_mul, ← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ g (f.pderivFun i) h₃ h₁,
    ← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ f (g.pderivFun i) h₃ h₁, trunc_pderivFun,
    trunc_pderivFun, ← coeff_coe, ← coeff_coe, ← coeff_coe, ← map_add, coe_mul, coe_mul, coe_mul,
    ← pderivFun_coe_mul_coe, coeff_pderivFun]

private theorem pderivFun_smul {i : σ} (r : R) (f : MvPowerSeries σ R) :
    pderivFun i (r • f) = r • pderivFun i f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, pderivFun_mul, pderivFun_C, smul_zero, add_zero, smul_eq_mul]

variable (R) in
/-- The formal partial derivative of a multivariate formal power series with respect to
variable `i`, as an `R`-derivation on `MvPowerSeries σ R`. -/
@[no_expose]
noncomputable def pderiv (i : σ) : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := pderivFun i
  map_add' := pderivFun_add
  map_smul' := pderivFun_smul
  map_one_eq_zero' := pderivFun_one
  leibniz' := pderivFun_mul

@[simp] theorem pderiv_C {i : σ} {r : R} : pderiv R i (C r) = 0 := pderivFun_C r

theorem pderiv_one {i : σ} : pderiv R i 1 = 0 := pderiv_C

theorem coeff_pderiv {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1) :=
  coeff_pderivFun f n

theorem pderiv_coe {i : σ} (f : MvPolynomial σ R) :
    pderiv R i f = MvPolynomial.pderiv i f := pderivFun_coe f

@[simp]
theorem pderiv_X_self {i : σ} : pderiv R i (X i) = 1 := by
  classical
  ext n
  simp only [coeff_pderiv, coeff_X, boole_mul, add_eq_right, coeff_one]
  split_ifs <;> simp_all

@[simp]
theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv R i (X j) = 0 := by
  classical
  ext n
  simpa only [coeff_pderiv, coeff_X, boole_mul, coeff_zero] using
    if_neg (ne_iff.mpr ⟨i, by grind [Finsupp.add_apply]⟩)

theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv R i (X j) = Pi.single (M := fun _ => MvPowerSeries σ R) i 1 j := by
  by_cases h : i = j
  · subst h; simp only [pderiv_X_self, Pi.single_eq_same]
  · grind [pderiv_X_of_ne]

theorem trunc_pderiv [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    trunc R n (pderiv R i f) = MvPolynomial.pderiv i (trunc R (n + single i 1) f) :=
  trunc_pderivFun ..

/-- The partial derivative of `g^n` equals `n * g^(n-1) * g'`. -/
theorem pderiv_pow {i : σ} (g : MvPowerSeries σ R) (n : ℕ) :
    pderiv R i (g ^ n) = n * g ^ (n - 1) * pderiv R i g := by
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, mul_assoc]

end CommSemiring

/-- If `f` and `g` have the same constant term and all partial derivatives, then they are equal.

The `CommRing` assumption is needed because the proof uses `smul_right_inj`, which requires
cancellation of addition in `R`; `IsAddTorsionFree` alone does not suffice. -/
theorem pderiv.ext [CommRing R] [IsAddTorsionFree R] {f g : MvPowerSeries σ R}
    (hD : ∀ i, pderiv R i f = pderiv R i g) (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  by_cases h : n = 0
  · rw [h, coeff_zero_eq_constantCoeff, hc]
  obtain ⟨i, hi : n i ≠ 0⟩ := ne_iff.mp h
  have : single i 1 ≤ n := fun j ↦ by
    by_cases hj : j = i <;> grind [single_eq_same, single_eq_of_ne]
  have e := congr(coeff (n - single i 1) $(hD i))
  rwa [coeff_pderiv, coeff_pderiv, tsub_add_cancel_of_le this, coe_tsub, Pi.sub_apply,
    single_eq_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel,
    mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul, smul_right_inj hi] at e

@[simp]
theorem pderiv_inv {i : σ} [CommRing R] (f : (MvPowerSeries σ R)ˣ) :
    pderiv R i ↑f⁻¹ = -(↑f⁻¹ : MvPowerSeries σ R) ^ 2 * pderiv R i f :=
  (pderiv R i).leibniz_of_mul_eq_one f.inv_mul

@[simp]
theorem pderiv_invOf {i : σ} [CommRing R] (f : MvPowerSeries σ R) [Invertible f] :
    pderiv R i ⅟f = -⅟f ^ 2 * pderiv R i f :=
  (pderiv R i).leibniz_invOf f

/-
The following theorem is stated only in the case that `R` is a field. This is because
there is currently no instance of `Inv (MvPowerSeries σ R)` for more general base rings `R`.
-/

@[simp]
theorem pderiv_inv' {i : σ} [Field R] (f : MvPowerSeries σ R) :
    pderiv R i f⁻¹ = -f⁻¹ ^ 2 * pderiv R i f := by
  by_cases h : constantCoeff f = 0
  · suffices f⁻¹ = 0 by
      rw [this, pow_two, zero_mul, neg_zero, zero_mul, map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact MvPowerSeries.inv_mul_cancel (h := h)

end MvPowerSeries
