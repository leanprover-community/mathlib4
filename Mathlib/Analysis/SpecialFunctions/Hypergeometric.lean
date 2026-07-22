/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! # Generalized hypergeometric function

In this file we define the generalized hypergeometric function as well as the Gaussian
hypergeometric function.

The hypergeometric function is a function with parameters `a : Fin p → ℂ` and `b : Fin q → ℂ`.

Note that in this file, we use the *regularized* version of the hypergeometric function, that is
the coefficients are divides by `∏ i, Gamma (b i)`, giving in the case of the Gaussian
hypergeometric function the series representation
$$\sum_j \frac{(a)^n (b)^n}{\Gamma(c + n) n!} z^ n,$$
where `(a)^n` denotes the rising Pochhammer symbol.

This definition is valid for all values of `c`, whereas the usual hypergeometric function has a
pole for `c = -k` and `k : ℕ`. To our knowledge the regularized hypergeometric function only appears
in the literature only for the Gaussian case, it is implicit in the definition of the Bessel
function (`p = 0` and `q = 1`).
To recover the usual hypergeometric function, simply multiply by `∏ i, Gamma (b i)`.

## Definitions
For the general case we have
* `Complex.regularizedHGFunCoeff`: the coefficients
* `Complex.regularizedHGFunSeries`: the formal multilinear series
* `Complex.regularizedHGFun`: the function

For the Gaussian case (`p = 2` and `q = 1`), we define
* `Complex.regularizedGaussHGFunSeries`: the formal multilinear series
* `Complex.regularizedGaussHGFun`: the function

## Results

Convergence:
* `radius_regularizedHGFunSeries_eq_top_of_finite`: in the case that the series reduces to a
  polynomial, the radius of convergence is infinite.
* `radius_regularizedHGFunSeries_eq_top`: if `p < q + 1`, then the series has infinite convergence
  radius.
* `radius_regularizedHGFunSeries_eq_one`: if `p = q + 1`, then the series has convergence radius
  `1`.
* `Complex.radius_regularizedGaussHGFunSeries_eq_one`: the Gaussian hypergeometric series has
  convergence radius `1`.

-/

@[expose] public noncomputable section

namespace Complex

open scoped Nat Real
open Topology Filter

/-- The ascending Pochhammer symbol is given by the ratio of `Γ` functions. -/
theorem Gamma_nat_add_div_Gamma_eq {n : ℕ} (z : ℂ) (hz : ∀ k : ℕ, -z ≠ k) :
    Gamma (n + z) / Gamma z = (ascPochhammer ℂ n).eval z := by
  induction n generalizing z with
  | zero =>
    simp
    grind
  | succ n ih =>
    suffices h : Gamma (n + 1 + z) = Gamma (n + z) * (z + n) by
      simp [ascPochhammer_succ_right, ← ih z hz, div_mul_eq_mul_div, h]
    calc
      _ = Gamma ((z + n) + 1) := by group
      _ =  (z + n) * Gamma (z + n) := by grind
      _ = _ := by group

variable {p q : ℕ}

variable {a : Fin p → ℂ} {b : Fin q → ℂ} {n : ℕ}

/-- The coefficients of the regularized hypergeometric series. -/
def regularizedHGFunCoeff (a : Fin p → ℂ) (b : Fin q → ℂ) (n : ℕ) : ℂ :=
  (∏ i : Fin p, (ascPochhammer ℂ n).eval (a i)) / (n ! * ∏ j : Fin q, Gamma (b j + n))

@[grind =]
theorem regularizedHGFunCoeff_eq_zero_iff :
    regularizedHGFunCoeff a b n = 0 ↔
    (∃ j, ∃ k < n, k = -a j) ∨ ∃ (j : Fin q) (m : ℕ), b j + n = -m := by
  unfold regularizedHGFunCoeff
  simp [Finset.prod_eq_zero_iff, Gamma_eq_zero_iff, n.factorial_ne_zero]

variable (a b n) in
theorem regularizedHGFunCoeff_eq_zero_right
    (hb : ∃ (j : Fin q) (m : ℕ), b j = -n - m) : regularizedHGFunCoeff a b n = 0 := by grind

variable (a b n) in
theorem regularizedHGFunCoeff_eq_zero_left
    (ha : ∃ (j : Fin p), ∃ k < n, k = -a j) : regularizedHGFunCoeff a b n = 0 := by grind

/-- If `a j = -k` for some `k : ℕ`, then the coefficients of the regularized hypergeometric series
vanish for all `n > k`. -/
theorem regularizedHGFunCoeff_eq_zero_left' (a : Fin p → ℂ) (b : Fin q → ℂ) (k n : ℕ)
    (ha : ∃ (j : Fin p), a j = -k) (hkn : k < n) : regularizedHGFunCoeff a b n = 0 := by grind

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one {a : Fin p → ℂ} {b : Fin q → ℂ} {n : ℕ}
    (hb : ∀ j, b j ≠ -n) :
    regularizedHGFunCoeff a b (n + 1) = regularizedHGFunCoeff a b n *
      ((∏ i : Fin p, (a i + n)) / ((∏ i : Fin q, (b i + n)) * (n + 1))) := calc
  _ = (∏ i : Fin p, ((ascPochhammer ℂ n).eval (a i)) * (a i + n)) /
      (n ! * (n + 1) * ∏ j : Fin q, Gamma (b j + n) * (b j + n)) := by
    unfold regularizedHGFunCoeff
    congr
    · ext j
      simp [ascPochhammer_succ_right]
    · rw [Nat.factorial_succ]
      grind
    · ext j
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
      grind
  _ = _ := by
    unfold regularizedHGFunCoeff
    simp_rw [div_mul_div_comm, Finset.prod_mul_distrib]
    ring

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one_div_self
    (h : regularizedHGFunCoeff a b n ≠ 0) :
    regularizedHGFunCoeff a b (n + 1) / regularizedHGFunCoeff a b n =
      (∏ i : Fin p, (a i + n)) / ((∏ i : Fin q, (b i + n)) * (n + 1)) := by
  by_cases! hb : ∀ j, b j ≠ -n
  · rw [regularizedHGFunCoeff_add_one hb]
    field_simp
  · obtain ⟨j, hj⟩ := hb
    have h₁ : (∏ i, (b i + n)) = 0 := by
      grind [Finset.prod_eq_zero_iff]
    rw [regularizedHGFunCoeff_eq_zero_right a b n (by use j, 0; grind)]
    simp [h₁]

private theorem prod_eq_pow_mul_prod (a : Fin p → ℂ) (hn : n ≠ 0) :
    ∏ i, (a i + n) = n ^ p * ∏ i, (a i / n + 1) := calc
  _ = ∏ i, n * (a i / n + 1) := by
    congr; ext; field_simp
  _ = _ := by
    simp [Finset.prod_mul_distrib]

private
theorem finsetProd_div_finsetProd_mul (a : Fin p → ℂ) (b : Fin q → ℂ) (hn : n ≠ 0) :
    (∏ i : Fin p, (a i + n)) / ((∏ i : Fin q, (b i + n)) * (n + 1)) =
    n ^ (p - (q : ℤ) - 1) * (∏ i, (a i / n + 1)) / ((∏ i, (b i / n + 1)) * (1 + (n : ℂ)⁻¹)) := by
  rw [prod_eq_pow_mul_prod a hn, prod_eq_pow_mul_prod b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ q * n ^ (p - q - (1 : ℤ)) * ∏ x, (a x + n) / n := by
      congr 1
      rw [← pow_succ', ← zpow_natCast, ← zpow_natCast, ← zpow_add' (by left; norm_cast)]
      grind
    _ = _ := by ring

/-- The regularized hypergeometric series. -/
def regularizedHGFunSeries (a : Fin p → ℂ) (b : Fin q → ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (regularizedHGFunCoeff a b)

@[simp]
theorem regularizedHGFunSeries_coeff (a : Fin p → ℂ) (b : Fin q → ℂ) :
    (regularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b := by
  unfold regularizedHGFunSeries
  ext; simp

@[simp, grind =]
theorem regularizedHGFunSeries_eq_zero (a : Fin p → ℂ) (b : Fin q → ℂ) (n : ℕ) :
    regularizedHGFunSeries a b n = 0 ↔ regularizedHGFunCoeff a b n = 0 := by
  apply FormalMultilinearSeries.ofScalars_eq_zero

/-- The regularized hypergeometric function. -/
def regularizedHGFun (a : Fin p → ℂ) (b : Fin q → ℂ) (z : ℂ) : ℂ :=
  (regularizedHGFunSeries a b).sum z

/-- If there exists `j` and `k : ℕ`, such that `a j = -k`, then the hypergeometric series is finite
and has convergence radius `∞`. -/
theorem radius_regularizedHGFunSeries_eq_top_of_finite
    (ha : ∃ (j : Fin p) (k : ℕ), a j = -k) : (regularizedHGFunSeries a b).radius = ⊤ := by
  obtain ⟨j, k, h⟩ := ha
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use k + 1
  grind

/-- If for all `j` and `k : ℕ`, `a j ≠ -k`, then the coefficients of the hypergeometric series
are eventually non-vanishing. -/
theorem eventually_atTop_regularizedHGFunCoeff_ne_zero
    (h : ∀ (j : Fin p) (k : ℕ), a j ≠ -↑k) :
    ∀ᶠ (n : ℕ) in atTop, regularizedHGFunCoeff a b n ≠ 0 := by
  rw [Filter.eventually_atTop]
  use ⌈iSup (-re ∘ b)⌉₊ + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, k, h'⟩)
  · grind
  · rw [Order.add_one_le_iff] at hn
    have h : b j = -k - n := by grind
    simpa [h, ← Nat.cast_add] using lt_of_le_of_lt (Nat.ceil_mono <| Finite.le_ciSup (-re ∘ b) j) hn

variable (a) in
private theorem tendsto_finsetProd_div_add_one :
    Tendsto (fun n : ℕ ↦ (∏ i, (a i / n + 1))) atTop (𝓝 1) := by
  suffices ∀ i ∈ Finset.univ, Tendsto (fun n : ℕ ↦ (a i / n + 1)) atTop (𝓝 <| (fun _ : _ ↦ 1) i) by
    simpa using tendsto_finsetProd Finset.univ this
  intro i
  simpa using (tendsto_const_div_atTop_nhds_zero_nat (a i)).add_const 1

variable (a b) in
private theorem tendsto_finsetProd_div_finsetProd_mul :
    Tendsto (fun n : ℕ ↦ (∏ i, (a i / n + 1)) / ((∏ i, (b i / n + 1)) * (1 + (n : ℂ)⁻¹))) atTop
      (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (tendsto_finsetProd_div_add_one a).div
    ((tendsto_finsetProd_div_add_one b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

/-- If `p < q + 1`, then the hypergeometric series has infinite convergence radius. -/
theorem radius_regularizedHGFunSeries_eq_top (a : Fin p → ℂ) (b : Fin q → ℂ) (h : p < q + 1) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  by_cases! ha : ∃ (j : Fin p) (k : ℕ), a j = -k
  · apply radius_regularizedHGFunSeries_eq_top_of_finite ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero ha
  · simp only [Nat.succ_eq_add_one]
    have h₁ : Tendsto (fun (n : ℕ) ↦ (n : ℂ) ^ (p - (q : ℤ) - 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℂ)).pow (q + 1 - p)
      rw [zero_pow (by grind)] at this
      apply this.congr
      intro n
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg, Int.ofNat_sub (by grind),
        Int.natCast_add_one]
      ring_nf
    have := (h₁.mul (tendsto_finsetProd_div_finsetProd_mul a b)).norm
    simp only [mul_one, norm_zero] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero ha (b := b)
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    rw [← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      finsetProd_div_finsetProd_mul a b hn₂, mul_div]

/-- If `p = q + 1`, then the hypergeometric series has convergence radius `1`, unless it is a
polynomial. -/
theorem radius_regularizedHGFunSeries_eq_one (a : Fin p → ℂ) (b : Fin q → ℂ) (h : p = q + 1)
    (h' : ∀ (j : Fin p) (k : ℕ), a j ≠ -k) :
    (regularizedHGFunSeries a b).radius = 1 := by
  have : Tendsto (fun n ↦ ‖regularizedHGFunCoeff a b n.succ‖ / ‖regularizedHGFunCoeff a b n‖) atTop
      (𝓝 1) := by
    have := (tendsto_finsetProd_div_finsetProd_mul a b).norm
    simp only [norm_one] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero h' (b := b)
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    simp [Nat.succ_eq_add_one, ← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      finsetProd_div_finsetProd_mul a b hn₂, h]
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 1) ℂ _ (by simp) this
  simpa

section Gaussian

/-- The regularized Gaussian hypergeometric function. -/
def regularizedGaussHGFunSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  regularizedHGFunSeries (fun (k : Fin 2) ↦ if k = 0 then a else b) (fun _ : Fin 1 ↦ c)

/-- The regularized Gaussian hypergeometric function. -/
def regularizedGaussHGFun (a b c z : ℂ) : ℂ :=
  (regularizedGaussHGFunSeries a b c).sum z

variable {a b c : ℂ}

variable (c) in
theorem radius_regularizedGaussHGFunSeries_eq_one (h : ∀ k : ℕ, a ≠ -k ∧ b ≠ -k) :
    (regularizedGaussHGFunSeries a b c).radius = 1 :=
  radius_regularizedHGFunSeries_eq_one _ _ (by simp) (by grind)

end Gaussian

end Complex
