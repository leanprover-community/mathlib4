/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

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

open Filter

open scoped Nat Real Topology

variable {p q : ℕ}

variable {a : Multiset ℂ} {b : Multiset ℂ} {n m : ℕ} {j k : ℂ}

/-- The coefficients of the regularized hypergeometric series. -/
def regularizedHGFunCoeff (a : Multiset ℂ) (b : Multiset ℂ) (n : ℕ) : ℂ :=
  (a.map (ascPochhammer ℂ n).eval).prod / (n ! * (b.map (Gamma <| · + n)).prod)

attribute [grind .] Nat.factorial_ne_zero

@[grind =]
theorem regularizedHGFunCoeff_eq_zero_iff :
    regularizedHGFunCoeff a b n = 0 ↔
    (∃ j ∈ a, ∃ k < n, j = -k) ∨ ∃ j ∈ b, ∃ (m : ℕ), j + n = -m := by
  unfold regularizedHGFunCoeff
  simp
  grind

variable (a b n m) in
theorem regularizedHGFunCoeff_eq_zero_right (hb : -(n : ℂ) - m ∈ b := by grind) :
    regularizedHGFunCoeff a b n = 0 := by grind

variable (a b n m) in
theorem regularizedHGFunCoeff_eq_zero_left (ha : -(m : ℂ) ∈ a := by grind)
    (hm : m < n := by grind) :
  regularizedHGFunCoeff a b n = 0 := by grind

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one (hb : ∀ k ∈ b, k ≠ -n) :
    regularizedHGFunCoeff a b (n + 1) = regularizedHGFunCoeff a b n *
      ((a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod  * (n + 1))) := calc
  _ = (a.map fun i ↦ ((ascPochhammer ℂ n).eval i) * (i + n)).prod /
      (n ! * (n + 1) * (b.map fun j ↦ Gamma (j + n) * (j + n)).prod) := by
    unfold regularizedHGFunCoeff
    congrm ((a.map ?_).prod / (?_ * Multiset.prod ?_))
    · ext j
      simp [ascPochhammer_succ_right]
    · rw [Nat.factorial_succ]
      grind
    · refine Multiset.map_congr rfl (fun j hj ↦ ?_)
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
      grind
  _ = _ := by
    unfold regularizedHGFunCoeff
    simp_rw [div_mul_div_comm, Multiset.prod_map_mul]
    ring

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one_div_self (h : regularizedHGFunCoeff a b n ≠ 0) :
    regularizedHGFunCoeff a b (n + 1) / regularizedHGFunCoeff a b n =
      (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) := by
  by_cases! hb : ∀ k ∈ b, k ≠ -n
  · rw [regularizedHGFunCoeff_add_one hb]
    field_simp
  · obtain ⟨j, hj⟩ := hb
    have h₁ : (b.map (· + (n : ℂ))).prod = 0 := by
      grind [Multiset.prod_eq_zero, Multiset.mem_map]
    simp [regularizedHGFunCoeff_eq_zero_right a b n 0, h₁]

private theorem multiset_prod_eq_pow_mul_multiset_prod (a : Multiset ℂ) (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod = n ^ a.card * (a.map (· / (n : ℂ) + 1)).prod := calc
  _ = (a.map (fun j ↦ n * (j / (n : ℂ) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by
    simp [Multiset.prod_map_mul]

private
theorem multiset_prod_div_multiset_prod_mul (a : Multiset ℂ) (b : Multiset ℂ) (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) =
      n ^ (a.card - (b.card : ℤ) - 1) * (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹)) := by
  rw [multiset_prod_eq_pow_mul_multiset_prod a hn, multiset_prod_eq_pow_mul_multiset_prod b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ b.card * n ^ (a.card - b.card - (1 : ℤ)) *
        (a.map (fun x : ℂ ↦ (x + n) / n)).prod := by
      congr 1
      rw [← pow_succ', ← zpow_natCast, ← zpow_natCast, ← zpow_add' (by left; norm_cast)]
      grind
    _ = _ := by ring

variable (a b) in
/-- The regularized hypergeometric series. -/
def regularizedHGFunSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (regularizedHGFunCoeff a b)

@[simp]
theorem regularizedHGFunSeries_coeff :
    (regularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b := by
  unfold regularizedHGFunSeries
  ext; simp

@[simp, grind =]
theorem regularizedHGFunSeries_eq_zero :
    regularizedHGFunSeries a b n = 0 ↔ regularizedHGFunCoeff a b n = 0 := by
  apply FormalMultilinearSeries.ofScalars_eq_zero

variable (a b) in
/-- The regularized hypergeometric function. -/
def regularizedHGFun (z : ℂ) : ℂ := (regularizedHGFunSeries a b).sum z

/-- If there exists `j` and `k : ℕ`, such that `a j = -k`, then the hypergeometric series is finite
and has convergence radius `∞`. -/
theorem radius_regularizedHGFunSeries_eq_top_of_finite (ha : j ∈ a) (hj : j = -n) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use n + 1
  grind

variable (b) in
/-- If for all `j` and `k : ℕ`, `a j ≠ -k`, then the coefficients of the hypergeometric series
are eventually non-vanishing. -/
theorem eventually_atTop_regularizedHGFunCoeff_ne_zero (h : ∀ j ∈ a, ∀ (k : ℕ), j ≠ -↑k) :
    ∀ᶠ (n : ℕ) in atTop, regularizedHGFunCoeff a b n ≠ 0 := by
  rw [Filter.eventually_atTop]
  use b.toFinset.sup (⌈-re ·⌉₊) + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, hj, m, h'⟩)
  · grind
  · suffices (m : ℝ) < 0 by grind
    suffices -j.re < n by
      have h : j = -m - n := by grind
      simpa [h] using this
    calc
      -j.re ≤ ⌈-j.re⌉₊ := Nat.le_ceil (-j.re)
      _ ≤ b.toFinset.sup (⌈-re ·⌉₊) := mod_cast Finset.le_sup (by grind) (f := (⌈-re ·⌉₊))
      _ < n := by norm_cast

variable (a) in
private theorem tendsto_multiset_prod_div_add_one :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod) atTop (𝓝 1) := by
  suffices ∀ i ∈ a, Tendsto (fun n : ℕ ↦ (i / n + 1)) atTop (𝓝 <| (fun _ : _ ↦ 1) i) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

variable (a b) in
private theorem tendsto_multiset_prod_div_multiset_prod_mul :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (tendsto_multiset_prod_div_add_one a).div
    ((tendsto_multiset_prod_div_add_one b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

/-- If `a.card ≤ b.card`, then the hypergeometric series has infinite convergence radius. -/
@[grind =]
theorem radius_regularizedHGFunSeries_eq_top (h : a.card ≤ b.card) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  by_cases! ha : ∃ j ∈ a, ∃ k : ℕ, j = -k
  · obtain ⟨j, hj, k, ha⟩ := ha
    apply radius_regularizedHGFunSeries_eq_top_of_finite hj ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
  · simp only [Nat.succ_eq_add_one]
    have h₁ : Tendsto (fun (n : ℕ) ↦ (n : ℂ) ^ (a.card - (b.card : ℤ) - 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℂ)).pow (b.card + 1 - a.card)
      rw [zero_pow (by grind)] at this
      apply this.congr
      intro n
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg, Int.ofNat_sub (by grind),
        Int.natCast_add_one]
      ring_nf
    have := (h₁.mul (tendsto_multiset_prod_div_multiset_prod_mul a b)).norm
    simp only [mul_one, norm_zero] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    rw [← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b hn₂, mul_div]

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius `1`, unless it
is a polynomial. -/
@[grind =]
theorem radius_regularizedHGFunSeries_eq_one (h : a.card = b.card + 1)
    (h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k) :
    (regularizedHGFunSeries a b).radius = 1 := by
  have : Tendsto (fun n ↦ ‖regularizedHGFunCoeff a b n.succ‖ / ‖regularizedHGFunCoeff a b n‖) atTop
      (𝓝 1) := by
    have := (tendsto_multiset_prod_div_multiset_prod_mul a b).norm
    simp only [norm_one] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b h'
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    simp [Nat.succ_eq_add_one, ← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b hn₂, h]
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 1) ℂ _ (by simp) this
  simpa

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius greater or equal
to `1`. -/
theorem radius_regularizedHGFunSeries_ge_one (h : a.card = b.card + 1) :
    1 ≤ (regularizedHGFunSeries a b).radius := by
  by_cases! h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k
  · grind
  · obtain ⟨j, hj, k, h'⟩ := h'
    rw [radius_regularizedHGFunSeries_eq_top_of_finite hj h']
    simp

section ZeroZero

/-- The regularized hypergeometric series with `a = b = 0` is exponential series. -/
@[simp, grind =]
theorem regularizedHGFunSeries_zero_zero :
    regularizedHGFunSeries 0 0 = NormedSpace.expSeries ℂ ℂ := by
  ext n
  simp [regularizedHGFunCoeff, NormedSpace.expSeries]

/-- The regularized hypergeometric function `₀F₀` is the complex exponential. -/
@[simp, grind =]
theorem regularizedHGFun_zero_zero : regularizedHGFun 0 0 = exp := by
  rw [exp_eq_exp_ℂ, NormedSpace.exp_eq_expSeries_sum (𝕂 := ℂ)]
  unfold regularizedHGFun
  simp

end ZeroZero

section Gaussian

/-- The regularized Gaussian hypergeometric function. -/
def regularizedGaussHGFunSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  regularizedHGFunSeries {a, b} {c}

/-- The regularized Gaussian hypergeometric function. -/
def regularizedGaussHGFun (a b c z : ℂ) : ℂ :=
  (regularizedGaussHGFunSeries a b c).sum z

variable {a b c z : ℂ}

variable (a b c) in
theorem regularizedGaussHGFunSeries_symm :
    regularizedGaussHGFunSeries a b c = regularizedGaussHGFunSeries b a c := by
  unfold regularizedGaussHGFunSeries
  rw [Multiset.pair_comm]

variable (a b c) in
theorem regularizedGaussHGFun_symm :
    regularizedGaussHGFun a b c = regularizedGaussHGFun b a c := by
  unfold regularizedGaussHGFun
  rw [regularizedGaussHGFunSeries_symm]

theorem coeff_regularizedGaussHGFunSeries :
    (a.regularizedGaussHGFunSeries b c).coeff n =
    ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) / (n ! * Gamma (c + n)) := by
  simp [regularizedGaussHGFunSeries, regularizedHGFunCoeff]

theorem Gamma_inv_mul_ordinaryHypergeometricSeries_eq (hc : ∀ k : ℕ, c ≠ -k) {n : ℕ} :
    (Gamma c)⁻¹ * (ordinaryHypergeometricSeries ℂ a b c).coeff n =
      (a.regularizedGaussHGFunSeries b c).coeff n := by
  rw [coeff_regularizedGaussHGFunSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.coeff_ofScalars, ordinaryHypergeometricCoefficient,
    ← Gamma_add_nat_div_Gamma_eq c hc]
  grind

theorem ordinaryHypergeometric_div_Gamma_eq (hc : ∀ k : ℕ, c ≠ -k) :
    ordinaryHypergeometric a b c z / Gamma c = regularizedGaussHGFun a b c z := by
  rw [regularizedGaussHGFun, ordinaryHypergeometric, div_eq_inv_mul, ← smul_eq_mul,
    FormalMultilinearSeries.const_smul_sum_apply]
  congr
  ext n
  simp [Gamma_inv_mul_ordinaryHypergeometricSeries_eq hc]

variable (b c) in
@[simp]
theorem radius_regularizedGaussHGFunSeries_eq_top_of_left (k : ℕ) :
    (regularizedGaussHGFunSeries (-k) b c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : ℂ)) (by simp) rfl

variable (a c) in
@[simp]
theorem radius_regularizedGaussHGFunSeries_eq_top_of_right (k : ℕ) :
    (regularizedGaussHGFunSeries a (-k) c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : ℂ)) (by simp) rfl

variable (c) in
@[grind =]
theorem radius_regularizedGaussHGFunSeries_eq_one (h : ∀ k : ℕ, a ≠ -k ∧ b ≠ -k) :
    (regularizedGaussHGFunSeries a b c).radius = 1 :=
  radius_regularizedHGFunSeries_eq_one rfl (by simp; grind)

variable (a b c) in
theorem radius_regularizedGaussHGFunSeries_ge_one :
    1 ≤ (regularizedGaussHGFunSeries a b c).radius :=
  radius_regularizedHGFunSeries_ge_one rfl

end Gaussian

end Complex
