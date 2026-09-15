/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.InfiniteSum.Operator

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

local notation "C" => regularizedHGFunCoeff

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

@[simp]
theorem regularizedHGFunCoeff_zero_neg_nat_add_one (n i : ℕ) :
    regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) = regularizedHGFunCoeff 0 {(n : ℂ) + 1} i := by
  simp [regularizedHGFunCoeff, ← Gamma_nat_eq_factorial]
  ring_nf

variable (b) in
theorem mul_regularizedHGFunCoeff_of_mem_left (n : ℕ) {u : ℂ} (h : u ∈ a) :
    (u + n) * regularizedHGFunCoeff a b n =
    u * regularizedHGFunCoeff ((u + 1) ::ₘ a.erase u) b n := by
  unfold regularizedHGFunCoeff
  simp_rw [mul_div]
  congrm ?_ / _
  calc
    _ = (u + n) * (ascPochhammer ℂ n).eval u *
        ((a.erase u).map ((ascPochhammer ℂ n).eval · )).prod := by
      rw [← Multiset.prod_map_erase h]
      ring
    _ = u * (ascPochhammer ℂ n).eval (u + 1) *
        ((a.erase u).map ((ascPochhammer ℂ n).eval · )).prod := by
      rw [ascPochhammer_eval_succ']
    _ = _ := by
      simp
      ring

variable (a) in
theorem mul_regularizedHGFunCoeff_of_mem_right (n : ℕ) {u : ℂ} (h : u ∈ b) :
    (u - 1 + n) * regularizedHGFunCoeff a b n =
    regularizedHGFunCoeff a ((u - 1) ::ₘ b.erase u) n := by
  by_cases h0 : u - 1 + n = 0
  · symm
    simp [h0, regularizedHGFunCoeff_eq_zero_iff]
  unfold regularizedHGFunCoeff
  rw [mul_div, mul_comm, mul_div_assoc]
  suffices  ((u - 1 + n) / (n ! * (Multiset.map (fun x ↦ Gamma (x + n)) b).prod)) =
      1 / (n ! * (Multiset.map (fun x ↦ Gamma (x + n)) ((u - 1) ::ₘ b.erase u)).prod) by
    rw [this]
    ring
  calc
    _ = (u - 1 + n) / (n ! * (Gamma (u - 1 + n + 1)) *
        (Multiset.map (fun x ↦ Gamma (x + n)) (b.erase u)).prod) := by
      rw [← Multiset.prod_map_erase h]
      ring_nf
    _ = (u - 1 + n) / ((u - 1 + n) *
        (n ! * (Gamma (u - 1 + n)) * (Multiset.map (fun x ↦ Gamma (x + n)) (b.erase u)).prod)) := by
      rw [Complex.Gamma_add_one _ h0]
      ring
    _ = _ := by
      rw [← div_div, div_self h0, Multiset.map_cons, Multiset.prod_cons]
      ring

theorem mul_regularizedHGFunCoeff (n : ℕ) :
    (n + 1) * regularizedHGFunCoeff a b (n + 1) =
    a.prod * regularizedHGFunCoeff (a.map (· + 1)) (b.map (· + 1)) n := by
  unfold regularizedHGFunCoeff
  simp only [Nat.cast_add, Nat.cast_one, Multiset.map_map, Function.comp_apply]
  calc
    _ = (a.map ((ascPochhammer ℂ (n + 1)).eval ·)).prod /
        (n ! * (b.map (fun x ↦ Gamma (x + (n + 1)))).prod) := by
      rw [Nat.factorial_succ]
      push_cast
      field
    _ = a.prod * (a.map fun x ↦ (ascPochhammer ℂ n).eval (x + 1)).prod /
        (n ! * (b.map (fun x ↦ Gamma (x + (n + 1)))).prod) := by
      simp [ascPochhammer, Multiset.prod_map_mul]
    _ = a.prod * (a.map fun x ↦ (ascPochhammer ℂ n).eval (x + 1)).prod /
        (n ! * (b.map (fun x ↦ Gamma (x + 1 + n))).prod) := by
      congr with x
      congrm Gamma ($(by ring))
    _ = _ := by
      ring

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

@[simp]
theorem regularizedHGFun_zero : regularizedHGFun a b 0 = regularizedHGFunCoeff a b 0 := by
  rw [regularizedHGFun, regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalarsSum]
  simp

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

@[simp]
theorem radius_regularizedHGFunSeries_zero_eq_top : (regularizedHGFunSeries 0 b).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top (by simp)

theorem analyticAt_regularizedHGFun_of_card_le (h : a.card ≤ b.card) (z : ℂ) :
    AnalyticAt ℂ (regularizedHGFun a b) z :=
  ((regularizedHGFunSeries a b).hasFPowerSeriesOnBall
    (by simp [radius_regularizedHGFunSeries_eq_top h])).analyticAt_of_mem
    (by simp [radius_regularizedHGFunSeries_eq_top h])

@[fun_prop]
theorem analyticAt_regularizedHGFun_zero (z : ℂ) : AnalyticAt ℂ (regularizedHGFun 0 b) z :=
  analyticAt_regularizedHGFun_of_card_le (by simp) z

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

theorem regularizedHGFun_zero_singleton_neg_nat_add_one (n : ℕ) (z : ℂ) :
    regularizedHGFun 0 {-(n : ℂ) + 1} z = z ^ n * regularizedHGFun 0 {(n : ℂ) + 1} z := by
  unfold regularizedHGFun FormalMultilinearSeries.sum
  conv_lhs =>
    rw [← ((regularizedHGFunSeries 0 {-(n : ℂ) + 1}).summable (by simp)).sum_add_tsum_nat_add n]
  suffices ∑ i ∈ Finset.range n, z ^ i * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} i +
      ∑' i, z ^ (i + n) * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) =
      z ^ n * ∑' i, z ^ i * regularizedHGFunCoeff 0 {(n : ℂ) + 1} i by
    simpa
  calc
    _ = 0 + ∑' i, z ^ (i + n) * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) := by
      congrm $(Finset.sum_eq_zero fun i hi ↦ mul_eq_zero_of_right _ ?_) + _
      refine regularizedHGFunCoeff_eq_zero_right _ _ _ (n - i - 1) ?_
      rw [Multiset.mem_singleton]
      norm_cast
      grind
    _ = z ^ n * ∑' i, z ^ i * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) := by
      simp_rw [zero_add, ← tsum_mul_left]
      congr with i
      ring
    _ = _ := by simp

theorem mul_regularizedHGFun_zero_singleton_aux (u : ℂ) (n : ℕ) :
    u * C 0 {u + 1} (n + 1) + C 0 {u + 2} n = C 0 {u} (n + 1) := by
  suffices u * ((Gamma (u + 1 + (n + 1)))⁻¹ * ((↑ n !)⁻¹ * (n + 1 : ℂ)⁻¹)) +
      (Gamma (u + 2 + n))⁻¹ * (↑ n !)⁻¹ = (Gamma (u + (n + 1)))⁻¹ * ((↑ n !)⁻¹ * (n + 1 : ℂ)⁻¹) by
    simpa [regularizedHGFunCoeff, Nat.factorial_succ]
  calc
    _ = u * ((Gamma (u + (n + 1) + 1))⁻¹ * ((↑ n !)⁻¹ * (n + 1 : ℂ)⁻¹)) +
        (Gamma (u + (n + 1) + 1))⁻¹ * (↑ n !)⁻¹ := by
      ring_nf
    _ = (Gamma (u + (n + 1) + 1))⁻¹ * (↑ n !)⁻¹ * (u * (n + 1 : ℂ)⁻¹ + 1) := by
      ring
    _ = _ := by
      by_cases h : u + (↑n + 1) = 0
      · have h1 : u = -(n + 1) := by grind
        have h2 : u * (n + 1 : ℂ)⁻¹ + 1 = 0 := by
          rw [h1, neg_mul, mul_inv_cancel₀ (by norm_cast), neg_add_cancel]
        simp [h, h2]
      rw [Gamma_add_one _ h, mul_inv]
      field

theorem mul_regularizedHGFun_zero_singleton (u : ℂ) (z : ℂ) :
    regularizedHGFun 0 {u} z =
    u * regularizedHGFun 0 {u + 1} z + z * regularizedHGFun 0 {u + 2} z := by
  have hsummable1: Summable fun n ↦ z ^ n * C 0 {u + 1} n := by
    simpa using (regularizedHGFunSeries 0 {u + 1}).summable (by simp)
  have hsummable2 : Summable fun n ↦ u * (z ^ (n + 1) * C 0 {u + 1} (n + 1)) :=
    (hsummable1.comp_injective (add_left_injective 1)).mul_left u
  have hsummable3 : Summable fun n ↦ z * (z ^ n * C 0 {u + 2} n) := by
    apply Summable.mul_left
    simpa using (regularizedHGFunSeries 0 {u + 2}).summable (by simp)
  have hsummable4: Summable fun n ↦ z ^ n * C 0 {u} n := by
    simpa using (regularizedHGFunSeries 0 {u}).summable (by simp : z ∈ _)
  symm
  suffices u * ∑' n, z ^ n * C 0 {u + 1} (n) + z * ∑' n, z ^ n * C 0 {u + 2} n =
      ∑' n, z ^ n * C 0 {u} n by
    simpa [regularizedHGFun, FormalMultilinearSeries.sum]
  calc
    _ = u * C 0 {u + 1} 0 + (∑' n, u * (z ^ (n + 1) * C 0 {u + 1} (n + 1)) +
        ∑' n, z * (z ^ n * C 0 {u + 2} n)) := by
      rw [hsummable1.tsum_eq_zero_add]
      simp [tsum_mul_left]
      ring
    _ = u * C 0 {u + 1} 0 + ∑' n, (u * (z ^ (n + 1) * C 0 {u + 1} (n + 1)) +
        z * (z ^ n * C 0 {u + 2} n)) := by
      rw [Summable.tsum_add hsummable2 hsummable3]
    _ = u * C 0 {u + 1} 0 + ∑' n, z ^ (n + 1) * (u * C 0 {u + 1} (n + 1) + C 0 {u + 2} n) := by
      congr with n
      ring
    _ = u * C 0 {u + 1} 0 + ∑' n, z ^ (n + 1) * C 0 {u} (n + 1) := by
      congrm _ + ∑' n, z ^ (n + 1) * $(mul_regularizedHGFun_zero_singleton_aux u n)
    _ = _ := by
      conv_rhs => rw [hsummable4.tsum_eq_zero_add]
      simpa using mul_regularizedHGFunCoeff_of_mem_right 0 0 (Multiset.mem_singleton_self (u + 1))


section Derivative

private theorem summable_deriv_HGF {z : ℂ} (hz : ‖z‖ₑ < (regularizedHGFunSeries a b).radius) :
    Summable fun n ↦ z ^ n • (regularizedHGFunSeries a b).derivSeries.coeff n := by
  have hball : z ∈ Metric.eball 0 (regularizedHGFunSeries a b).radius := by simpa using hz
  have hdball : z ∈ Metric.eball 0 (regularizedHGFunSeries a b).derivSeries.radius := by
    simpa using hz.trans_le (FormalMultilinearSeries.radius_le_radius_derivSeries _)
  simpa using ((regularizedHGFunSeries a b).derivSeries).summable hdball

private theorem summable_deriv_HGF' {z : ℂ} (hz : ‖z‖ₑ < (regularizedHGFunSeries a b).radius) :
    Summable fun n ↦ z ^ n * (n * C a b n) := by
  apply Summable.comp_nat_add (k := 1)
  convert! ((ContinuousLinearMap.apply ℂ ℂ 1).summable (summable_deriv_HGF hz)).mul_left z
    using 2 with n
  simp
  ring

theorem mul_deriv_regularizedHGFun_of_mem_left {u : ℂ} (h : u ∈ a) {z : ℂ}
    (hz : ‖z‖ₑ < (regularizedHGFunSeries a b).radius) :
    z * deriv (regularizedHGFun a b) z =
    u * regularizedHGFun ((u + 1) ::ₘ a.erase u) b z - u * regularizedHGFun a b z := by
  rw [eq_sub_iff_add_eq]
  unfold regularizedHGFun deriv
  rw [FormalMultilinearSeries.fderiv_sum hz]
  suffices  z * ∑' n, z ^ n * ((n + 1) * C a b (n + 1)) + u * ∑' n, z ^ n * C a b n =
      u * ∑' (n : ℕ), z ^ n * C ((u + 1) ::ₘ a.erase u) b n by
    simpa [FormalMultilinearSeries.sum, ContinuousLinearMap.tsum_apply (summable_deriv_HGF hz)]
  calc
    _ = ∑' n, z * (z ^ n * ((n + 1) * C a b (n + 1))) + ∑' n, u * (z ^ n * C a b n) := by
      simp [tsum_mul_left]
    _ = ∑' n, z ^ (n + 1) * ((n + 1) * C a b (n + 1)) + ∑' n, u * (z ^ n * C a b n) := by
      congr with n
      ring
    _ = ∑' n, z ^ n * (n * C a b n) + ∑' n, u * (z ^ n * C a b n) := by
      rw [(summable_deriv_HGF' hz).tsum_eq_zero_add]
      simp
    _ = ∑' n, (z ^ n * (n * C a b n) + u * (z ^ n * C a b n)) := by
      rw [(summable_deriv_HGF' hz).tsum_add ?_]
      simpa using ((regularizedHGFunSeries a b).summable (by simpa using hz)).mul_left u
    _ = ∑' n, z ^ n * ((u + n) * C a b n) := by
      congr with n
      ring
    _ = ∑' (n : ℕ), z ^ n * (u * C ((u + 1) ::ₘ a.erase u) b n) := by
      congrm ∑' n, z ^ n * ?_
      rw [mul_regularizedHGFunCoeff_of_mem_left _ _ h]
    _ = _ := by
      rw [← tsum_mul_left]
      congr with n
      ring

theorem mul_deriv_regularizedHGFun_of_mem_right {u : ℂ} (h : u ∈ b) {z : ℂ}
    (hz : ‖z‖ₑ < (regularizedHGFunSeries a b).radius) :
    z * deriv (regularizedHGFun a b) z =
    regularizedHGFun a ((u - 1) ::ₘ b.erase u) z - (u - 1) * regularizedHGFun a b z  := by
  rw [eq_sub_iff_add_eq]
  unfold regularizedHGFun deriv
  rw [FormalMultilinearSeries.fderiv_sum hz]
  suffices z * ∑' n, z ^ n * ((n + 1) * C a b (n + 1)) + (u - 1) * ∑' n, z ^ n * C a b n =
      ∑' n, z ^ n * C a ((u - 1) ::ₘ b.erase u) n by
    simpa [FormalMultilinearSeries.sum, ContinuousLinearMap.tsum_apply (summable_deriv_HGF hz)]
  calc
    _ = ∑' n, z * (z ^ n * ((n + 1) * C a b (n + 1))) + ∑' n, (u - 1) * (z ^ n * C a b n) := by
      simp [tsum_mul_left]
    _ = ∑' n, z ^ (n + 1) * ((n + 1) * C a b (n + 1)) + ∑' n, (u - 1) * (z ^ n * C a b n) := by
      congr with n
      ring
    _ = ∑' n, z ^ n * (n * C a b n) + ∑' n, (u - 1) * (z ^ n * C a b n) := by
      rw [(summable_deriv_HGF' hz).tsum_eq_zero_add]
      simp
    _ = ∑' n, (z ^ n * (n * C a b n) + (u - 1) * (z ^ n * C a b n)) := by
      rw [(summable_deriv_HGF' hz).tsum_add ?_]
      simpa using ((regularizedHGFunSeries a b).summable (by simpa using hz)).mul_left (u - 1)
    _ = ∑' n, z ^ n * ((u - 1 + n) * C a b n) := by
      congr with n
      ring
    _ = _ := by
      congrm ∑' n, z ^ n * ?_
      exact mul_regularizedHGFunCoeff_of_mem_right _ _ h

theorem deriv_regularizedHGFun {z : ℂ} (hz : ‖z‖ₑ < (regularizedHGFunSeries a b).radius) :
    deriv (regularizedHGFun a b) z =
    a.prod * regularizedHGFun (a.map (· + 1)) (b.map (· + 1)) z := by
  unfold regularizedHGFun deriv
  rw [FormalMultilinearSeries.fderiv_sum hz]
  suffices ∑' n, z ^ n * ((n + 1) * C a b (n + 1)) =
      a.prod * ∑' n, z ^ n * C (a.map (· + 1)) (b.map (· + 1)) n by
    simpa [FormalMultilinearSeries.sum, ContinuousLinearMap.tsum_apply (summable_deriv_HGF hz)]
  rw [← tsum_mul_left]
  congr with n
  rw [mul_regularizedHGFunCoeff]
  ring

end Derivative

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
