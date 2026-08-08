/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.EulerProduct.ExpLog
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Euler Product for the Riemann Zeta Function and Dirichlet L-Series

The first main result of this file is the Euler Product formula for the Riemann ζ function
$$\prod_p \frac{1}{1 - p^{-s}}
   = \lim_{n \to \infty} \prod_{p < n} \frac{1}{1 - p^{-s}} = \zeta(s)$$
for $s$ with real part $> 1$ ($p$ runs through the primes).
`riemannZeta_eulerProduct` is the second equality above. There are versions
`riemannZeta_eulerProduct_hasProd` and `riemannZeta_eulerProduct_tprod` in terms of `HasProd`
and `tprod`, respectively.

The second result is `dirichletLSeries_eulerProduct` (with variants
`dirichletLSeries_eulerProduct_hasProd` and `dirichletLSeries_eulerProduct_tprod`),
which is the analogous statement for Dirichlet L-series.
-/

@[expose] public section

open Complex

variable {s : ℂ}

/-- When `s ≠ 0`, the map `n ↦ n^(-s)` is completely multiplicative and vanishes at zero. -/
noncomputable
def riemannZetaSummandHom (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, ofReal_natCast]
      using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _

/-- When `χ` is a Dirichlet character and `s ≠ 0`, the map `n ↦ χ n * n^(-s)` is completely
multiplicative and vanishes at zero. -/
noncomputable
def dirichletSummandHom {n : ℕ} (χ : DirichletCharacter ℂ n) (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := χ n * (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← ofReal_natCast]
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _]
      using mul_mul_mul_comm ..

/-- When `s.re > 1`, the map `n ↦ n^(-s)` is norm-summable. -/
lemma summable_riemannZetaSummand (hs : 1 < s.re) :
    Summable (fun n ↦ ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert! Real.summable_nat_rpow_inv.mpr hs with n
  rw [← ofReal_natCast,
    norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) <| re_neg_ne_zero_of_one_lt_re hs,
    neg_re, Real.rpow_neg <| Nat.cast_nonneg n]

lemma tsum_riemannZetaSummand (hs : 1 < s.re) :
    ∑' (n : ℕ), riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n = riemannZeta s := by
  have hsum := summable_riemannZetaSummand hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hsum.of_norm.tsum_eq_zero_add, map_zero, zero_add]
  simp only [riemannZetaSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Nat.cast_add, Nat.cast_one, one_div]

/-- When `s.re > 1`, the map `n ↦ χ(n) * n^(-s)` is norm-summable. -/
lemma summable_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    Summable (fun n ↦ ‖dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ by positivity)
    (fun n ↦ mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n)

open scoped LSeries.notation in
lemma tsum_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    ∑' (n : ℕ), dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n = L ↗χ s := by
  simp only [dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]

open Filter Nat Topology EulerProduct

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in terms of `HasProd`. -/
theorem riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative_hasProd <| summable_riemannZetaSummand hs

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in terms of `tprod`. -/
theorem riemannZeta_eulerProduct_tprod (hs : 1 < s.re) :
    ∏' p : Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  (riemannZeta_eulerProduct_hasProd hs).tprod_eq

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in the form of convergence of finite partial products. -/
theorem riemannZeta_eulerProduct (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (riemannZeta s)) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative <| summable_riemannZetaSummand hs

open scoped LSeries.notation

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in terms of `HasProd`. -/
theorem DirichletCharacter.LSeries_eulerProduct_hasProd {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (L ↗χ s) := by
  rw [← tsum_dirichletSummand χ hs]
  convert! eulerProduct_completely_multiplicative_hasProd <| summable_dirichletSummand χ hs

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in terms of `tprod`. -/
theorem DirichletCharacter.LSeries_eulerProduct_tprod {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    ∏' p : Primes, (1 - χ p * (p : ℂ) ^ (-s))⁻¹ = L ↗χ s :=
  (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).tprod_eq

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in the form of convergence of finite partial products. -/
theorem DirichletCharacter.LSeries_eulerProduct {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - χ p * (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (L ↗χ s)) := by
  rw [← tsum_dirichletSummand χ hs]
  apply eulerProduct_completely_multiplicative <| summable_dirichletSummand χ hs

open LSeries

/-- A variant of the Euler product for Dirichlet L-series. -/
theorem DirichletCharacter.LSeries_eulerProduct_exp_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
  let f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, map_zero]
    · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, div_eq_mul_inv,
        dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, f]
  simpa only [LSeries, h]
    using! exp_tsum_primes_log_eq_tsum (f := f) <| summable_dirichletSummand χ hs

open DirichletCharacter

/-- A variant of the Euler product for the L-series of `ζ`. -/
theorem ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert!
    modOne_eq_one (R := ℂ) ▸
      DirichletCharacter.LSeries_eulerProduct_exp_log (1 : DirichletCharacter ℂ 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- A variant of the Euler product for the Riemann zeta function. -/
theorem riemannZeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log hs

/-!
### Changing the level of a Dirichlet `L`-series
-/

/-- If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain the L-series
of `χ` considered as a Dirichlet character of level `N` from the L-series of `χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`. -/
lemma DirichletCharacter.LSeries_changeLevel {M N : ℕ} [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(changeLevel hMN χ) s =
      LSeries ↗χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rw [prod_eq_tprod_mulIndicator, ← DirichletCharacter.LSeries_eulerProduct_tprod _ hs,
    ← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]
  -- convert to a form suitable for `tprod_subtype`
  have (f : Primes → ℂ) : ∏' (p : Primes), f p = ∏' (p : ↑{p : ℕ | p.Prime}), f p := rfl
  rw [this, tprod_subtype _ fun p : ℕ ↦ (1 - (changeLevel hMN χ) p * p ^ (-s))⁻¹,
    this, tprod_subtype _ fun p : ℕ ↦ (1 - χ p * p ^ (-s))⁻¹, ← Multipliable.tprod_mul]
  rotate_left -- deal with convergence goals first
  · exact multipliable_subtype_iff_mulIndicator.mp
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  · exact multipliable_subtype_iff_mulIndicator.mp Multipliable.of_finite
  · congr 1 with p
    simp only [Set.mulIndicator_apply, Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_primeFactors,
      ne_eq, mul_ite, mul_one]
    by_cases h : p.Prime; swap
    · simp only [h, false_and, if_false]
    simp only [h, true_and, if_true]
    by_cases hp' : p ∣ N; swap
    · simp only [hp', false_and, ↓reduceIte, inv_inj, sub_right_inj, mul_eq_mul_right_iff,
        cpow_eq_zero_iff, Nat.cast_eq_zero, h.ne_zero, ne_eq, neg_eq_zero, or_false]
      have hq : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd h).mpr hp'
      simp only [hq.unit_spec ▸ DirichletCharacter.changeLevel_eq_cast_of_dvd χ hMN hq.unit,
        ZMod.cast_natCast hMN]
    · simp only [hp', NeZero.ne N, not_false_eq_true, and_self, ↓reduceIte]
      have : ¬IsUnit (p : ZMod N) := by rwa [ZMod.isUnit_prime_iff_not_dvd h, not_not]
      rw [MulChar.map_nonunit _ this, zero_mul, sub_zero, inv_one]
      refine (inv_mul_cancel₀ ?_).symm
      rw [sub_ne_zero, ne_comm]
      -- Remains to show `χ p * p ^ (-s) ≠ 1`. We show its norm is strictly `< 1`.
      apply_fun (‖·‖)
      simp only [norm_mul, norm_one]
      have ha : ‖χ p‖ ≤ 1 := χ.norm_le_one p
      have hb : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := norm_prime_cpow_le_one_half ⟨p, h⟩ hs
      exact ((mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_lt (by norm_num)).ne

section LogDirichlet

open Real hiding log exp_nat_mul exp_add
open ArithmeticFunction Primes Summable

variable {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}

/-- For `1 < s.re`, the sum over primes of `-log (1 - χ p * p ^ (-s))` — the logarithm of the Euler
product — equals the `L`-series of `n ↦ χ n * Λ n / Real.log n`.
-/
theorem DirichletCharacter.eulerProduct_log_eq_LSeries (hs : 1 < s.re) :
    ∑' p : Primes, -log (1 - χ p * p ^ (-s)) = LSeries (fun n ↦ χ n * Λ n / Real.log n) s := by
  have hpow_le (p : Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    grw [norm_mul, norm_le_one, norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re, one_mul]
    apply rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)
  rw [tsum_congr (fun p ↦ (hasSum_taylorSeries_neg_log' (hpow_le p)).tsum_eq.symm),
    LSeries_def₀ (by simp)]
  let f : ℕ → ℂ := fun n ↦ χ n * Λ n / Real.log n * ((n : ℂ) ^ (-s))
  calc
    _ = ∑' (p : Primes) (k : ℕ), (χ (p ^ (k + 1)) * ((p ^ (k + 1) : ℕ) : ℂ) ^ (-s)) *
          Λ (p ^ (k + 1)) / Real.log (p ^ (k + 1)) := by
      refine tsum_congr fun p ↦ tsum_congr fun k ↦ ?_
      have : Complex.log p ≠ 0 := mod_cast p.prop.log_ne_zero
      simp [mul_pow, ← cpow_nat_mul, ← natCast_cpow_natCast_mul, vonMangoldt_apply_pow,
        vonMangoldt_apply_prime p.2, field]
    _ = ∑' n : {n : ℕ // IsPrimePow n}, f n := by
      rw [← tsum_primes_pow_eq]
      · exact tsum_congr fun p ↦ tsum_congr fun k ↦ (by unfold f; simp; ring)
      · apply comp_injective _ Subtype.coe_injective (f := f)
        apply of_norm_bounded_eventually_nat (g := (↑· ^ (-s.re)))
        · simp [hs]
        · filter_upwards [eventually_gt_atTop 1] with n hn
          simp only [f, norm_mul, norm_div, norm_real, norm_eq_abs]
          grw [norm_le_one, vonMangoldt_le_log]
          have := log_pos (x := n) (mod_cast hn)
          field_simp
          rw [← ofReal_natCast n, norm_cpow_eq_rpow_re_of_nonneg (by simp) (by simp; grind)]
          simp
    _ = _ := by
      simp only [div_eq_mul_inv _ (_ ^ _), ← cpow_neg]
      suffices (Function.support f) ⊆ {n | IsPrimePow n} from
        tsum_subtype_eq_of_support_subset this
      intro n hn
      contrapose! hn
      simp [f, vonMangoldt_eq_zero_iff.mpr hn]

/-- For `1 < s.re`, the Dirichlet L-function is the exponential of the `L`-series of
`n ↦ χ n * Λ n / Real.log n`.
-/
theorem DirichletCharacter.LSeries_eq_exp_LSeries (hs : 1 < s.re) :
    exp (LSeries (fun (n : ℕ) ↦ χ n * Λ n / Real.log n) s) = L ↗χ s := by
  rw [← eulerProduct_log_eq_LSeries χ hs, LSeries_eulerProduct_exp_log χ hs]

theorem riemannZeta_eq_exp_LSeries {s : ℂ} (hs : 1 < s.re) :
    exp (LSeries (fun (n : ℕ) ↦ Λ n / Real.log n) s) = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  convert LSeries_eq_exp_LSeries (1 : DirichletCharacter ℂ 1) hs
  <;> simp [MulChar.one_apply <| isUnit_of_subsingleton _]

/-- For real `s > 1`, the logarithm of the (real) Riemann zeta function equals
`∑' n, Λ n / (n ^ s * Real.log n)`, where `Λ` is the von Mangoldt function.
-/
theorem log_riemannZeta_eq {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re = ∑' n, Λ n / (n ^ s * Real.log n) := by
  rw [← riemannZeta_eq_exp_LSeries (by simpa using hs), LSeries_def₀ (by simp)]
  convert Real.log_exp _
  convert exp_ofReal_re _
  push_cast
  congr! 2 with p
  rw [ofReal_cpow (by positivity)]
  simp [field]

end LogDirichlet
