/-
Copyright (c) 2024 Edward Watine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Watine
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Ordinary hypergeometric function in a Banach algebra

In this file, we define `ordinaryHypergeometric`, the _ordinary_ or _Gaussian_ hypergeometric
function in a topological algebra `𝔸` over a field `𝕂` given by: $$
_2\mathrm{F}_1(a\ b\ c : \mathbb{K}, x : \mathbb{A}) = \sum_{n=0}^{\infty}\frac{(a)_n(b)_n}{(c)_n}
\frac{x^n}{n!}   \,,
$$
with $(a)_n$ is the ascending Pochhammer symbol (see `ascPochhammer`).

This file contains the basic definitions over a general field `𝕂` and notation for `₂F₁`,
as well as showing that terms of the series are zero if any of the `(a b c : 𝕂)` are sufficiently
large non-positive integers, rendering the series finite. In this file "sufficiently large" means
that `-n < a` for the `n`-th term, and similarly for `b` and `c`.

- `ordinaryHypergeometricSeries` is the `FormalMultilinearSeries` given above for some `(a b c : 𝕂)`
- `ordinaryHypergeometric` is the sum of the series for some `(x : 𝔸)`
- `ordinaryHypergeometricSeries_eq_zero_of_nonpos_int` shows that the `n`-th term of the series is
zero if any of the parameters are sufficiently large non-positive integers

## `[RCLike 𝕂]`

If we have `[RCLike 𝕂]`, then we show that the latter result is an iff, and hence prove that the
radius of convergence of the series is unity if the series is infinite, or `⊤` otherwise.

- `ordinaryHypergeometricSeries_eq_zero_iff` is iff variant of
`ordinaryHypergeometricSeries_eq_zero_of_nonpos_int`
- `ordinaryHypergeometricSeries_radius_eq_one` proves that the radius of convergence of the
`ordinaryHypergeometricSeries` is unity under non-trivial parameters

## Notation

`₂F₁` is notation for `ordinaryHypergeometric`.

## References

See <https://en.wikipedia.org/wiki/Hypergeometric_function>.

## Tags

hypergeometric, gaussian, ordinary
-/

open Nat

section Field

variable {𝕂 : Type*} (𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [TopologicalRing 𝔸]

/-- `ordinaryHypergeometricSeries 𝔸 (a b c : 𝕂)` is a `FormalMultilinearSeries`.
Its sum is the `ordinaryHypergeometric` map. -/
noncomputable def ordinaryHypergeometricSeries (a b c : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  fun n => ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
    ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

variable {𝔸} (a b c : 𝕂)

/-- `ordinaryHypergeometric (a b c : 𝕂) : 𝔸 → 𝔸` is the ordinary hypergeometric map, defined as the
sum of the `FormalMultilinearSeries` `ordinaryHypergeometricSeries 𝔸 a b c`.

Note that this takes the junk value `0` outside the radius of convergence.
-/
noncomputable def ordinaryHypergeometric (x : 𝔸) : 𝔸 :=
  (ordinaryHypergeometricSeries 𝔸 a b c).sum x

@[inherit_doc]
notation "₂F₁" => ordinaryHypergeometric

theorem ordinaryHypergeometricSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (ordinaryHypergeometricSeries 𝔸 a b c n fun _ => x) =
      ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
        ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n := by
  simp [ordinaryHypergeometricSeries]

/-- This naming follows the convention of `NormedSpace.expSeries_apply_eq'`. -/
theorem ordinaryHypergeometricSeries_apply_eq' (x : 𝔸) :
    (fun n => ordinaryHypergeometricSeries 𝔸 a b c n fun _ => x) =
      fun n => ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
        ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n := by
  simp [ordinaryHypergeometricSeries]

theorem ordinaryHypergeometric_sum_eq (x : 𝔸) : (ordinaryHypergeometricSeries 𝔸 a b c).sum x =
    ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
      ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n :=
  tsum_congr fun n => ordinaryHypergeometricSeries_apply_eq a b c x n

theorem ordinaryHypergeometric_eq_tsum : ₂F₁ a b c =
    fun (x : 𝔸) => ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a *
      (ascPochhammer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n :=
  funext (ordinaryHypergeometric_sum_eq a b c)

theorem ordinaryHypergeometricSeries_apply_zero (n : ℕ) :
    (ordinaryHypergeometricSeries 𝔸 a b c n fun _ => 0) = Pi.single (f := fun _ => 𝔸) 0 1 n := by
  rw [ordinaryHypergeometricSeries_apply_eq]
  cases n <;> simp

@[simp]
theorem ordinaryHypergeometric_zero : ₂F₁ a b c (0 : 𝔸) = 1 := by
  simp [ordinaryHypergeometric_eq_tsum, ← ordinaryHypergeometricSeries_apply_eq,
    ordinaryHypergeometricSeries_apply_zero]

@[simp]
theorem ordinaryHypergeometric_op [T2Space 𝔸] (x : 𝔸) :
    ₂F₁ a b c (MulOpposite.op x) = MulOpposite.op (₂F₁ a b c x) := by
  simp [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq, ← MulOpposite.op_pow,
    ← MulOpposite.op_smul, tsum_op]

@[simp]
theorem ordinaryHypergeometric_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    ₂F₁ a b c (MulOpposite.unop x) = MulOpposite.unop (₂F₁ a b c x) := by
  simp [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq, ← MulOpposite.unop_pow,
     ← MulOpposite.unop_smul, tsum_unop]

theorem ordinaryHypergeometricSeries_symm :
    ordinaryHypergeometricSeries 𝔸 a b c = ordinaryHypergeometricSeries 𝔸 b a c := by
  ext
  simp [ordinaryHypergeometricSeries, mul_assoc, mul_left_comm]

/-- If any parameter to the series is a sufficiently large nonpositive integer, then the series
term is zero. -/
lemma ordinaryHypergeometricSeries_eq_zero_of_neg_nat {n k : ℕ}
    (habc : k = -a ∨ k = -b ∨ k = -c) (hk : k < n) :
      ordinaryHypergeometricSeries 𝔸 a b c n = 0 := by
  rw [ordinaryHypergeometricSeries]
  rcases habc with h | h | h
  all_goals
    ext
    simp [(ascPochhammer_eval_eq_zero_iff n _).2 ⟨k, hk, h⟩]

end Field

section RCLike

open Asymptotics Filter Real Set Nat

open scoped Topology

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  (a b c : 𝕂)

theorem ordinaryHypergeometric_radius_top_of_neg_nat₁ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 (-(k : 𝕂)) b c).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
  exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat (-(k : 𝕂)) b c (by aesop) (by omega)

theorem ordinaryHypergeometric_radius_top_of_neg_nat₂ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 a (-(k : 𝕂)) c).radius = ⊤ := by
  rw [ordinaryHypergeometricSeries_symm]
  exact ordinaryHypergeometric_radius_top_of_neg_nat₁ 𝔸 a c

theorem ordinaryHypergeometric_radius_top_of_neg_nat₃ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 a b (-(k : 𝕂))).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
  exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat a b (-(k : 𝕂)) (by aesop) (by omega)

/-- An iff variation on `ordinaryHypergeometricSeries_eq_zero_of_nonpos_int` for `[RCLike 𝕂]`. -/
lemma ordinaryHypergeometricSeries_eq_zero_iff (n : ℕ) :
    ordinaryHypergeometricSeries 𝔸 a b c n = 0 ↔
      ∃ k < n, k = -a ∨ k = -b ∨ k = -c := by
  refine ⟨fun h ↦ ?_, fun zero ↦ ?_⟩
  · rw [ordinaryHypergeometricSeries,
      smul_eq_zero (c:=(_ * (Polynomial.eval c (ascPochhammer 𝕂 n))⁻¹))
      (x:=ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸)] at h
    cases' h with h hm
    · simp only [_root_.mul_eq_zero, inv_eq_zero] at h
      rcases h with ((hn | h) | h) | h
      · simp [Nat.factorial_ne_zero] at hn
      all_goals
        obtain ⟨kn, hkn, hn⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 h
        exact ⟨kn, hkn, by tauto⟩
    · rw [ContinuousMultilinearMap.ext_iff] at hm
      absurd hm
      push_neg
      exact ⟨fun _ ↦ 1, by simp⟩
  · obtain ⟨_, h, hn⟩ := zero
    exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat a b c hn h

theorem ordinaryHypergeometricSeries_succ_norm_div_norm (n : ℕ)
    (habc : ∀ kn < n, (↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c)) :
      ‖ordinaryHypergeometricSeries 𝔸 a b c (n+1)‖ / ‖ordinaryHypergeometricSeries 𝔸 a b c n‖ =
        ‖a + n‖ * ‖b + n‖ * ‖c + n‖⁻¹ * ‖1 + (n : 𝕂)‖⁻¹ := by
  simp [ordinaryHypergeometricSeries, factorial_succ, ascPochhammer_succ_eval]
  rw [norm_smul (x:=ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 (n + 1) 𝔸),
    norm_smul (x:=ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸)]
  simp only [norm_mul, norm_inv, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
  have : ‖(n ! : 𝕂)‖⁻¹ * ‖(n : 𝕂) + 1‖⁻¹ * (‖Polynomial.eval a (ascPochhammer 𝕂 n)‖ * ‖a + n‖) *
    (‖Polynomial.eval b (ascPochhammer 𝕂 n)‖ * ‖b + n‖) *
    (‖c + n‖⁻¹ * ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹) /
    (‖(n ! : 𝕂)‖⁻¹ * ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖ *
    ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖ * ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹) =
    ‖(n ! : 𝕂)‖⁻¹⁻¹ * ‖(n ! : 𝕂)‖⁻¹ * ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖ *
    ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖⁻¹ * ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖ *
    ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖⁻¹ * ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹⁻¹ *
    ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹ * ‖a + n‖ * ‖b + n‖ * ‖c + n‖⁻¹ * ‖1 + (n : 𝕂)‖⁻¹ :=
    by ring_nf
  rw [this, inv_inv, inv_inv]
  repeat rw [DivisionRing.mul_inv_cancel, one_mul]
  all_goals
    rw [norm_ne_zero_iff]
  any_goals
    apply (ascPochhammer_eval_eq_zero_iff n _).not.2
    push_neg
    exact fun kn hkn ↦ by simp [habc kn hkn]
  exact cast_ne_zero.2 (factorial_ne_zero n)

/-- The ratio of successive terms of `ordinaryHypergeometricSeries` tends to one. This theorem
is used in the proof `ordinaryHypergeometric_ratio_tendsto_nhds_atTop`. -/
theorem ordinaryHypergeometricSeries_ratio_tendsto_one_atTop :
    Tendsto (fun k : ℕ ↦ (a + k) * (b + k) * (c + k)⁻¹ * ((1 : 𝕂) + k)⁻¹) atTop (𝓝 1) := by
  conv =>
    enter [1, n]
    rw [mul_assoc, ← mul_inv, ← div_eq_mul_inv, mul_div_mul_comm]
  apply (mul_one (1 : 𝕂)) ▸ Filter.Tendsto.mul <;>
  convert RCLike.tendsto_add_div_add_atTop_nhds _ _ (1 : 𝕂) one_ne_zero <;> simp

/-- The ratio of successive terms of the sum `ordinaryHypergeometric a b c r` is `r`. This theorem
is used for the ratio test in `ordinaryHypergeometricSeries_radius_eq_one`. -/
theorem ordinaryHypergeometric_ratio_tendsto_nhds_atTop {r : ℝ} (hr : 0 < r)
    (habc : ∀ kn : ℕ, ↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c) : Tendsto (fun n ↦
      ‖‖ordinaryHypergeometricSeries 𝔸 a b c (n + 1)‖ * r ^ (n + 1)‖ /
        ‖‖ordinaryHypergeometricSeries 𝔸 a b c n‖ * r ^ n‖) atTop (𝓝 r) := by
  simp_rw [← norm_div, mul_div_mul_comm, pow_succ, mul_div_right_comm]
  apply Real.norm_of_nonneg (le_of_lt hr) ▸ Filter.Tendsto.norm
  conv =>
    enter [1, n]
    rw [ordinaryHypergeometricSeries_succ_norm_div_norm, div_self (pow_ne_zero n hr.ne.symm),
      one_mul, ← norm_mul, ← norm_inv, ← norm_mul, ← norm_inv, ← norm_mul]
    rfl
    tactic => aesop
  apply (one_mul (_ : ℝ)) ▸ Filter.Tendsto.mul_const _ _
  exact (norm_one (α := 𝕂)) ▸ Filter.Tendsto.norm
    (ordinaryHypergeometricSeries_ratio_tendsto_one_atTop a b c)

/-- The radius of convergence of `ordinaryHypergeometricSeries` is unity if none of the parameters
are non-positive integers. This proof uses a similar technique to
`formalMultilinearSeries_geometric_radius`. -/
theorem ordinaryHypergeometricSeries_radius_eq_one
    (habc : ∀ kn : ℕ, ↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c) :
      (ordinaryHypergeometricSeries 𝔸 a b c).radius = 1 := by
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt (fun r hr ↦ ?_)
  · rw [← ENNReal.coe_one, ENNReal.coe_le_coe]
    have := FormalMultilinearSeries.summable_norm_mul_pow _ hr
    contrapose! this
    apply not_summable_of_ratio_test_tendsto_gt_one this
    refine ordinaryHypergeometric_ratio_tendsto_nhds_atTop 𝔸 a b c ?_ habc
    exact NNReal.coe_pos.2 (lt_trans zero_lt_one this)
  · rw [← Nat.cast_one, ENNReal.coe_lt_natCast, Nat.cast_one] at hr
    by_cases hr' : r = 0
    · simp [hr']
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      apply summable_of_ratio_test_tendsto_lt_one hr
      · refine Eventually.of_forall (fun n ↦ mul_ne_zero (norm_ne_zero_iff.2 ?_) ?_)
        · exact (ordinaryHypergeometricSeries_eq_zero_iff 𝔸 a b c n).not.2 (by aesop)
        · exact (pow_ne_zero n <| NNReal.coe_ne_zero.2 hr')
      apply ordinaryHypergeometric_ratio_tendsto_nhds_atTop 𝔸 a b c ?_ habc
      exact (Ne.intro hr').lt_of_le' (NNReal.coe_nonneg r)

end RCLike
