/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Miscellaneous lemmas about generating functions
-/

public section

namespace Complex

/-- If a family of functions `f : ℤ → ℂ → E` satisfies the equation
`deriv (f k) x = ∑ i ∈ s, c i • f (k - p i) x`, then its generating function satisfies
`∑' k, t ^ k • f k x = exp ((x - x₀) * ∑ i ∈ s, c i * t ^ p i) • C`, where
`C = ∑' k, t ^ k • f k x₀` is a constant determined by a fixed point `x₀`. We require bound on
`t ^ k • f k x` uniform over `x` to ensure exchangeability of summation and derivative. -/
theorem tsum_zpow_smul_eq_exp_smul {ι : Type*} {s : Finset ι} {c : ι → ℂ} {p : ι → ℤ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℤ → ℂ → E} (hderiv : ∀ k, ∀ x ∈ U, HasDerivAt (f k) (∑ i ∈ s, c i • f (k - p i) x) x)
    {t : ℂ} (ht : t ≠ 0) {u : ℤ → ℝ} (hu : Summable u)
    (hbound : ∀ k, ∀ x ∈ U, ‖t ^ k • f k x‖ ≤ u k) {x₀ x : ℂ} (hx₀ : x₀ ∈ U) (hx : x ∈ U) :
    ∑' k, t ^ k • f k x = exp ((x - x₀) * ∑ i ∈ s, c i * t ^ p i) • (∑' k, t ^ k • f k x₀) := by
  have hdiff (k : ℤ) : DifferentiableOn ℂ (t ^ k • f k ·) U := fun x hx ↦
    ((hderiv k x hx).differentiableAt.const_smul _).differentiableWithinAt
  set w := ∑ i ∈ s, c i * t ^ p i
  set g := fun x ↦ ∑' k, t ^ k • f k x
  have hg : DifferentiableOn ℂ g U := differentiableOn_tsum_of_summable_norm hu hdiff hU hbound
  suffices ∀ x ∈ U, deriv (fun x ↦ exp (x * -w) • g x) x = 0 by
    rw [← neg_sub, neg_mul, ← mul_neg, sub_mul, exp_sub, div_eq_mul_inv, mul_comm, ← smul_smul,
      eq_inv_smul_iff₀ (exp_ne_zero _)]
    exact hU.is_const_of_deriv_eq_zero hUc (by fun_prop) this hx hx₀
  intro x hx
  suffices deriv g x = w • g x by
    rw [deriv_fun_smul (by fun_prop) ((hg x hx).differentiableAt (hU.mem_nhds hx)), this,
      deriv_cexp (by fun_prop)]
    simp
    module
  calc
    _ = ∑' k, deriv (fun w ↦ t ^ k • f k w) x :=
      (hasSum_deriv_of_summable_norm hu hdiff hU hbound hx).tsum_eq.symm
    _ = ∑' k, ∑ i ∈ s, (c i * t ^ p i) • (t ^ (k - p i) • f (k - p i) x) := by
      congr with k
      rw [((hderiv k x hx).fun_const_smul (t ^ k)).deriv, Finset.smul_sum]
      congr with i
      rw [smul_smul, smul_smul, mul_assoc, ← zpow_add₀ ht, add_sub_cancel, mul_comm]
    _ = ∑ i ∈ s, ∑' k, (c i * t ^ p i) • (t ^ (k - p i) • f (k - p i) x) := by
      refine Summable.tsum_finsetSum fun i _ ↦ .const_smul _ ?_
      simpa [Function.comp_def] using
        (Equiv.subRight (p i)).summable_iff.mpr (hu.of_norm_bounded (hbound · x hx))
    _ = _ := by
      simp_rw [w, Finset.sum_smul, tsum_const_smul'']
      congrm ∑ i ∈ s, _ • $((Equiv.subRight (p i)).tsum_eq fun k ↦ t ^ k • f k x)

end Complex
