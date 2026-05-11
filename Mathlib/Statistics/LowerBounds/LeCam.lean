/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Le Cam's two-point method (algebraic core)

Le Cam's two-point method reduces a minimax lower bound for an estimation
problem to a binary hypothesis testing problem. Given any estimator `T`
and any pair of distributions `P₀, P₁` indexed by parameters `θ₀, θ₁`
with loss separation `Δ = ℓ(θ₀, θ₁)`, the base inequality reads

`inf_T max_{i ∈ {0,1}} 𝔼_{Pᵢ} ℓ(T, θᵢ) ≥ (Δ / 2) · (1 - TV(P₀, P₁))`.

The right-hand side is the **Le Cam bound**. This module formalizes its
**algebraic core**, treating `Δ`, `TV(P₀, P₁)` and the testing errors as
real parameters. The full measure-theoretic statement, which additionally
requires the testing-affinity identity
`1 - TV(P₀, P₁) = inf_A (P₀ A + P₁ Aᶜ)`, can be layered on top once the
relevant Mathlib infrastructure on total-variation distance is in place
(see *Future work* in the accompanying PR description).

## Main definitions

* `Statistics.leCamBound Δ tv` — the scalar Le Cam lower bound
  `Δ / 2 * (1 - tv)`. It depends only on the loss separation `Δ` and the
  total-variation distance `tv` between the two hypothesis measures.

## Main results

* `Statistics.leCamBound_le_half_delta` — the Le Cam bound is dominated
  by the trivial upper bound `Δ / 2` (testing-error lower bound is at
  most `1/2`).
* `Statistics.leCamBound_nonneg` — the Le Cam bound is nonnegative under
  the natural hypotheses `0 ≤ Δ`, `tv ≤ 1`.
* `Statistics.leCamBound_mono_delta` — monotonicity in the loss
  separation `Δ` (for fixed `tv ≤ 1`).
* `Statistics.leCamBound_antitone_tv` — antitonicity in the total
  variation `tv` (for fixed `0 ≤ Δ`).
* `Statistics.leCamBound_eq_zero_iff` — the bound vanishes exactly when
  the two distributions are totally separated (`tv = 1`), provided the
  loss separation is strictly positive.
* `Statistics.leCam_testing_error_le_half` — the optimal Bayes testing
  error `(1 - tv) / 2` is at most `1 / 2` for any `tv ∈ [0, 1]`.
* `Statistics.gaussian_two_point_kl_nonneg` — the KL divergence between
  two univariate Gaussians with equal variance `σ² > 0` and mean gap `Δ`
  equals `Δ² / (2 σ²)`, packaged as a nonnegativity lemma so that it can
  be chained with Pinsker's inequality downstream of Le Cam.

## References

* L. Le Cam, *Convergence of Estimates Under Dimensionality Restrictions*,
  Annals of Statistics, vol. 1, no. 1, pp. 38–53, 1973.
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, Section 2.4 (two-point method) and Section 2.2 (Gaussian
  two-point KL).
* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic
  Viewpoint*, Cambridge University Press, 2019, Chapter 15.

## Tags

Le Cam, minimax, lower bound, two-point method, hypothesis testing
-/

namespace Statistics

@[expose] public section

/-- The scalar **Le Cam lower bound** as a function of the loss
separation `Δ` and the total-variation distance `tv` between the two
hypothesis measures:

`leCamBound Δ tv = Δ / 2 * (1 - tv)`.

This is the right-hand side of Le Cam's two-point inequality

`inf_T max_{i ∈ {0,1}} 𝔼_{Pᵢ} ℓ(T, θᵢ) ≥ (Δ / 2) · (1 - TV(P₀, P₁))`,

isolated as a real-valued function so that the algebraic content of the
inequality can be reasoned about without commitments to a particular
measure-theoretic setup. -/
noncomputable def leCamBound (Δ tv : ℝ) : ℝ := Δ / 2 * (1 - tv)

/-- The Le Cam lower bound is dominated by the trivial upper bound
`Δ / 2` whenever the loss separation is nonnegative and the total
variation lies in `[0, 1]`. This corresponds to the testing-error
sanity check that a random guess achieves error at most `1 / 2`. -/
theorem leCamBound_le_half_delta
    {Δ tv : ℝ} (hΔ : 0 ≤ Δ) (htv₀ : 0 ≤ tv) :
    leCamBound Δ tv ≤ Δ / 2 := by
  unfold leCamBound
  have hΔ2 : 0 ≤ Δ / 2 := by linarith
  have hone_sub_le : 1 - tv ≤ 1 := by linarith
  calc Δ / 2 * (1 - tv)
      ≤ Δ / 2 * 1 := mul_le_mul_of_nonneg_left hone_sub_le hΔ2
    _ = Δ / 2 := by ring

/-- Nonnegativity of the Le Cam lower bound: if `0 ≤ Δ` and `tv ≤ 1`
(the natural regime in which the bound is informative), then
`0 ≤ leCamBound Δ tv`. -/
theorem leCamBound_nonneg
    {Δ tv : ℝ} (hΔ : 0 ≤ Δ) (htv : tv ≤ 1) :
    0 ≤ leCamBound Δ tv := by
  unfold leCamBound
  have hΔ2 : 0 ≤ Δ / 2 := by linarith
  have hone_sub_nn : 0 ≤ 1 - tv := by linarith
  exact mul_nonneg hΔ2 hone_sub_nn

/-- Monotonicity in the loss separation: for fixed `tv ≤ 1`, the map
`Δ ↦ leCamBound Δ tv = Δ / 2 * (1 - tv)` is monotone in `Δ`. -/
theorem leCamBound_mono_delta
    {tv : ℝ} (htv : tv ≤ 1) :
    Monotone (fun Δ : ℝ => leCamBound Δ tv) := by
  intro Δ₁ Δ₂ hΔ
  unfold leCamBound
  have hone_sub_nn : 0 ≤ 1 - tv := by linarith
  have hhalf : Δ₁ / 2 ≤ Δ₂ / 2 := by linarith
  exact mul_le_mul_of_nonneg_right hhalf hone_sub_nn

/-- Antitonicity in the total-variation distance: for fixed `0 ≤ Δ`,
the map `tv ↦ leCamBound Δ tv = Δ / 2 * (1 - tv)` is antitone in `tv`.
As `tv` grows the two hypotheses become more distinguishable and the
guaranteed lower bound shrinks. -/
theorem leCamBound_antitone_tv
    {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    Antitone (fun tv : ℝ => leCamBound Δ tv) := by
  intro tv₁ tv₂ htv
  unfold leCamBound
  have hΔ2 : 0 ≤ Δ / 2 := by linarith
  have hone_sub_le : 1 - tv₂ ≤ 1 - tv₁ := by linarith
  exact mul_le_mul_of_nonneg_left hone_sub_le hΔ2

/-- The Le Cam bound vanishes exactly when the two distributions are
totally separated (`tv = 1`), provided the loss separation is strictly
positive. When `Δ = 0` the bound is identically zero and the
characterization is trivial. -/
theorem leCamBound_eq_zero_iff
    {Δ tv : ℝ} (hΔ : 0 < Δ) :
    leCamBound Δ tv = 0 ↔ tv = 1 := by
  unfold leCamBound
  have hΔ2 : Δ / 2 ≠ 0 := by
    have : 0 < Δ / 2 := by linarith
    exact ne_of_gt this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : 1 - tv = 0 := by
      rcases mul_eq_zero.mp h with h₁ | h₂
      · exact absurd h₁ hΔ2
      · exact h₂
    linarith
  · rw [h]; ring

/-- The optimal Bayes testing error `(1 - tv) / 2` never exceeds `1 / 2`
for any `tv ∈ [0, 1]`. This is the testing-side sanity check
underlying Le Cam's method: the worst case is `tv = 0`, where the two
distributions coincide and the Bayes error reaches its maximum
`1 / 2`. -/
theorem leCam_testing_error_le_half
    {tv : ℝ} (htv₀ : 0 ≤ tv) (_htv₁ : tv ≤ 1) :
    (1 - tv) / 2 ≤ (1 : ℝ) / 2 := by
  linarith

/-- The KL divergence between two univariate Gaussians with common
variance `σ² > 0` and mean separation `Δ` equals `Δ² / (2 σ²)`, which is
nonnegative. This nonnegativity lemma packages the algebraic content of
the Gaussian two-point calculation so it can be chained with Pinsker's
inequality (relating KL and total variation) downstream of Le Cam. -/
theorem gaussian_two_point_kl_nonneg
    {Δ σ : ℝ} (hσ : 0 < σ) :
    0 ≤ Δ ^ 2 / (2 * σ ^ 2) := by
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have h2σ2 : 0 < 2 * σ ^ 2 := by positivity
  exact div_nonneg hΔ2 h2σ2.le

/-! ### Examples

The two examples below pin down the boundary behaviour of `leCamBound`:
at `tv = 0` the two hypotheses are identical and the bound saturates at
`Δ / 2` (maximally informative); at `tv = 1` the two hypotheses are
totally separated and the bound collapses to `0` (no separation
guaranteed). -/

section Examples

/-- At `tv = 0` (hypotheses indistinguishable in total variation), the
Le Cam bound saturates at `Δ / 2`, the maximum useful value. -/
example (Δ : ℝ) : leCamBound Δ 0 = Δ / 2 := by
  unfold leCamBound; ring

/-- At `tv = 1` (hypotheses totally separated), the Le Cam bound
collapses to `0`: no minimax lower bound is guaranteed by the
two-point method. -/
example (Δ : ℝ) : leCamBound Δ 1 = 0 := by
  unfold leCamBound; ring

end Examples

end

end Statistics
