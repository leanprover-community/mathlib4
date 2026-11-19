/-
Copyright (c) 2026 Meshal Alawein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Meshal Alawein
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ConditionalProbability

import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The CHSH inequality for bounded random variables

This file proves the Clauser-Horne-Shimony-Holt (CHSH) inequality in its probabilistic form.
If `A₀ A₁ B₀ B₁` are real random variables on a probability space, each bounded by `1` in
absolute value, then the CHSH combination of the correlations `𝔼[Aᵢ * Bⱼ]` has absolute value
at most `2`. Physically, the random variables are the outcomes of a local hidden-variable model,
with the sample space playing the role of the hidden variable.

## Main statements

* `ProbabilityTheory.abs_chsh_integral_le_two`: the CHSH inequality for bounded random variables.
* `ProbabilityTheory.abs_chsh_integral_cond_le_two`: the same bound for the conditional measure
  `μ[|s]` on an event `s` of positive measure.

## Implementation notes

The proof integrates the pointwise bound
`|a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁| ≤ 2`, valid whenever `|a₀|, |a₁|, |b₀|, |b₁| ≤ 1`.
See `Mathlib/Algebra/Star/CHSH.lean` for the operator-algebraic counterpart, which states the
inequality for commuting self-adjoint involutions in an ordered `*`-ring, together with
Tsirelson's bound in the noncommutative case.

## References

* [Clauser, Horne, Shimony, Holt,
  *Proposed experiment to test local hidden-variable theories*][zbMATH06785026]

## Tags

CHSH inequality, Bell inequality, local hidden variables
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **CHSH inequality** for bounded random variables: if `A₀ A₁ B₀ B₁` are real random
variables bounded by `1` in absolute value, then
`|𝔼[A₀ B₀] + 𝔼[A₀ B₁] + 𝔼[A₁ B₀] - 𝔼[A₁ B₁]| ≤ 2`. -/
theorem abs_chsh_integral_le_two (μ : Measure Ω) [IsProbabilityMeasure μ] {A₀ A₁ B₀ B₁ : Ω → ℝ}
    (hA₀m : AEStronglyMeasurable A₀ μ) (hA₁m : AEStronglyMeasurable A₁ μ)
    (hB₀m : AEStronglyMeasurable B₀ μ) (hB₁m : AEStronglyMeasurable B₁ μ)
    (hA₀ : ∀ ω, |A₀ ω| ≤ 1) (hA₁ : ∀ ω, |A₁ ω| ≤ 1)
    (hB₀ : ∀ ω, |B₀ ω| ≤ 1) (hB₁ : ∀ ω, |B₁ ω| ≤ 1) :
    |(∫ ω, A₀ ω * B₀ ω ∂μ) + (∫ ω, A₀ ω * B₁ ω ∂μ) + (∫ ω, A₁ ω * B₀ ω ∂μ) -
      ∫ ω, A₁ ω * B₁ ω ∂μ| ≤ 2 := by
  have hint : ∀ {f g : Ω → ℝ}, AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
      (∀ ω, |f ω| ≤ 1) → (∀ ω, |g ω| ≤ 1) → Integrable (fun ω ↦ f ω * g ω) μ :=
    fun hf hg hf₁ hg₁ ↦ .of_bound (hf.mul hg) 1 <| ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hf₁ ω) (hg₁ ω) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have h₀₀ := hint hA₀m hB₀m hA₀ hB₀
  have h₀₁ := hint hA₀m hB₁m hA₀ hB₁
  have h₁₀ := hint hA₁m hB₀m hA₁ hB₀
  have h₂ : Integrable (fun ω ↦ A₀ ω * B₀ ω + A₀ ω * B₁ ω) μ := h₀₀.add h₀₁
  have h₃ : Integrable (fun ω ↦ A₀ ω * B₀ ω + A₀ ω * B₁ ω + A₁ ω * B₀ ω) μ := h₂.add h₁₀
  rw [← integral_add h₀₀ h₀₁, ← integral_add h₂ h₁₀,
    ← integral_sub h₃ (hint hA₁m hB₁m hA₁ hB₁)]
  have hb : ∀ ω, ‖A₀ ω * B₀ ω + A₀ ω * B₁ ω + A₁ ω * B₀ ω - A₁ ω * B₁ ω‖ ≤ 2 := fun ω ↦ by
    obtain ⟨ha₀, ha₀'⟩ := abs_le.1 (hA₀ ω)
    obtain ⟨ha₁, ha₁'⟩ := abs_le.1 (hA₁ ω)
    obtain ⟨hb₀, hb₀'⟩ := abs_le.1 (hB₀ ω)
    obtain ⟨hb₁, hb₁'⟩ := abs_le.1 (hB₁ ω)
    rw [Real.norm_eq_abs, abs_le]
    rcases le_total 0 (B₀ ω + B₁ ω) with h | h <;>
    rcases le_total 0 (B₀ ω - B₁ ω) with h' | h' <;>
    constructor <;> nlinarith
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hb)

/-- The **CHSH inequality** for bounded random variables under the conditional measure `μ[|s]`
on an event `s` of positive measure. -/
theorem abs_chsh_integral_cond_le_two (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A₀ A₁ B₀ B₁ : Ω → ℝ}
    (hA₀m : AEStronglyMeasurable A₀ μ) (hA₁m : AEStronglyMeasurable A₁ μ)
    (hB₀m : AEStronglyMeasurable B₀ μ) (hB₁m : AEStronglyMeasurable B₁ μ)
    (hA₀ : ∀ ω, |A₀ ω| ≤ 1) (hA₁ : ∀ ω, |A₁ ω| ≤ 1)
    (hB₀ : ∀ ω, |B₀ ω| ≤ 1) (hB₁ : ∀ ω, |B₁ ω| ≤ 1)
    {s : Set Ω} (hμs : μ s ≠ 0) :
    |(∫ ω, A₀ ω * B₀ ω ∂μ[|s]) + (∫ ω, A₀ ω * B₁ ω ∂μ[|s]) + (∫ ω, A₁ ω * B₀ ω ∂μ[|s]) -
      ∫ ω, A₁ ω * B₁ ω ∂μ[|s]| ≤ 2 := by
  have := cond_isProbabilityMeasure (μ := μ) hμs
  have hac : μ[|s] ≪ μ := cond_absolutelyContinuous
  exact abs_chsh_integral_le_two μ[|s] (hA₀m.mono_ac hac) (hA₁m.mono_ac hac)
    (hB₀m.mono_ac hac) (hB₁m.mono_ac hac) hA₀ hA₁ hB₀ hB₁

end ProbabilityTheory
