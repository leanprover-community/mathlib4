/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Logarithmic Derivatives


We prove some facts about logarithmid derivatives and limits of logarithmic deriviative, for example
that the logarithmic derivative of a sequence of functions converging
locally uniformly to a function is the logarithmic derivative of the limit function. This is useful
for example for the Mittag-Leffler expansion of the cotangent function.
-/

noncomputable section

open Filter Function

open scoped Topology BigOperators Classical

section log

/-- The derivative of `log ∘ f` is the logarithmic derivative provided `f` is differentiable and
we are on the slitPlane. -/
lemma Complex.deriv_log_comp_eq_logDeriv {f : ℂ → ℂ} {x : ℂ} (h₁ : DifferentiableAt ℂ f x)
    (h₂ : f x ∈ Complex.slitPlane) : deriv (Complex.log ∘ f) x = logDeriv f x := by
  have A := (HasDerivAt.clog h₁.hasDerivAt h₂).deriv
  rw [← h₁.hasDerivAt.deriv] at A
  simp only [logDeriv, Pi.div_apply, ← A, Function.comp_def]

/-- The derivative of `log ∘ f` is the logarithmic derivative provided `f` is differentiable and
`f x  ≠ 0`. -/
lemma Real.deriv_log_comp_eq_logDeriv {f : ℝ → ℝ} {x : ℝ} (h₁ : DifferentiableAt ℝ f x)
    (h₂ : f x ≠ 0) : deriv (Real.log ∘ f) x = logDeriv f x := by
  simp only [ne_eq, logDeriv, Pi.div_apply, ← deriv.log h₁ h₂]
  rfl

end log

/-- The logarithmic derivative of a sequence of functions converging locally uniformly to a
function is the logarithmic derivative of the limit function-/
theorem logDeriv_tendsto {ι : Type*} {p : Filter ι} (f : ι → ℂ → ℂ) (g : ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : s) (hF : TendstoLocallyUniformlyOn f g p s)
    (hf : ∀ᶠ n : ι in p, DifferentiableOn ℂ (f n) s) (hg : g x ≠ 0) :
    Tendsto (fun n : ι => logDeriv (f n) x) p (𝓝 ((logDeriv g) x)) := by
  simp_rw [logDeriv]
  apply Tendsto.div ((hF.deriv hf hs).tendsto_at x.2) (hF.tendsto_at x.2) hg
