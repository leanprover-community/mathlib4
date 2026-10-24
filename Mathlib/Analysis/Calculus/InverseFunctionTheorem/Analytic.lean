/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Analyticity of local inverses
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}
  [CompleteSpace 𝕜] [CharZero 𝕜]

namespace AnalyticAt

/-- The local inverse of an analytic function (at a point where its derivative does not vanish)
is itself analytic. -/
lemma analyticAt_localInverse (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f x) := by
  let i : 𝕜 ≃L[𝕜] 𝕜 := .unitsEquivAut 𝕜 (.mk0 _ hf') -- multiplication by `deriv f a` as equiv
  have hfd : HasStrictFDerivAt f i.toContinuousLinearMap x := hf.hasStrictDerivAt
  let R : OpenPartialHomeomorph 𝕜 𝕜 := hfd.toOpenPartialHomeomorph _
  have hx : x ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  refine R.hasFPowerSeriesAt_symm hx hf.hasFPowerSeriesAt (i := i) ?_ |>.analyticAt
  ext
  simp [i]

end AnalyticAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E}

lemma analyticAt_comp_iff_of_deriv_ne_zero (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt 𝕜 (g ∘ f) x ↔ AnalyticAt 𝕜 g (f x) := by
  refine ⟨fun hg ↦ ?_, (AnalyticAt.comp · hf)⟩
  let r := hf.hasStrictDerivAt.localInverse _ _ _ hf'
  have hra : AnalyticAt 𝕜 r (f x) := hf.analyticAt_localInverse hf'
  have : r (f x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hg
  exact (hg.comp hra).congr <| .fun_comp (HasStrictDerivAt.eventually_right_inverse ..) g

lemma analyticAt_comp_iff_right_of_deriv_ne_zero {f : E → 𝕜} {g : 𝕜 → 𝕜} {x : E}
    (hg : AnalyticAt 𝕜 g (f x)) (hg' : deriv g (f x) ≠ 0) (hf : ContinuousAt f x) :
    AnalyticAt 𝕜 (g ∘ f) x ↔ AnalyticAt 𝕜 f x := by
  refine ⟨fun h ↦ ?_, (hg.comp ·)⟩
  let r := hg.hasStrictDerivAt.localInverse _ _ _ hg'
  have hra : AnalyticAt 𝕜 r ((g ∘ f) x) := hg.analyticAt_localInverse hg'
  exact hra.comp h |>.congr (hf.eventually <| hg.hasStrictDerivAt.eventually_left_inverse hg')

end
