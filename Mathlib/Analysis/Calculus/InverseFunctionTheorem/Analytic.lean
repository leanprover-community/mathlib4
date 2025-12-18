/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Analyticity of local inverses
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {a : 𝕜}

namespace AnalyticAt

lemma hasStrictDerivAt (hf : AnalyticAt 𝕜 f a) : HasStrictDerivAt f (deriv f a) a := by
  rw [hasStrictDerivAt_iff_hasStrictFDerivAt]
  simpa [deriv_fderiv] using hf.hasStrictFDerivAt

variable [CompleteSpace 𝕜] [CharZero 𝕜]

/-- The local inverse of an analytic function (at a point where its derivative does not vanish)
is itself analytic. -/
lemma analyticAt_localInverse (hf : AnalyticAt 𝕜 f a) (hf' : deriv f a ≠ 0) :
    AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f a) := by
  have hfd : HasStrictFDerivAt f
    (((ContinuousLinearEquiv.unitsEquivAut 𝕜) (Units.mk0 _ hf'))).toContinuousLinearMap
    a := hf.hasStrictDerivAt
  let R := hfd.toOpenPartialHomeomorph _
  have ha : a ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  refine R.hasFPowerSeriesAt_symm ha hf.hasFPowerSeriesAt
      (i := (ContinuousLinearEquiv.unitsEquivAut 𝕜) (.mk0 _ hf')) ?_ |>.analyticAt
  ext
  simp

end AnalyticAt
