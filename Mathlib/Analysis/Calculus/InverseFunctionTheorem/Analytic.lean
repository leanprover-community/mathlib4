/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

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

end
