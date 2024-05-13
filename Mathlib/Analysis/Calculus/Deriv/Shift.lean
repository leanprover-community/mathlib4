/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
### Invariance of the derivative under translation

We show that if a function `h` has derivative `h'` at a point `a + x`, then `h (a + ·)`
has derivative `h'` at `x`. Similarly for `x + a`.
-/

/-- Translation in the domain does not change the derivative. -/
lemma HasDerivAt.comp_const_add {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a x : 𝕜) {𝕜' : Type*}
    [NormedAddCommGroup 𝕜'] [NormedSpace 𝕜 𝕜'] {h : 𝕜 → 𝕜'} {h' : 𝕜'}
    (hh : HasDerivAt h h' (a + x)) :
    HasDerivAt (fun x ↦ h (a + x)) h' x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hh <| hasDerivAt_id' x |>.const_add a

/-- Translation in the domain does not change the derivative. -/
lemma HasDerivAt.comp_add_const {𝕜 : Type*} [NontriviallyNormedField 𝕜] (x a : 𝕜) {𝕜' : Type*}
    [NormedAddCommGroup 𝕜'] [NormedSpace 𝕜 𝕜'] {h : 𝕜 → 𝕜'} {h' : 𝕜'}
    (hh : HasDerivAt h h' (x + a)) :
    HasDerivAt (fun x ↦ h (x + a)) h' x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hh <| hasDerivAt_id' x |>.add_const a

/-- The derivative of `x ↦ f (-x)` at `a` is the negative of the derivative of `f` at `-a`. -/
lemma deriv_comp_neg {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (f : 𝕜 → F) (a : 𝕜) : deriv (fun x ↦ f (-x)) a = -deriv f (-a) := by
  by_cases h : DifferentiableAt 𝕜 f (-a)
  · simpa only [deriv_neg, neg_one_smul] using deriv.scomp a h (differentiable_neg _)
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_comp_neg_iff.mpr h),
      deriv_zero_of_not_differentiableAt h, neg_zero]

/-- Translation in the domain does not change the derivative. -/
lemma deriv_comp_const_add {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a x : 𝕜) {𝕜' : Type*}
    [NormedAddCommGroup 𝕜'] [NormedSpace 𝕜 𝕜'] {h : 𝕜 → 𝕜'}
    (hh : DifferentiableAt 𝕜 h (a + x)) :
    deriv (fun x ↦ h (a + x)) x = deriv h (a + x) := HasDerivAt.deriv hh.hasDerivAt.comp_const_add

/-- Translation in the domain does not change the derivative. -/
lemma deriv_comp_add_const {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a x : 𝕜) {𝕜' : Type*}
    [NormedAddCommGroup 𝕜'] [NormedSpace 𝕜 𝕜'] {h : 𝕜 → 𝕜'}
    (hh : DifferentiableAt 𝕜 h (x + a)) :
    deriv (fun x ↦ h (x + a)) x = deriv h (x + a) := HasDerivAt.deriv hh.hasDerivAt.comp_add_const
