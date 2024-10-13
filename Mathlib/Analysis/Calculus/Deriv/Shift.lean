/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Yaël Dillies
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
### Invariance of the derivative under translation

We show that if a function `f` has derivative `f'` at a point `a + x`, then `f (a + ·)`
has derivative `f'` at `x`. Similarly for `x + a`.
-/

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : 𝕜 → F} {f' : F}

/-- Translation in the domain does not change the derivative. -/
lemma HasDerivAt.comp_const_add (a x : 𝕜) (hf : HasDerivAt f f' (a + x)) :
    HasDerivAt (fun x ↦ f (a + x)) f' x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf <| hasDerivAt_id' x |>.const_add a

/-- Translation in the domain does not change the derivative. -/
lemma HasDerivAt.comp_add_const (x a : 𝕜) (hf : HasDerivAt f f' (x + a)) :
    HasDerivAt (fun x ↦ f (x + a)) f' x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf <| hasDerivAt_id' x |>.add_const a

/-- Translation in the domain does not change the derivative. -/
lemma HasDerivAt.comp_const_sub (a x : 𝕜) (hf : HasDerivAt f f' (a - x)) :
    HasDerivAt (fun x ↦ f (a - x)) (-f') x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf <| hasDerivAt_id' x |>.const_sub a

/-- Translation in the domain does not change the derivative. -/
lemma HasDerivAt.comp_sub_const (x a : 𝕜) (hf : HasDerivAt f f' (x - a)) :
    HasDerivAt (fun x ↦ f (x - a)) f' x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf <| hasDerivAt_id' x |>.sub_const a

variable (f) (a x : 𝕜)

/-- The derivative of `x ↦ f (-x)` at `a` is the negative of the derivative of `f` at `-a`. -/
lemma deriv_comp_neg : deriv (fun x ↦ f (-x)) x = -deriv f (-x) := by
  by_cases f : DifferentiableAt 𝕜 f (-x)
  · simpa only [deriv_neg, neg_one_smul] using deriv.scomp _ f (differentiable_neg _)
  · rw [deriv_zero_of_not_differentiableAt (differentiableAt_comp_neg.not.2 f),
      deriv_zero_of_not_differentiableAt f, neg_zero]

/-- Translation in the domain does not change the derivative. -/
lemma deriv_comp_const_add : deriv (fun x ↦ f (a + x)) x = deriv f (a + x) := by
  by_cases hf : DifferentiableAt 𝕜 f (a + x)
  · exact HasDerivAt.deriv hf.hasDerivAt.comp_const_add
  · rw [deriv_zero_of_not_differentiableAt (differentiableAt_comp_const_add.not.2 hf),
      deriv_zero_of_not_differentiableAt hf]

/-- Translation in the domain does not change the derivative. -/
lemma deriv_comp_add_const : deriv (fun x ↦ f (x + a)) x = deriv f (x + a) := by
  simpa [add_comm] using deriv_comp_const_add f a x

lemma deriv_comp_const_sub : deriv (fun x ↦ f (a - x)) x = -deriv f (a - x) := by
  simp_rw [sub_eq_add_neg, deriv_comp_neg (f <| a + ·), deriv_comp_const_add]

lemma deriv_comp_sub_const : deriv (fun x ↦ f (x - a)) x = deriv f (x - a) := by
  simp_rw [sub_eq_add_neg, deriv_comp_add_const]
