/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Implicit

/-!
# Implicit function theorem for a parametric family of functions

Implicit function theorem says that a strictly differentiable function
with a surjective Fréchet derivative is conjugate
to a linear projection along the kernel of the derivative.
The smoothness of the conjugating map is the same as the smoothness of the original function.

In Mathlib, the theorem is formalized using an auxiliary structure `ImplicitFunctionData`
that allows us to explicitly choose a linear projection of the domain
onto the kernel of the derivative.

In this file we provide a constructor for `ImplicitFunctionData` that works well
for parametrized families of functions.

Namely, let `f : E × F → G` be a function such that `∂f/∂y` is surjective,
where `∂f/∂y` is defined as the derivative of `fun y ↦ f (x, y)` for a fixed `x`.
Then one can find an implicit function that preserves the first coordinate.

In these settings, we think about this function as a family of functions indexed by `x : X`,
so we can think about this construction as simultaneous application of the implicit function theorem
to all the functions `fun y ↦ f (x, y)` with some extra guarantees
about dependency on the parameter.

-/

@[expose] public noncomputable section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

namespace ImplicitFunctionData

/-- A constructor for `ImplicitFunctionData` that allows us to simultaneously apply the theorem
to an indexed family of functions. -/
@[simps -fullyApplied leftFun leftDeriv pt]
def parametric
    (f : E × F → G) (a : E × F)
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    ImplicitFunctionData 𝕜 (E × F) G (E × (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker) where
  leftFun := f
  leftDeriv := fderiv 𝕜 f a
  hasStrictFDerivAt_leftFun := hfa
  rightFun := Prod.map id projKer
  rightDeriv := .prodMap (.id 𝕜 E) projKer
  hasStrictFDerivAt_rightFun := ContinuousLinearMap.hasStrictFDerivAt (.prodMap (.id 𝕜 E) projKer)
  pt := a
  range_leftDeriv := by
    rw [← top_le_iff, ← hdf, fderiv_fun_comp_prodMk, ContinuousLinearMap.coe_comp]
    · exact LinearMap.range_comp_le_range _ _
    · exact hfa.hasFDerivAt.differentiableAt
  range_rightDeriv := by simp [LinearMap.range_eq_of_proj hprojKer]
  isCompl_ker := by
    have H := congr($(fderiv_fun_comp_prodMk hfa.hasFDerivAt.differentiableAt).toLinearMap)
    push_cast [Prod.eta] at H
    suffices IsCompl (fderiv 𝕜 f a).ker (.prod ⊥ projKer.ker) by simpa [LinearMap.ker_prodMap]
    apply Submodule.isCompl_prod_right
    · convert isCompl_top_bot
      rw [LinearMap.map_fst_ker_eq_top, ← H, hdf]
      apply le_top
    · simpa [H] using projKer.isCompl_of_proj hprojKer

theorem rightDeriv_parametric_apply_ker' (f : E × F → G) (a : E × F)
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x)
    (x : E) {y : F} (hy : fderiv 𝕜 (fun z ↦ f (a.1, z)) a.2 y = 0) :
    (parametric f a hfa hdf projKer hprojKer).rightDeriv (x, y) = (x, ⟨y, hy⟩) := by
  simpa [parametric] using hprojKer ⟨y, _⟩

theorem rightDeriv_parametric_apply_ker
    (f : E × F → G) (a : E × F)
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x)
    (x : E) {y : F} (hy : fderiv 𝕜 f a (0, y) = 0) :
    (parametric f a hfa hdf projKer hprojKer).rightDeriv (x, y) =
      (x, ⟨y, by simpa [fderiv_fun_comp_prodMk hfa.hasFDerivAt.differentiableAt]⟩) :=
  rightDeriv_parametric_apply_ker' f a hfa hdf projKer hprojKer x _

end ImplicitFunctionData
