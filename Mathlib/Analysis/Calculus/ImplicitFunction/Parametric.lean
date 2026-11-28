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

open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

namespace ImplicitFunctionData

/-- A constructor for `ImplicitFunctionData` that allows us to simultaneously apply the theorem
to an indexed family of functions. -/
@[simps -fullyApplied leftFun leftDeriv pt, simps -isSimp rightFun rightDeriv]
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
    rw [← top_le_iff, ← hdf, fderiv_fun_comp_prodMk, ContinuousLinearMap.toLinearMap_comp]
    · exact LinearMap.range_comp_le_range _ _
    · exact hfa.hasFDerivAt.differentiableAt
  range_rightDeriv := by simp [LinearMap.range_eq_of_proj hprojKer]
  isCompl_ker := by
    have H : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2 : F →ₗ[𝕜] G) = fderiv 𝕜 f a ∘ₗ .inr 𝕜 E F := by
      simp [fderiv_fun_comp_prodMk hfa.hasFDerivAt.differentiableAt]
    suffices IsCompl (fderiv 𝕜 f a).ker (.prod ⊥ projKer.ker) by simpa [LinearMap.ker_prodMap]
    apply Submodule.isCompl_prod_right
    · convert isCompl_top_bot
      rw [LinearMap.map_fst_ker_eq_top, ← H, hdf]
      apply le_top
    · simpa [H, LinearMap.ker_comp] using projKer.isCompl_of_proj hprojKer

theorem rightDeriv_parametric_apply_ker' {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x)
    (x : E) {y : F} (hy : fderiv 𝕜 (fun z ↦ f (a.1, z)) a.2 y = 0) :
    (parametric f a hfa hdf projKer hprojKer).rightDeriv (x, y) = (x, ⟨y, hy⟩) := by
  simpa [parametric] using hprojKer ⟨y, _⟩

theorem rightDeriv_parametric_apply_ker {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x)
    (x : E) {y : F} (hy : fderiv 𝕜 f a (0, y) = 0) :
    (parametric f a hfa hdf projKer hprojKer).rightDeriv (x, y) =
      (x, ⟨y, by simpa [fderiv_fun_comp_prodMk hfa.hasFDerivAt.differentiableAt]⟩) :=
  rightDeriv_parametric_apply_ker' hfa hdf projKer hprojKer x _

theorem fst_implicitFunction_parametric_eventuallyEq_fst_snd {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    letI φ := (parametric f a hfa hdf projKer hprojKer).implicitFunction
    (fun z ↦ (φ z.1 z.2).fst) =ᶠ[𝓝 (f a, a.1, projKer a.2)] fun z ↦ z.2.1 := by
  simpa [Filter.EventuallyEq, parametric_rightFun, Prod.map_apply']
    using Filter.EventuallyEq.fun_comp
      (parametric f a hfa hdf projKer hprojKer).rightFun_implicitFunction (·.1)

theorem fst_implicitFunction_parametric_eventuallyEq_fst {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    letI φ := (parametric f a hfa hdf projKer hprojKer).implicitFunction
    (fun z ↦ (φ (f a) z).fst) =ᶠ[𝓝 (a.1, projKer a.2)] Prod.fst :=
  fst_implicitFunction_parametric_eventuallyEq_fst_snd hfa hdf projKer hprojKer
    |>.comp_tendsto (tendsto_const_nhds.prodMk_nhds Filter.tendsto_id)

theorem apply_implicitFunction_parametric_eventuallyEq_fst {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    letI φ := (parametric f a hfa hdf projKer hprojKer).implicitFunction
    (fun z ↦ f (φ z.1 z.2)) =ᶠ[𝓝 (f a, a.1, projKer a.2)] Prod.fst := by
  simpa [Filter.EventuallyEq, parametric_rightFun, Prod.map_apply']
    using (parametric f a hfa hdf projKer hprojKer).leftFun_implicitFunction

theorem apply_implicitFunction_parametric_eventuallyEq_const {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    letI φ := (parametric f a hfa hdf projKer hprojKer).implicitFunction
    (fun z ↦ f (φ (f a) z)) =ᶠ[𝓝 (a.1, projKer a.2)] fun _ ↦ f a :=
  apply_implicitFunction_parametric_eventuallyEq_fst hfa hdf projKer hprojKer
    |>.comp_tendsto (tendsto_const_nhds.prodMk_nhds Filter.tendsto_id)

end ImplicitFunctionData
