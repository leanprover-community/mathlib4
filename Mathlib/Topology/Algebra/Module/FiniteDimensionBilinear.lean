/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Building continuous bilinear maps in finite dimensions over complete fields

Given a complete nontrivially normed field `𝕜` and finite dimensional T₂ topological vector spaces
over `𝕜`, this file builds a continuous bilinear map from any bilinear function.

This applies in particular to evaluation of linear maps between such spaces.

Working with topological vector spaces instead of normed spaces is important for applications in the
differential geometry part of Mathlib where we don’t want to fix a norm on tangent spaces for
instance.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

variable
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T2Space E]
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F] [T2Space F]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]

/-- Building continuous bilinear maps from bilinear maps between finite dimensional topological
  vector spaces over a complete field. -/
def LinearMap.toContinuousBilinearMap (f : E →ₗ[𝕜] F →ₗ[𝕜] G) : E →L[𝕜] F →L[𝕜] G :=
  IsLinearMap.mk' (fun x : E ↦ f x |>.toContinuousLinearMap)
      (by constructor <;> (intros; simp)) |>.toContinuousLinearMap

@[simp]
lemma LinearMap.toContinuousBilinearMap_apply (f : E →ₗ[𝕜] F →ₗ[𝕜] G) (x : E) (y : F) :
  f.toContinuousBilinearMap x y = f x y := rfl

/-- Building continuous bilinear maps from bilinear functions between finite dimensional topological
  vector spaces over a complete field. -/
def IsBilinearMap.toContinuousBilinearMap
    {f : E → F → G} (h : IsBilinearMap 𝕜 f) : E →L[𝕜] F →L[𝕜] G :=
  h.toLinearMap.toContinuousBilinearMap

@[simp]
lemma IsBilinearMap.toContinuousBilinearMap_apply {f : E → F → G} (h : IsBilinearMap 𝕜 f)
    (x : E) (y : F) :
  h.toContinuousBilinearMap x y = f x y := rfl

variable (𝕜 E F) in
/-- Evaluation of continuous linear maps as a continuous linear map in the
case of finite dimensional topological vector spaces over a complete field.
See also `ContinuousLinearMap.apply` for the case of normed spaces.

TODO: generalize the two constructions in the setting of maps from a bornological space to a locally
convex one, or define a `NormableSpace` class to deduce this case from the normed case.
-/
def ContinuousLinearMap.evalL : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F :=
  LinearMap.toContinuousLinearMap.symm.toLinearMap |>.flip |>.toContinuousBilinearMap

@[simp]
lemma ContinuousLinearMap.evalL_apply (x : E) (φ : E →L[𝕜] F) : φ.evalL 𝕜 E F x = φ x := rfl
