/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Submanifold
public import Mathlib.Geometry.Manifold.RegularPoint

/-! # The regular value theorem

to be written!
-/

public section

open scoped ContDiff
open Manifold Topology Function Set

universe u
-- Let `M` and `N` be `C^n` manifolds over a field `𝕜`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ E₄ E₅ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₄]
  [NormedAddCommGroup E₅] [NormedSpace 𝕜 E₅]
  {H H' H'' G G' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E₁ H} {I' : ModelWithCorners 𝕜 E₂ H'}
  {J : ModelWithCorners 𝕜 E₃ G} {J' : ModelWithCorners 𝕜 E₄ G'} {J'' : ModelWithCorners 𝕜 E₅ H''}
  {M M' N N' P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  [TopologicalSpace P] [ChartedSpace H'' P]
  {n : WithTop ℕ∞}
  {F F' : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-

Finite-dimensional versions:
- constant rank theorem; differential has constant rank
- standard version: differential is surjective everyhere
- conceptual version: differential (is surjective and) has a bounded right inverse

-/

public noncomputable section

variable {f : M → N}

variable (I) in
def ModelWithCorners.restrictPreimage (M : Submodule 𝕜 E₁) : ModelWithCorners 𝕜 M (I ⁻¹' M) where
  toPartialEquiv.toFun := Set.restrictPreimage M I
  toPartialEquiv.invFun := Set.MapsTo.restrict I.symm _ _ fun x hx ↦ sorry
  toPartialEquiv.source := sorry
  toPartialEquiv.target := sorry
  toPartialEquiv.map_source' := sorry
  toPartialEquiv.map_target' := sorry
  toPartialEquiv.left_inv' := sorry
  toPartialEquiv.right_inv' := sorry
  source_eq := sorry
  convex_range' := sorry
  nonempty_interior' := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

-- Should this include a differentiability assumption? Then
-- there is no need to manually also pass the `ContMDiff` below.
variable (I J) in
@[expose]
def IsRegularValue (f : M → N) (y : N) := ∀ x ∈ f ⁻¹' {y}, IsRegularPoint I J f x

-- Suppose M is not empty. (Otherwise, we can do anything we want.)
-- Pick a pre-image x of y. Then mfderiv has a bounded right inverse;
-- take the image of that right inverse.

@[expose]
def IsRegularValue.Complement {x : M} (hx : IsRegularValue I J f (f x)) : Type _ :=
  (hx x rfl).choose.range
  deriving NormedAddCommGroup

namespace IsRegularValue

instance {x : M} (hx : IsRegularValue I J f (f x)) : NormedSpace 𝕜 hx.Complement := by
  delta Complement
  infer_instance

/-- The set `f ⁻¹' {f x}` coerced to a type that will be endowed with a manifold
structure by the regular value theorem. -/
@[nolint unusedArguments, expose]
abbrev Preimage {x : M} (_hx : IsRegularValue I J f (f x)) (_hf : ContMDiff I J n f) : Type _ :=
  f ⁻¹' {f x}

/-- The model normed space for the manifold structure on `f ⁻¹' {f x}`. -/
@[nolint unusedArguments, expose]
def modelSpace {x : M} (_hx : IsRegularValue I J f (f x)) : Type _ :=
  (mfderiv I J f x).ker

instance {x : M} (hx : IsRegularValue I J f (f x)) :
    NormedAddCommGroup hx.modelSpace := by
  unfold modelSpace
  infer_instance

instance {x : M} (hx : IsRegularValue I J f (f x)) :
    NormedSpace 𝕜 hx.modelSpace := by
  unfold modelSpace
  letI : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs <| NormedAddCommGroup E₁
  letI : NormedSpace 𝕜 (TangentSpace I x) := inferInstanceAs <| NormedSpace _ E₁
  infer_instance

namespace sandbox

@[nolint unusedArguments, expose]
def model {x : M} (_hx : IsRegularValue I J f (f x)) : Type _ :=
  I ⁻¹' ((mfderiv I J f x).ker : Set (TangentSpace I x))
  deriving TopologicalSpace

@[nolint unusedArguments, expose]
def modelWithCorners {x : M} (hx : IsRegularValue I J f (f x)) :
    ModelWithCorners 𝕜 hx.modelSpace (sandbox.model hx) :=
  letI : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs <| NormedAddCommGroup E₁
  letI : NormedSpace 𝕜 (TangentSpace I x) := inferInstanceAs <| NormedSpace _ E₁
  .restrictPreimage _ _

/-- The regular value theorem. -/
def immersedSubmanifold {x : M} (hx : IsRegularValue I J f (f x))
    (hf : ContMDiff I J n f) :
    ImmersedSubmanifold (sandbox.modelWithCorners hx) I (hx.Preimage hf) M n hx.Complement where
  map := Subtype.val
  sliceModel.equiv := sorry
  sliceModel.map := Subtype.val
  sliceModel.hmap := .subtypeVal
  sliceModel.compatible := sorry
  real_condition := sorry

instance {x : M} (hx : IsRegularValue I J f (f x)) (hf : ContMDiff I J n f) :
    ChartedSpace (sandbox.model hx) (hx.Preimage hf) :=
  (immersedSubmanifold hx hf).chartedSpace

end sandbox

-- Let us assume we have a boundaryless manifold: otherwise, the mathematics is less clear for now.
section Boundaryless

/-- In a boundaryless manifold, the trivial model with corners is a fine choice. -/
@[nolint unusedArguments, expose]
def modelWithCorners {x : M} (hx : IsRegularValue I J f (f x)) :
    ModelWithCorners 𝕜 hx.modelSpace hx.modelSpace :=
  𝓘(𝕜, _)

/-- The regular value theorem. -/
instance immersedSubmanifold [I.Boundaryless] {x : M} (hx : IsRegularValue I J f (f x))
    (hf : ContMDiff I J n f) :
    ImmersedSubmanifold hx.modelWithCorners I (hx.Preimage hf) M n hx.Complement where
  map := Subtype.val
  sliceModel := sorry -- should be a known condition
  real_condition := sorry

instance [I.Boundaryless] {x : M} (hx : IsRegularValue I J f (f x)) (hf : ContMDiff I J n f) :
    ChartedSpace hx.modelSpace (hx.Preimage hf) :=
  (hx.immersedSubmanifold hf).chartedSpace

end Boundaryless

end IsRegularValue
