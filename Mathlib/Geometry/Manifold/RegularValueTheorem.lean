/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Submanifold
public import Mathlib.Geometry.Manifold.RegularPoint
public import Mathlib.Geometry.Manifold.Submersion

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

section move

variable {x : M}

lemma IsRegularPoint.isSubmersionAt (hx : IsRegularPoint I J f x) :
    IsSubmersionAt I J n f x := by
  sorry

lemma IsSubmersionAt.isRegularPoint (hf : IsSubmersionAt I J n f x) : IsRegularPoint I J f x := by
  sorry

end move

-- Should this include a differentiability assumption? Then
-- there is no need to manually also pass the `ContMDiff` below.
variable (I J) in
@[expose]
def IsRegularValue (f : M → N) (y : N) := ∀ x ∈ f ⁻¹' {y}, IsRegularPoint I J f x

/-- If `f` is a submersion, every point in `y` is a regular value of `f`. -/
lemma IsSubmersion.isRegularValue (hf : IsSubmersion I J n f) (y : N) : IsRegularValue I J f y :=
  fun x _hx ↦ (hf.isSubmersionAt x).isRegularPoint

namespace IsRegularValue

-- Suppose M is not empty. (Otherwise, we can do anything we want.)
-- Pick a pre-image x of y. Then mfderiv has a bounded right inverse;
-- take the image of that right inverse.

/-- A complement in the model normed spaces `E` of `M` for the regular value `f x`. -/
@[expose]
def Complement {x : M} (hx : IsRegularValue I J f (f x)) : Type _ :=
  (hx x rfl).choose.range
  deriving NormedAddCommGroup

/-- A complement in the model normed spaces `E` of `M` for an arbitrary regular value `y`.
If `y` is not in the range of `f`, we simply take the trivial normed space. -/
@[expose] def Complement' {y : N} (hy : IsRegularValue I J f y) : Type _ := by
  classical exact if h : y ∈ range f then (h.choose_spec ▸ hy).Complement else PUnit

instance {y : N} (hy : IsRegularValue I J f y) : NormedAddCommGroup hy.Complement' := by
  by_cases h : y ∈ range f
  · simp only [Complement', h, ↓reduceDIte]; infer_instance
  simp only [Complement', h, ↓reduceDIte]
  infer_instance

instance {x : M} (hx : IsRegularValue I J f (f x)) : NormedSpace 𝕜 hx.Complement := by
  delta Complement
  infer_instance

-- TODO: expanding the definition of Complement' does not seem to work, at all!
instance {y : N} (hy : IsRegularValue I J f y) : NormedSpace 𝕜 hy.Complement' := by
  by_cases h : y ∈ range f
  · simp [Complement', h]
    --have : NormedSpace 𝕜 (h.choose_spec ▸ hy).Complement := sorry
    sorry
  simp only [Complement'] --, h, ↓reduceDIte]
  sorry

--- XXX(MR): do we really need _hf here?
/-- The set `f ⁻¹' {f x}` coerced to a type that will be endowed with a manifold
structure by the regular value theorem. -/
@[nolint unusedArguments, expose]
abbrev Preimage {x : M} (_hx : IsRegularValue I J f (f x)) (_hf : ContMDiff I J n f) : Type _ :=
  f ⁻¹' {f x}

/-
--- XXX(MR): do we really need _hf here?
@[nolint unusedArguments, expose]
abbrev PreimageWithin {x : M} (_hx : IsRegularValue I J f (f x)) (_hf : ContMDiff I J n f) (s : Set M) : Type _ :=
  (s ∩ (f ⁻¹' {f x})) -/

-- @[simp] lemma preimageWithin_univ {x : M} (_hx : IsRegularValue I J f (f x)) (_hf : ContMDiff I J n f) :
--  PreimageWithin _hx _hf univ = Preimage _hx _hf := sorry

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

variable (I) in
def _root_.ModelWithCorners.restrictPreimage (M : Submodule 𝕜 E₁) : ModelWithCorners 𝕜 M (I ⁻¹' M) where
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

variable {x : M}
/- Idea of proof: if x is a regular point of f, then f is a submersion at x.
The submersion's given charts induce a slice chart,
making f ⁻¹' {f x} ∩ chart source a charted space.
(XXX: do we need to shrink the source to ensure f ⁻¹ f x has only one component belonging to x?
 Maybe not!) -/
-- Let's state this for a regular value, just to be safe.
-- -- lemma intuition (hx : IsRegularPoint I J f x) :
-- lemma intuition (hx : IsRegularValue I J f (f x)) :
--  ChartedSpace (PreimageWithin f v hx.isSubmersionAt.domChart.source) hx.modelSpace := sorry

/-- In a boundaryless manifold, the trivial model with corners is a fine choice. -/
@[nolint unusedArguments, expose]
def modelWithCorners {x : M} (hx : IsRegularValue I J f (f x)) :
    ModelWithCorners 𝕜 hx.modelSpace hx.modelSpace :=
  𝓘(𝕜, _)

/-- The **regular value theorem** for boundaryless manifolds, main case:
for a regular value `y` of `f` which lies in `range f`. -/
def immersedSubmanifold_aux [I.Boundaryless] {x : M} (hx : IsRegularValue I J f (f x))
    (hf : ContMDiff I J n f) :
    ImmersedSubmanifold hx.modelWithCorners I (hx.Preimage hf) M n hx.Complement where
  map := Subtype.val
  sliceModel := sorry -- should be a known condition
  real_condition := sorry

/-- The **regular value theorem** for boundaryless manifolds, for any regular `y` of `f`. -/
instance immersedSubmanifold [I.Boundaryless] {y : N} (hy : IsRegularValue I J f y)
    (hf : ContMDiff I J n f) :
    -- hy.Preimage hf does not typecheck yet!
    ImmersedSubmanifold hy.modelWithCorners I (hy.Preimage hf) M n hy.Complement' := by
  sorry

/-- The regular value theorem. -/
instance immersedSubmanifold [I.Boundaryless] {x : M} (hx : IsRegularValue I J f (f x))
    (hf : ContMDiff I J n f) :
    ImmersedSubmanifold hx.modelWithCorners I (hx.Preimage hf) M n hx.Complement where
  map := Subtype.val
  sliceModel := sorry -- should be a known condition
  real_condition := sorry

instance [I.Boundaryless] (hx : IsRegularValue I J f (f x)) (hf : ContMDiff I J n f) :
    ChartedSpace hx.modelSpace (hx.Preimage hf) :=
  (hx.immersedSubmanifold hf).chartedSpace

instance [I.Boundaryless] {x : M} (hx : IsRegularValue I J f (f x)) (hf : ContMDiff I J n f) :
    IsManifold hx.modelWithCorners n (hx.Preimage hf) :=
  (hx.immersedSubmanifold hf).isManifold

-- ideally, this would not be necessary
abbrev inclusion (hx : IsRegularValue I J f (f x)) (hf : ContMDiff I J n f) : (hx.Preimage hf) → M :=
    fun x ↦ x.val

lemma foo [I.Boundaryless] (hx : IsRegularValue I J f (f x)) (hf : ContMDiff I J n f) :
    IsSmoothEmbedding hx.modelWithCorners I n (hx.inclusion hf) :=
  sorry -- general submanifold nonsense

end Boundaryless

end IsRegularValue
