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

TODO: flesh out this doc-string; a few notes

- general version, for a regular value
- specialisation for finite dimensions (over a complete field): differential is surjective

- constant rank theorem: rank of the differential is constant

Full sorry-free statements require ironing out the definition of immersed and embedded submanifolds.

## Implementation notes

* currently, all statements assume a boundaryless manifold: in that case, the proof essentially
  follows from the characterisation of submersions by a split differential
* for manifolds with boundary, the statement and proof need to be adapted: the regular value `y`
  should be an interior point of the target, and we also require `y` to be a regular value of
  `f` restricted to the boundary. (This only makes sense if the boundary of `M` is a smooth
  manifold; for corners, even more care is needed.)
  Formalising this will require a notion of manifolds with smooth boundary and no corners
  (which is being worked on).
  In the medium-term, this theorem may be proven separately for particular models with boundary.
  Mathlib's definition of manifolds with boundary and corners might be too general to easily handle.

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

public noncomputable section

variable {f : M → N}

variable (I J) in
@[expose]
def IsRegularValue (f : M → N) (y : N) := ∀ x ∈ f ⁻¹' {y}, IsRegularPoint I J f x

/-- If `f` is a submersion, every point in `y` is a regular value of `f`. -/
lemma IsSubmersion.isRegularValue (hf : IsSubmersion I J n f) (y : N) : IsRegularValue I J f y :=
  fun x _hx ↦ (hf.isSubmersionAt x).isRegularPoint

namespace IsRegularValue

variable {x : M} {y : N}

-- Suppose M is not empty. (Otherwise, we can do anything we want.)
-- Pick a pre-image x of y. Then mfderiv has a bounded right inverse;
-- take the image of that right inverse.

/-- A complement in the model normed spaces `E` of `M` for the regular value `f x`. -/
@[expose]
def Complement (hx : IsRegularValue I J f (f x)) : Type _ :=
  (hx x rfl).choose.range
  deriving NormedAddCommGroup

/-- A complement in the model normed spaces `E` of `M` for an arbitrary regular value `y`.
If `y` is not in the range of `f`, we simply take the trivial normed space. -/
@[expose] def Complement' {y : N} (hy : IsRegularValue I J f y) : Type _ :=
  open scoped Classical in
  if h : y ∈ range f then (h.choose_spec ▸ hy).Complement else PUnit

instance (hy : IsRegularValue I J f y) : NormedAddCommGroup hy.Complement' := by
  by_cases h : y ∈ range f <;> simp only [Complement', h, ↓reduceDIte] <;> infer_instance

instance (hx : IsRegularValue I J f (f x)) : NormedSpace 𝕜 hx.Complement := by
  delta Complement
  infer_instance

-- TODO: expanding the definition of Complement' does not seem to work, at all!
instance (hy : IsRegularValue I J f y) : NormedSpace 𝕜 hy.Complement' := by
  classical
  /-
  -- issue: the motive depends on the parameter; NormedSpace 𝕜 x depends on x in that it requires
  -- a `NormedAddCommGorup x` instance.
  unfold Complement'
  -- also need to unfold Complement' in the NormedAddCommGroup instance...
  rw [dif_pos]
  let aux := dif_pos
  --apply iteInduction (c := y ∈ range f) (α := Type _) (motive := fun _ ↦ ))
  by_cases h : y ∈ range f
  · simp [Complement', h]
    --simp_rw [if_pos h]
    --have : NormedSpace 𝕜 (h.choose_spec ▸ hy).Complement := sorry
    sorry
  simp only [Complement'] --, h, ↓reduceDIte] -/
  sorry

/-- The set `f ⁻¹' y` coerced to a type that will be endowed with a manifold
structure by the regular value theorem.

Note: we want the hypothesis `hy` to appear in the type of this definition,
so the instance `immersedSubmanifold` mentions `I`, `J` and `f` somewhere. -/
@[nolint unusedArguments, expose]
abbrev Preimage (_hy : IsRegularValue I J f y) : Type _ :=
  f ⁻¹' {y}

/-
@[nolint unusedArguments, expose]
abbrev PreimageWithin (_hy : IsRegularValue I J f y) (s : Set M) : Type _ :=
  (s ∩ (f ⁻¹' {y})) -/

-- @[simp] lemma preimageWithin_univ (_hy : IsRegularValue I J f y) :
--  PreimageWithin _hy _hf univ = Preimage _hy _hf := sorry

/-- The model normed space for the manifold structure on `f ⁻¹' {y}`. -/
@[nolint unusedArguments, expose]
def modelSpace (_hx : IsRegularValue I J f (f x)) : Type _ :=
  (mfderiv I J f x).ker

/-- The model normed space for the manifold structure on `f ⁻¹' {y}`. -/
@[nolint unusedArguments, expose]
def modelSpace' (_hy : IsRegularValue I J f y) : Type _ := by
  classical exact if h : y ∈ range f then (h.choose_spec ▸ _hy).modelSpace else PUnit

instance (hx : IsRegularValue I J f (f x)) :
    NormedAddCommGroup hx.modelSpace := by
  unfold modelSpace
  infer_instance

instance (hx : IsRegularValue I J f (f x)) :
    NormedSpace 𝕜 hx.modelSpace := by
  unfold modelSpace
  letI : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs <| NormedAddCommGroup E₁
  letI : NormedSpace 𝕜 (TangentSpace I x) := inferInstanceAs <| NormedSpace _ E₁
  infer_instance

instance (hy : IsRegularValue I J f y) : NormedAddCommGroup hy.modelSpace' := by
  by_cases h : y ∈ range f <;> simp only [modelSpace', h, ↓reduceDIte] <;> infer_instance

instance (hy : IsRegularValue I J f y) :
    NormedSpace 𝕜 hy.modelSpace' := by
  sorry -- TODO: why does this not work?
  -- by_cases h : y ∈ range f <;> simp only [modelSpace', h, ↓reduceDIte] <;> infer_instance

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
    ImmersedSubmanifold (sandbox.modelWithCorners hx) I hx.Preimage M n hx.Complement where
  map := Subtype.val
  sliceModel.equiv := sorry
  sliceModel.map := Subtype.val
  sliceModel.hmap := .subtypeVal
  sliceModel.compatible := sorry
  real_condition := sorry

instance {x : M} (hx : IsRegularValue I J f (f x)) (hf : ContMDiff I J n f) :
    ChartedSpace (sandbox.model hx) hx.Preimage :=
  (immersedSubmanifold hx hf).chartedSpace

end sandbox

-- Let us assume we have a boundaryless manifold: otherwise, the mathematics is less clear for now.
section Boundaryless

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
@[expose]
def modelWithCorners (hx : IsRegularValue I J f (f x)) :
    ModelWithCorners 𝕜 hx.modelSpace hx.modelSpace :=
  𝓘(𝕜, _)

-- TODO: also provide a version that allows bringing your own
-- right inverse for mfderiv f x? or complement?

/-- The **regular value theorem** for boundaryless manifolds, main case:
for a regular value `y` of `f` which lies in `range f`. -/
def immersedSubmanifold_aux [I.Boundaryless] (hx : IsRegularValue I J f (f x)) :
    ImmersedSubmanifold 𝓘(𝕜, hx.modelSpace) I hx.Preimage M n hx.Complement where
  map := Subtype.val
  sliceModel := sorry -- should be a known condition
  real_condition := sorry

-- ideally, this would not be necessary
abbrev inclusion (hy : IsRegularValue I J f y) : hy.Preimage → M :=
    fun x ↦ x.val

-- TODO: steal a universe level from M or so; this statement has free universe levels!
/-- The **regular value theorem** for boundaryless manifolds, for any regular value `y` of `f`. -/
lemma immersedSubmanifold [I.Boundaryless] (hy : IsRegularValue I J f y) :
    ∃ (E''' C : Type _) (_ : NormedAddCommGroup E''') (_ : NormedSpace 𝕜 E''')
      (_ : NormedAddCommGroup C) (_ : NormedSpace 𝕜 C),
    Nonempty (ImmersedSubmanifold 𝓘(𝕜, E''') I hy.Preimage M n C) := by
  sorry

/-- The **regular value theorem** for boundaryless manifolds, for any regular value `y` of `f`. -/
lemma immersedSubmanifolds_foo [I.Boundaryless] (hy : IsRegularValue I J f y)
    (hf : ContMDiff I J n f) :
    ∃ (E''' : Type*) (_ : NormedAddCommGroup E''') (_ : NormedSpace 𝕜 E''')
      (_ : ChartedSpace E''' hy.Preimage) (_ : IsManifold 𝓘(𝕜, E''') n hy.Preimage),
    IsImmersion 𝓘(𝕜, E''') I n hy.inclusion := by
  -- revisit once the above statement is fixed!
  -- choose modelSpace complement _ _ _ h using immersedSubmanifold hy hf
  sorry

-- use the other lemma
instance [I.Boundaryless] (hy : IsRegularValue I J f y) :
    ChartedSpace hy.modelSpace' hy.Preimage :=
  sorry -- use immersedSubmanifolds_foo
  -- was: (hy.immersedSubmanifold hf).chartedSpace

instance [I.Boundaryless] (hy : IsRegularValue I J f y) :
    IsManifold 𝓘(𝕜, hy.modelSpace') n hy.Preimage :=
  sorry -- use immersedSubmanifolds_foo
  -- was: (hy.immersedSubmanifold hf).isManifold


lemma foo [I.Boundaryless] (hy : IsRegularValue I J f y) :
    IsSmoothEmbedding 𝓘(𝕜, hy.modelSpace') I n hy.inclusion :=
  sorry -- general submanifold nonsense


/-- The **regular value theorem** for boundaryless manifolds:
if `f` is a submersion, for any value in the range of f. -/
def immersedSubmanifold_submersion [I.Boundaryless] (hf : IsSubmersion I J n f) :
    letI hx := hf.isRegularValue (f x)
    ImmersedSubmanifold hx.modelWithCorners I hx.Preimage M n hx.Complement where
  map := Subtype.val
  sliceModel := sorry -- should be a known condition
  real_condition := sorry

/-- The **regular value theorem** for boundaryless manifolds: if `f : M → N` has surjective
differential everywhere and `N` is finite-dimensional over a complete field,
`f ⁻¹' {y}` is a submanifold for each `y ∈ range f`. -/
def immersedSubmanifold_submersion' [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E₃] [I.Boundaryless]
    (hf : ∀ (x : M), Surjective (mfderiv I J f x)) :
    letI  hf' := IsSubmersion.of_mfderiv_surjective_of_finiteDimensional hf (n := n)
    letI hx := hf'.isRegularValue (f x)
    ImmersedSubmanifold hx.modelWithCorners I hx.Preimage M n hx.Complement :=
  immersedSubmanifold_submersion (.of_mfderiv_surjective_of_finiteDimensional hf)


/-- The model normed space for the manifold structure on `f ⁻¹' {y}`,
in case the differential at `x` has constant rank. -/
@[nolint unusedArguments, expose]
def _root_.modelSpace'' {k : ℕ} (_hx : (mfderiv I J f x).rank = k) : Type _ :=
  (mfderiv I J f x).ker

instance {k : ℕ} (hx : (mfderiv I J f x).rank = k) :
    NormedAddCommGroup (modelSpace'' hx) := by
  delta modelSpace''
  infer_instance

instance {k : ℕ} (hx : (mfderiv I J f x).rank = k) :
    NormedSpace 𝕜 (modelSpace'' hx) := by
  delta modelSpace''
  letI : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs <| NormedAddCommGroup E₁
  letI : NormedSpace 𝕜 (TangentSpace I x) := inferInstanceAs <| NormedSpace _ E₁
  infer_instance

-- TODO: think about this complement in general and provide one;
-- perhaps 𝕜^(finrak E₃ - k) already works
/-- A complement in the model normed spaces `E` of `M` for the point `f x`
with differential of fixed rank. -/
@[expose]
def Complement'' {k : ℕ} (hx : (mfderiv I J f x).rank = k) : Type _ :=
  sorry
  --deriving NormedAddCommGroup

instance {k : ℕ} (hx : (mfderiv I J f x).rank = k) : NormedAddCommGroup (Complement'' hx) := by
  sorry

instance {k : ℕ} (hx : (mfderiv I J f x).rank = k) : NormedSpace 𝕜 (Complement'' hx) := by sorry


/-- The **constank rank theorem** for boundaryless manifolds: if the differential of `f : M → N`
has constant rank and `N` is finite-dimensional over a complete field,
`f ⁻¹' {y}` is a submanifold for each `y ∈ range f`. -/
def ImmersedSubmanifold.of_constant_rank [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E₃] [I.Boundaryless]
    {k : ℕ} (hf : ∀ (x : M), (mfderiv I J f x).rank = k) :
    ImmersedSubmanifold 𝓘(𝕜, (modelSpace'' (hf x))) I (f ⁻¹' {y}) M n (Complement'' (hf x)) := by
  -- This will require a separate proof, similar to the regular value theorem above.
  sorry

end Boundaryless

end IsRegularValue
