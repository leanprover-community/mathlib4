/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

#align_import geometry.manifold.mfderiv from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# The derivative of functions between smooth manifolds

Let `M` and `M'` be two smooth manifolds with corners over a field `𝕜` (with respective models with
corners `I` on `(E, H)` and `I'` on `(E', H')`), and let `f : M → M'`. We define the
derivative of the function at a point, within a set or along the whole space, mimicking the API
for (Fréchet) derivatives. It is denoted by `mfderiv I I' f x`, where "m" stands for "manifold" and
"f" for "Fréchet" (as in the usual derivative `fderiv 𝕜 f x`).

## Main definitions

* `UniqueMDiffOn I s` : predicate saying that, at each point of the set `s`, a function can have
  at most one derivative. This technical condition is important when we define
  `mfderivWithin` below, as otherwise there is an arbitrary choice in the derivative,
  and many properties will fail (for instance the chain rule). This is analogous to
  `UniqueDiffOn 𝕜 s` in a vector space.

Let `f` be a map between smooth manifolds. The following definitions follow the `fderiv` API.

* `mfderiv I I' f x` : the derivative of `f` at `x`, as a continuous linear map from the tangent
  space at `x` to the tangent space at `f x`. If the map is not differentiable, this is `0`.
* `mfderivWithin I I' f s x` : the derivative of `f` at `x` within `s`, as a continuous linear map
  from the tangent space at `x` to the tangent space at `f x`. If the map is not differentiable
  within `s`, this is `0`.
* `MDifferentiableAt I I' f x` : Prop expressing whether `f` is differentiable at `x`.
* `MDifferentiableWithinAt 𝕜 f s x` : Prop expressing whether `f` is differentiable within `s`
  at `x`.
* `HasMFDerivAt I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative at `x`.
* `HasMFDerivWithinAt I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative
  within `s` at `x`.
* `MDifferentiableOn I I' f s` : Prop expressing that `f` is differentiable on the set `s`.
* `MDifferentiable I I' f` : Prop expressing that `f` is differentiable everywhere.
* `tangentMap I I' f` : the derivative of `f`, as a map from the tangent bundle of `M` to the
  tangent bundle of `M'`.

Various related results are proven in separate files: see
- `Basic.lean` for basic properties of the `mfderiv`, mimicking the API of the Fréchet derivative,
- `FDeriv.lean` for the equivalence of the manifold notions with the usual Fréchet derivative
for functions between vector spaces,
- `SpecificFunctions.lean` for results on the differential of the identity, constant functions,
products and arithmetic operators (like addition or scalar multiplication),
- `Atlas.lean` for differentiability of charts, models with corners and extended charts,
- `UniqueDifferential.lean` for various properties of unique differentiability sets in manifolds.

## Implementation notes

The tangent bundle is constructed using the machinery of topological fiber bundles, for which one
can define bundled morphisms and construct canonically maps from the total space of one bundle to
the total space of another one. One could use this mechanism to construct directly the derivative
of a smooth map. However, we want to define the derivative of any map (and let it be zero if the map
is not differentiable) to avoid proof arguments everywhere. This means we have to go back to the
details of the definition of the total space of a fiber bundle constructed from core, to cook up a
suitable definition of the derivative. It is the following: at each point, we have a preferred chart
(used to identify the fiber above the point with the model vector space in fiber bundles). Then one
should read the function using these preferred charts at `x` and `f x`, and take the derivative
of `f` in these charts.

Due to the fact that we are working in a model with corners, with an additional embedding `I` of the
model space `H` in the model vector space `E`, the charts taking values in `E` are not the original
charts of the manifold, but those ones composed with `I`, called extended charts. We define
`writtenInExtChartAt I I' x f` for the function `f` written in the preferred extended charts. Then
the manifold derivative of `f`, at `x`, is just the usual derivative of
`writtenInExtChartAt I I' x f`, at the point `(extChartAt I x) x`.

There is a subtlety with respect to continuity: if the function is not continuous, then the image
of a small open set around `x` will not be contained in the source of the preferred chart around
`f x`, which means that when reading `f` in the chart one is losing some information. To avoid this,
we include continuity in the definition of differentiablity (which is reasonable since with any
definition, differentiability implies continuity).

*Warning*: the derivative (even within a subset) is a linear map on the whole tangent space. Suppose
that one is given a smooth submanifold `N`, and a function which is smooth on `N` (i.e., its
restriction to the subtype `N` is smooth). Then, in the whole manifold `M`, the property
`MDifferentiableOn I I' f N` holds. However, `mfderivWithin I I' f N` is not uniquely defined
(what values would one choose for vectors that are transverse to `N`?), which can create issues down
the road. The problem here is that knowing the value of `f` along `N` does not determine the
differential of `f` in all directions. This is in contrast to the case where `N` would be an open
subset, or a submanifold with boundary of maximal dimension, where this issue does not appear.
The predicate `UniqueMDiffOn I N` indicates that the derivative along `N` is unique if it exists,
and is an assumption in most statements requiring a form of uniqueness.

On a vector space, the manifold derivative and the usual derivative are equal. This means in
particular that they live on the same space, i.e., the tangent space is defeq to the original vector
space. To get this property is a motivation for our definition of the tangent space as a single
copy of the vector space, instead of more usual definitions such as the space of derivations, or
the space of equivalence classes of smooth curves in the manifold.

## Tags
derivative, manifold
-/

noncomputable section

open scoped Classical Topology Manifold
open Set ChartedSpace

section DerivativesDefinitions

/-!
### Derivative of maps between manifolds

The derivative of a smooth map `f` between smooth manifold `M` and `M'` at `x` is a bounded linear
map from the tangent space to `M` at `x`, to the tangent space to `M'` at `f x`. Since we defined
the tangent space using one specific chart, the formula for the derivative is written in terms of
this specific chart.

We use the names `MDifferentiable` and `mfderiv`, where the prefix letter `m` means "manifold".
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M']

/-- Property in the model space of a model with corners of being differentiable within at set at a
point, when read in the model vector space. This property will be lifted to manifolds to define
differentiable functions between manifolds. -/
def DifferentiableWithinAtProp (f : H → H') (s : Set H) (x : H) : Prop :=
  DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ Set.range I) (I x)
#align differentiable_within_at_prop DifferentiableWithinAtProp

/-- Being differentiable in the model space is a local property, invariant under smooth maps.
Therefore, it will lift nicely to manifolds. -/
theorem differentiable_within_at_localInvariantProp :
    (contDiffGroupoid ⊤ I).LocalInvariantProp (contDiffGroupoid ⊤ I')
      (DifferentiableWithinAtProp I I') :=
  { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s ∩ u) ∩ Set.range I = I.symm ⁻¹' s ∩ Set.range I ∩ I.symm ⁻¹' u := by
        simp only [Set.inter_right_comm, Set.preimage_inter]
      rw [DifferentiableWithinAtProp, DifferentiableWithinAtProp, this]
      symm
      apply differentiableWithinAt_inter
      have : u ∈ 𝓝 (I.symm (I x)) := by
        rw [ModelWithCorners.left_inv]
        exact u_open.mem_nhds xu
      apply I.continuous_symm.continuousAt this
    right_invariance' := by
      intro s x f e he hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h
      have : I (e x) ∈ I.symm ⁻¹' e.target ∩ Set.range I := by simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
      convert (h.comp' _ (this.differentiableWithinAt le_top)).mono_of_mem _ using 1
      · ext y; simp only [mfld_simps]
      refine
        mem_nhdsWithin.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [Set.mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
      mfld_set_tac
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [h, hy, mfld_simps]
      · simp only [hx, mfld_simps]
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ Set.range I' := by
        simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
      convert (this.differentiableWithinAt le_top).comp _ h _
      · ext y; simp only [mfld_simps]
      · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1 }
#align differentiable_within_at_local_invariant_prop differentiable_within_at_localInvariantProp

/-- Predicate ensuring that, at a point and within a set, a function can have at most one
derivative. This is expressed using the preferred chart at the considered point. -/
def UniqueMDiffWithinAt (s : Set M) (x : M) :=
  UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
#align unique_mdiff_within_at UniqueMDiffWithinAt

/-- Predicate ensuring that, at all points of a set, a function can have at most one derivative. -/
def UniqueMDiffOn (s : Set M) :=
  ∀ x ∈ s, UniqueMDiffWithinAt I s x
#align unique_mdiff_on UniqueMDiffOn

/-- `MDifferentiableWithinAt I I' f s x` indicates that the function `f` between manifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `DifferentiableWithinAt` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def MDifferentiableWithinAt (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x
#align mdifferentiable_within_at MDifferentiableWithinAt

theorem mdifferentiableWithinAt_iff' (f : M → M') (s : Set M) (x : M) :
    MDifferentiableWithinAt I I' f s x ↔ ContinuousWithinAt f s x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) := by
  rw [MDifferentiableWithinAt, liftPropWithinAt_iff']; rfl
#align mdifferentiable_within_at_iff_lift_prop_within_at mdifferentiableWithinAt_iff'

@[deprecated] -- 2024-04-30
alias mdifferentiableWithinAt_iff_liftPropWithinAt := mdifferentiableWithinAt_iff'

variable {I I'} in
theorem MDifferentiableWithinAt.continuousWithinAt {f : M → M'} {s : Set M} {x : M}
    (hf : MDifferentiableWithinAt I I' f s x) :
    ContinuousWithinAt f s x :=
  mdifferentiableWithinAt_iff' .. |>.1 hf |>.1
#align mdifferentiable_within_at.continuous_within_at MDifferentiableWithinAt.continuousWithinAt

variable {I I'} in
theorem MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
    {f : M → M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I I' f s x) :
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) :=
  mdifferentiableWithinAt_iff' .. |>.1 hf |>.2

/-- `MDifferentiableAt I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `DifferentiableAt` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def MDifferentiableAt (f : M → M') (x : M) :=
  LiftPropAt (DifferentiableWithinAtProp I I') f x
#align mdifferentiable_at MDifferentiableAt

theorem mdifferentiableAt_iff (f : M → M') (x : M) :
    MDifferentiableAt I I' f x ↔ ContinuousAt f x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) := by
  rw [MDifferentiableAt, liftPropAt_iff]
  congrm _ ∧ ?_
  simp [DifferentiableWithinAtProp, Set.univ_inter]
  -- Porting note: `rfl` wasn't needed
  rfl
#align mdifferentiable_at_iff_lift_prop_at mdifferentiableAt_iff

@[deprecated] -- 2024-04-30
alias mdifferentiableAt_iff_liftPropAt := mdifferentiableAt_iff

variable {I I'} in
theorem MDifferentiableAt.continuousAt {f : M → M'} {x : M} (hf : MDifferentiableAt I I' f x) :
    ContinuousAt f x :=
  mdifferentiableAt_iff .. |>.1 hf |>.1
#align mdifferentiable_at.continuous_at MDifferentiableAt.continuousAt

variable {I I'} in
theorem MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt {f : M → M'} {x : M}
    (hf : MDifferentiableAt I I' f x) :
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) :=
  mdifferentiableAt_iff .. |>.1 hf |>.2

/-- `MDifferentiableOn I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `DifferentiableOn` to manifolds. -/
def MDifferentiableOn (f : M → M') (s : Set M) :=
  ∀ x ∈ s, MDifferentiableWithinAt I I' f s x
#align mdifferentiable_on MDifferentiableOn

/-- `MDifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `Differentiable` to manifolds. -/
def MDifferentiable (f : M → M') :=
  ∀ x, MDifferentiableAt I I' f x
#align mdifferentiable MDifferentiable

/-- Prop registering if a partial homeomorphism is a local diffeomorphism on its source -/
def PartialHomeomorph.MDifferentiable (f : PartialHomeomorph M M') :=
  MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target
#align local_homeomorph.mdifferentiable PartialHomeomorph.MDifferentiable

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']

/-- `HasMFDerivWithinAt I I' f s x f'` indicates that the function `f` between manifolds
has, at the point `x` and within the set `s`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

This is a generalization of `HasFDerivWithinAt` to manifolds (as indicated by the prefix `m`).
The order of arguments is changed as the type of the derivative `f'` depends on the choice of `x`.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def HasMFDerivWithinAt (f : M → M') (s : Set M) (x : M)
    (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousWithinAt f s x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f'
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
#align has_mfderiv_within_at HasMFDerivWithinAt

/-- `HasMFDerivAt I I' f x f'` indicates that the function `f` between manifolds
has, at the point `x`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

We require continuity in the definition, as otherwise points close to `x` `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def HasMFDerivAt (f : M → M') (x : M) (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f' (range I) ((extChartAt I x) x)
#align has_mfderiv_at HasMFDerivAt

/-- Let `f` be a function between two smooth manifolds. Then `mfderivWithin I I' f s x` is the
derivative of `f` at `x` within `s`, as a continuous linear map from the tangent space at `x` to the
tangent space at `f x`. -/
def mfderivWithin (f : M → M') (s : Set M) (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) :
      _)
  else 0
#align mfderiv_within mfderivWithin

/-- Let `f` be a function between two smooth manifolds. Then `mfderiv I I' f x` is the derivative of
`f` at `x`, as a continuous linear map from the tangent space at `x` to the tangent space at
`f x`. -/
def mfderiv (f : M → M') (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E → E') (range I) ((extChartAt I x) x) : _)
  else 0
#align mfderiv mfderiv

/-- The derivative within a set, as a map between the tangent bundles -/
def tangentMapWithin (f : M → M') (s : Set M) : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
#align tangent_map_within tangentMapWithin

/-- The derivative, as a map between the tangent bundles -/
def tangentMap (f : M → M') : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
#align tangent_map tangentMap

end DerivativesDefinitions
