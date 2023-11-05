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

We also establish results on the differential of the identity, constant functions, charts, extended
charts. For functions between vector spaces, we show that the usual notions and the manifold notions
coincide.

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

There is a subtelty with respect to continuity: if the function is not continuous, then the image
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
Derivative, manifold
-/

set_option autoImplicit true


noncomputable section

open scoped Classical Topology Manifold Bundle
open Set Bundle ChartedSpace

universe u

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
        exact IsOpen.mem_nhds u_open xu
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
      refine'
        mem_nhdsWithin.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [Set.mem_preimage, I.left_inv, e.mapsTo hx], _⟩
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

/-- Predicate ensuring that, at a point and within a set, a function can have at most one
derivative. This is expressed using the preferred chart at the considered point. -/
def UniqueMDiffWithinAt (s : Set M) (x : M) :=
  UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)

/-- Predicate ensuring that, at all points of a set, a function can have at most one derivative. -/
def UniqueMDiffOn (s : Set M) :=
  ∀ x ∈ s, UniqueMDiffWithinAt I s x

/-- `MDifferentiableWithinAt I I' f s x` indicates that the function `f` between manifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `DifferentiableWithinAt` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def MDifferentiableWithinAt (f : M → M') (s : Set M) (x : M) :=
  ContinuousWithinAt f s x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x)

theorem mdifferentiableWithinAt_iff_liftPropWithinAt (f : M → M') (s : Set M) (x : M) :
    MDifferentiableWithinAt I I' f s x ↔ LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x :=
  by rfl

/-- `MDifferentiableAt I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `DifferentiableAt` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def MDifferentiableAt (f : M → M') (x : M) :=
  ContinuousAt f x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x)

theorem mdifferentiableAt_iff_liftPropAt (f : M → M') (x : M) :
    MDifferentiableAt I I' f x ↔ LiftPropAt (DifferentiableWithinAtProp I I') f x := by
  congrm ?_ ∧ ?_
  · rw [continuousWithinAt_univ]
  · -- porting note: `rfl` wasn't needed
    simp [DifferentiableWithinAtProp, Set.univ_inter]; rfl

/-- `MDifferentiableOn I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `DifferentiableOn` to manifolds. -/
def MDifferentiableOn (f : M → M') (s : Set M) :=
  ∀ x ∈ s, MDifferentiableWithinAt I I' f s x

/-- `MDifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `Differentiable` to manifolds. -/
def MDifferentiable (f : M → M') :=
  ∀ x, MDifferentiableAt I I' f x

/-- Prop registering if a local homeomorphism is a local diffeomorphism on its source -/
def LocalHomeomorph.MDifferentiable (f : LocalHomeomorph M M') :=
  MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target

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

/-- Let `f` be a function between two smooth manifolds. Then `mfderivWithin I I' f s x` is the
derivative of `f` at `x` within `s`, as a continuous linear map from the tangent space at `x` to the
tangent space at `f x`. -/
def mfderivWithin (f : M → M') (s : Set M) (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) :
      _)
  else 0

/-- Let `f` be a function between two smooth manifolds. Then `mfderiv I I' f x` is the derivative of
`f` at `x`, as a continuous linear map from the tangent space at `x` to the tangent space at
`f x`. -/
def mfderiv (f : M → M') (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E → E') (range I) ((extChartAt I x) x) : _)
  else 0

/-- The derivative within a set, as a map between the tangent bundles -/
def tangentMapWithin (f : M → M') (s : Set M) : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩

/-- The derivative, as a map between the tangent bundles -/
def tangentMap (f : M → M') : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩

end DerivativesDefinitions

section DerivativesProperties

/-! ### Unique differentiability sets in manifolds -/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f f₀ f₁ : M → M'} {x : M} {s t : Set M} {g : M' → M''} {u : Set M'}

theorem uniqueMDiffWithinAt_univ : UniqueMDiffWithinAt I univ x := by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.unique_diff _ (mem_range_self _)

variable {I}

theorem uniqueMDiffWithinAt_iff {s : Set M} {x : M} :
    UniqueMDiffWithinAt I s x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target)
        ((extChartAt I x) x) := by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

nonrec theorem UniqueMDiffWithinAt.mono_nhds {s t : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (ht : 𝓝[s] x ≤ 𝓝[t] x) : UniqueMDiffWithinAt I t x :=
  hs.mono_nhds <| by simpa only [← map_extChartAt_nhdsWithin] using Filter.map_mono ht

theorem UniqueMDiffWithinAt.mono_of_mem {s t : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (ht : t ∈ 𝓝[s] x) : UniqueMDiffWithinAt I t x :=
  hs.mono_nhds (nhdsWithin_le_iff.2 ht)

theorem UniqueMDiffWithinAt.mono (h : UniqueMDiffWithinAt I s x) (st : s ⊆ t) :
    UniqueMDiffWithinAt I t x :=
  UniqueDiffWithinAt.mono h <| inter_subset_inter (preimage_mono st) (Subset.refl _)

theorem UniqueMDiffWithinAt.inter' (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝[s] x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  hs.mono_of_mem (Filter.inter_mem self_mem_nhdsWithin ht)

theorem UniqueMDiffWithinAt.inter (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝 x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  hs.inter' (nhdsWithin_le_nhds ht)

theorem IsOpen.uniqueMDiffWithinAt (xs : x ∈ s) (hs : IsOpen s) : UniqueMDiffWithinAt I s x :=
  (uniqueMDiffWithinAt_univ I).mono_of_mem <| nhdsWithin_le_nhds <| hs.mem_nhds xs

theorem UniqueMDiffOn.inter (hs : UniqueMDiffOn I s) (ht : IsOpen t) : UniqueMDiffOn I (s ∩ t) :=
  fun _x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (IsOpen.mem_nhds ht hx.2)

theorem IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiffOn I s := fun _x hx =>
  IsOpen.uniqueMDiffWithinAt hx hs

theorem uniqueMDiffOn_univ : UniqueMDiffOn I (univ : Set M) :=
  isOpen_univ.uniqueMDiffOn

/- We name the typeclass variables related to `SmoothManifoldWithCorners` structure as they are
necessary in lemmas mentioning the derivative, but not in lemmas about differentiability, so we
want to include them or omit them when necessary. -/
variable [Is : SmoothManifoldWithCorners I M] [I's : SmoothManifoldWithCorners I' M']
  [I''s : SmoothManifoldWithCorners I'' M'']
  {f' f₀' f₁' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)}
  {g' : TangentSpace I' (f x) →L[𝕜] TangentSpace I'' (g (f x))}

/-- `UniqueMDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
nonrec theorem UniqueMDiffWithinAt.eq (U : UniqueMDiffWithinAt I s x)
    (h : HasMFDerivWithinAt I I' f s x f') (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' := by
  -- porting note: didn't need `convert` because of finding instances by unification
  convert U.eq h.2 h₁.2

theorem UniqueMDiffOn.eq (U : UniqueMDiffOn I s) (hx : x ∈ s) (h : HasMFDerivWithinAt I I' f s x f')
    (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' :=
  UniqueMDiffWithinAt.eq (U _ hx) h h₁

nonrec theorem UniqueMDiffWithinAt.prod {x : M} {y : M'} {s t} (hs : UniqueMDiffWithinAt I s x)
    (ht : UniqueMDiffWithinAt I' t y) : UniqueMDiffWithinAt (I.prod I') (s ×ˢ t) (x, y) := by
  refine (hs.prod ht).mono ?_
  rw [ModelWithCorners.range_prod, ← prod_inter_prod]
  rfl

theorem UniqueMDiffOn.prod {s : Set M} {t : Set M'} (hs : UniqueMDiffOn I s)
    (ht : UniqueMDiffOn I' t) : UniqueMDiffOn (I.prod I') (s ×ˢ t) := fun x h ↦
  (hs x.1 h.1).prod (ht x.2 h.2)

/-!
### General lemmas on derivatives of functions between manifolds

We mimick the API for functions between vector spaces
-/

theorem mdifferentiableWithinAt_iff {f : M → M'} {s : Set M} {x : M} :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) := by
  refine' and_congr Iff.rfl (exists_congr fun f' => _)
  rw [inter_comm]
  simp only [HasFDerivWithinAt, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

/-- One can reformulate differentiability within a set at a point as continuity within this set at
this point, and differentiability in any chart containing that point. -/
theorem mdifferentiableWithinAt_iff_of_mem_source {x' : M} {y : M'}
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    MDifferentiableWithinAt I I' f s x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ Set.range I) ((extChartAt I x) x') :=
  (differentiable_within_at_localInvariantProp I I').liftPropWithinAt_indep_chart
    (StructureGroupoid.chart_mem_maximalAtlas _ x) hx (StructureGroupoid.chart_mem_maximalAtlas _ y)
    hy

theorem mfderivWithin_zero_of_not_mdifferentiableWithinAt
    (h : ¬MDifferentiableWithinAt I I' f s x) : mfderivWithin I I' f s x = 0 := by
  simp only [mfderivWithin, h, if_neg, not_false_iff]

theorem mfderiv_zero_of_not_mdifferentiableAt (h : ¬MDifferentiableAt I I' f x) :
    mfderiv I I' f x = 0 := by simp only [mfderiv, h, if_neg, not_false_iff]

theorem HasMFDerivWithinAt.mono (h : HasMFDerivWithinAt I I' f t x f') (hst : s ⊆ t) :
    HasMFDerivWithinAt I I' f s x f' :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    HasFDerivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩

theorem HasMFDerivAt.hasMFDerivWithinAt (h : HasMFDerivAt I I' f x f') :
    HasMFDerivWithinAt I I' f s x f' :=
  ⟨ContinuousAt.continuousWithinAt h.1, HasFDerivWithinAt.mono h.2 (inter_subset_right _ _)⟩

theorem HasMFDerivWithinAt.mdifferentiableWithinAt (h : HasMFDerivWithinAt I I' f s x f') :
    MDifferentiableWithinAt I I' f s x :=
  ⟨h.1, ⟨f', h.2⟩⟩

theorem HasMFDerivAt.mdifferentiableAt (h : HasMFDerivAt I I' f x f') :
    MDifferentiableAt I I' f x :=
  ⟨h.1, ⟨f', h.2⟩⟩

@[simp, mfld_simps]
theorem hasMFDerivWithinAt_univ : HasMFDerivWithinAt I I' f univ x f' ↔ HasMFDerivAt I I' f x f' :=
  by simp only [HasMFDerivWithinAt, HasMFDerivAt, continuousWithinAt_univ, mfld_simps]

theorem hasMFDerivAt_unique (h₀ : HasMFDerivAt I I' f x f₀') (h₁ : HasMFDerivAt I I' f x f₁') :
    f₀' = f₁' := by
  rw [← hasMFDerivWithinAt_univ] at h₀ h₁
  exact (uniqueMDiffWithinAt_univ I).eq h₀ h₁

theorem hasMFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasMFDerivWithinAt I I' f (s ∩ t) x f' ↔ HasMFDerivWithinAt I I' f s x f' := by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq,
    hasFDerivWithinAt_inter', continuousWithinAt_inter' h]
  exact extChartAt_preimage_mem_nhdsWithin I x h

theorem hasMFDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasMFDerivWithinAt I I' f (s ∩ t) x f' ↔ HasMFDerivWithinAt I I' f s x f' := by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq, hasFDerivWithinAt_inter,
    continuousWithinAt_inter h]
  exact extChartAt_preimage_mem_nhds I x h

theorem HasMFDerivWithinAt.union (hs : HasMFDerivWithinAt I I' f s x f')
    (ht : HasMFDerivWithinAt I I' f t x f') : HasMFDerivWithinAt I I' f (s ∪ t) x f' := by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
  · convert HasFDerivWithinAt.union hs.2 ht.2 using 1
    simp only [union_inter_distrib_right, preimage_union]

theorem HasMFDerivWithinAt.mono_of_mem (h : HasMFDerivWithinAt I I' f s x f') (ht : s ∈ 𝓝[t] x) :
    HasMFDerivWithinAt I I' f t x f' :=
  (hasMFDerivWithinAt_inter' ht).1 (h.mono (inter_subset_right _ _))

theorem HasMFDerivWithinAt.hasMFDerivAt (h : HasMFDerivWithinAt I I' f s x f') (hs : s ∈ 𝓝 x) :
    HasMFDerivAt I I' f x f' := by
  rwa [← univ_inter s, hasMFDerivWithinAt_inter hs, hasMFDerivWithinAt_univ] at h

theorem MDifferentiableWithinAt.hasMFDerivWithinAt (h : MDifferentiableWithinAt I I' f s x) :
    HasMFDerivWithinAt I I' f s x (mfderivWithin I I' f s x) := by
  refine' ⟨h.1, _⟩
  simp only [mfderivWithin, h, if_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2

protected theorem MDifferentiableWithinAt.mfderivWithin (h : MDifferentiableWithinAt I I' f s x) :
    mfderivWithin I I' f s x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f : _) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) :=
  by simp only [mfderivWithin, h, if_pos]

theorem MDifferentiableAt.hasMFDerivAt (h : MDifferentiableAt I I' f x) :
    HasMFDerivAt I I' f x (mfderiv I I' f x) := by
  refine' ⟨h.1, _⟩
  simp only [mfderiv, h, if_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2

protected theorem MDifferentiableAt.mfderiv (h : MDifferentiableAt I I' f x) :
    mfderiv I I' f x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f : _) (range I) ((extChartAt I x) x) :=
  by simp only [mfderiv, h, if_pos]

protected theorem HasMFDerivAt.mfderiv (h : HasMFDerivAt I I' f x f') : mfderiv I I' f x = f' :=
  (hasMFDerivAt_unique h h.mdifferentiableAt.hasMFDerivAt).symm

theorem HasMFDerivWithinAt.mfderivWithin (h : HasMFDerivWithinAt I I' f s x f')
    (hxs : UniqueMDiffWithinAt I s x) : mfderivWithin I I' f s x = f' := by
  ext
  rw [hxs.eq h h.mdifferentiableWithinAt.hasMFDerivWithinAt]

theorem MDifferentiable.mfderivWithin (h : MDifferentiableAt I I' f x)
    (hxs : UniqueMDiffWithinAt I s x) : mfderivWithin I I' f s x = mfderiv I I' f x := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact h.hasMFDerivAt.hasMFDerivWithinAt

theorem mfderivWithin_subset (st : s ⊆ t) (hs : UniqueMDiffWithinAt I s x)
    (h : MDifferentiableWithinAt I I' f t x) :
    mfderivWithin I I' f s x = mfderivWithin I I' f t x :=
  ((MDifferentiableWithinAt.hasMFDerivWithinAt h).mono st).mfderivWithin hs

theorem MDifferentiableWithinAt.mono (hst : s ⊆ t) (h : MDifferentiableWithinAt I I' f t x) :
    MDifferentiableWithinAt I I' f s x :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    DifferentiableWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩

theorem mdifferentiableWithinAt_univ :
    MDifferentiableWithinAt I I' f univ x ↔ MDifferentiableAt I I' f x := by
  simp only [MDifferentiableWithinAt, MDifferentiableAt, continuousWithinAt_univ, mfld_simps]

theorem mdifferentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt, extChartAt_preimage_inter_eq,
    differentiableWithinAt_inter, continuousWithinAt_inter ht]
  exact extChartAt_preimage_mem_nhds I x ht

theorem mdifferentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt, extChartAt_preimage_inter_eq,
    differentiableWithinAt_inter', continuousWithinAt_inter' ht]
  exact extChartAt_preimage_mem_nhdsWithin I x ht

theorem MDifferentiableAt.mdifferentiableWithinAt (h : MDifferentiableAt I I' f x) :
    MDifferentiableWithinAt I I' f s x :=
  MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)

theorem MDifferentiableWithinAt.mdifferentiableAt (h : MDifferentiableWithinAt I I' f s x)
    (hs : s ∈ 𝓝 x) : MDifferentiableAt I I' f x := by
  have : s = univ ∩ s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h

theorem MDifferentiableOn.mdifferentiableAt (h : MDifferentiableOn I I' f s) (hx : s ∈ 𝓝 x) :
    MDifferentiableAt I I' f x :=
  (h x (mem_of_mem_nhds hx)).mdifferentiableAt hx

theorem MDifferentiableOn.mono (h : MDifferentiableOn I I' f t) (st : s ⊆ t) :
    MDifferentiableOn I I' f s := fun x hx => (h x (st hx)).mono st

theorem mdifferentiableOn_univ : MDifferentiableOn I I' f univ ↔ MDifferentiable I I' f := by
  simp only [MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps]; rfl

theorem MDifferentiable.mdifferentiableOn (h : MDifferentiable I I' f) :
    MDifferentiableOn I I' f s :=
  (mdifferentiableOn_univ.2 h).mono (subset_univ _)

theorem mdifferentiableOn_of_locally_mdifferentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ MDifferentiableOn I I' f (s ∩ u)) :
    MDifferentiableOn I I' f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)

@[simp, mfld_simps]
theorem mfderivWithin_univ : mfderivWithin I I' f univ = mfderiv I I' f := by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiableWithinAt_univ]

theorem mfderivWithin_inter (ht : t ∈ 𝓝 x) :
    mfderivWithin I I' f (s ∩ t) x = mfderivWithin I I' f s x := by
  rw [mfderivWithin, mfderivWithin, extChartAt_preimage_inter_eq, mdifferentiableWithinAt_inter ht,
    fderivWithin_inter (extChartAt_preimage_mem_nhds I x ht)]

theorem mdifferentiableAt_iff_of_mem_source {x' : M} {y : M'}
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    MDifferentiableAt I I' f x' ↔
      ContinuousAt f x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) x') :=
  mdifferentiableWithinAt_univ.symm.trans <|
    (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans <| by
      rw [continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]

/-! ### Deducing differentiability from smoothness -/

-- porting note: moved from `ContMDiffMFDeriv`

theorem ContMDiffWithinAt.mdifferentiableWithinAt (hf : ContMDiffWithinAt I I' n f s x)
    (hn : 1 ≤ n) : MDifferentiableWithinAt I I' f s x := by
  suffices h : MDifferentiableWithinAt I I' f (s ∩ f ⁻¹' (extChartAt I' (f x)).source) x
  · rwa [mdifferentiableWithinAt_inter'] at h
    apply hf.1.preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds I' (f x)
  rw [mdifferentiableWithinAt_iff]
  exact ⟨hf.1.mono (inter_subset_left _ _), (hf.2.differentiableWithinAt hn).mono (by mfld_set_tac)⟩

theorem ContMDiffAt.mdifferentiableAt (hf : ContMDiffAt I I' n f x) (hn : 1 ≤ n) :
    MDifferentiableAt I I' f x :=
  mdifferentiableWithinAt_univ.1 <| ContMDiffWithinAt.mdifferentiableWithinAt hf hn

theorem ContMDiffOn.mdifferentiableOn (hf : ContMDiffOn I I' n f s) (hn : 1 ≤ n) :
    MDifferentiableOn I I' f s := fun x hx => (hf x hx).mdifferentiableWithinAt hn

theorem ContMDiff.mdifferentiable (hf : ContMDiff I I' n f) (hn : 1 ≤ n) : MDifferentiable I I' f :=
  fun x => (hf x).mdifferentiableAt hn

nonrec theorem SmoothWithinAt.mdifferentiableWithinAt (hf : SmoothWithinAt I I' f s x) :
    MDifferentiableWithinAt I I' f s x :=
  hf.mdifferentiableWithinAt le_top

nonrec theorem SmoothAt.mdifferentiableAt (hf : SmoothAt I I' f x) : MDifferentiableAt I I' f x :=
  hf.mdifferentiableAt le_top

nonrec theorem SmoothOn.mdifferentiableOn (hf : SmoothOn I I' f s) : MDifferentiableOn I I' f s :=
  hf.mdifferentiableOn le_top

theorem Smooth.mdifferentiable (hf : Smooth I I' f) : MDifferentiable I I' f :=
  ContMDiff.mdifferentiable hf le_top

theorem Smooth.mdifferentiableAt (hf : Smooth I I' f) : MDifferentiableAt I I' f x :=
  hf.mdifferentiable x

theorem Smooth.mdifferentiableWithinAt (hf : Smooth I I' f) : MDifferentiableWithinAt I I' f s x :=
  hf.mdifferentiableAt.mdifferentiableWithinAt

/-! ### Deriving continuity from differentiability on manifolds -/

theorem HasMFDerivWithinAt.continuousWithinAt (h : HasMFDerivWithinAt I I' f s x f') :
    ContinuousWithinAt f s x :=
  h.1

theorem HasMFDerivAt.continuousAt (h : HasMFDerivAt I I' f x f') : ContinuousAt f x :=
  h.1

theorem MDifferentiableWithinAt.continuousWithinAt (h : MDifferentiableWithinAt I I' f s x) :
    ContinuousWithinAt f s x :=
  h.1

theorem MDifferentiableAt.continuousAt (h : MDifferentiableAt I I' f x) : ContinuousAt f x :=
  h.1

theorem MDifferentiableOn.continuousOn (h : MDifferentiableOn I I' f s) : ContinuousOn f s :=
  fun x hx => (h x hx).continuousWithinAt

theorem MDifferentiable.continuous (h : MDifferentiable I I' f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt

theorem tangentMapWithin_subset {p : TangentBundle I M} (st : s ⊆ t)
    (hs : UniqueMDiffWithinAt I s p.1) (h : MDifferentiableWithinAt I I' f t p.1) :
    tangentMapWithin I I' f s p = tangentMapWithin I I' f t p := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_subset st hs h]

theorem tangentMapWithin_univ : tangentMapWithin I I' f univ = tangentMap I I' f := by
  ext p : 1
  simp only [tangentMapWithin, tangentMap, mfld_simps]

theorem tangentMapWithin_eq_tangentMap {p : TangentBundle I M} (hs : UniqueMDiffWithinAt I s p.1)
    (h : MDifferentiableAt I I' f p.1) : tangentMapWithin I I' f s p = tangentMap I I' f p := by
  rw [← mdifferentiableWithinAt_univ] at h
  rw [← tangentMapWithin_univ]
  exact tangentMapWithin_subset (subset_univ _) hs h

@[simp, mfld_simps]
theorem tangentMapWithin_proj {p : TangentBundle I M} :
    (tangentMapWithin I I' f s p).proj = f p.proj :=
  rfl

@[simp, mfld_simps]
theorem tangentMap_proj {p : TangentBundle I M} : (tangentMap I I' f p).proj = f p.proj :=
  rfl

theorem MDifferentiableWithinAt.prod_mk {f : M → M'} {g : M → M''}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : MDifferentiableWithinAt I I'' g s x) :
    MDifferentiableWithinAt I (I'.prod I'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

theorem MDifferentiableAt.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I I'' g x) :
    MDifferentiableAt I (I'.prod I'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

theorem MDifferentiableOn.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiableOn I I' f s)
    (hg : MDifferentiableOn I I'' g s) :
    MDifferentiableOn I (I'.prod I'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prod_mk (hg x hx)

theorem MDifferentiable.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiable I I' f)
    (hg : MDifferentiable I I'' g) : MDifferentiable I (I'.prod I'') fun x => (f x, g x) := fun x =>
  (hf x).prod_mk (hg x)

theorem MDifferentiableWithinAt.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s x)
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, E'') g s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

theorem MDifferentiableAt.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableAt I 𝓘(𝕜, E') f x) (hg : MDifferentiableAt I 𝓘(𝕜, E'') g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

theorem MDifferentiableOn.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableOn I 𝓘(𝕜, E') f s) (hg : MDifferentiableOn I 𝓘(𝕜, E'') g s) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prod_mk_space (hg x hx)

theorem MDifferentiable.prod_mk_space {f : M → E'} {g : M → E''} (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E'') g) : MDifferentiable I 𝓘(𝕜, E' × E'') fun x => (f x, g x) :=
  fun x => (hf x).prod_mk_space (hg x)

/-! ### Congruence lemmas for derivatives on manifolds -/


theorem HasMFDerivWithinAt.congr_of_eventuallyEq (h : HasMFDerivWithinAt I I' f s x f')
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasMFDerivWithinAt I I' f₁ s x f' := by
  refine' ⟨ContinuousWithinAt.congr_of_eventuallyEq h.1 h₁ hx, _⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq h.2
  · have :
      (extChartAt I x).symm ⁻¹' {y | f₁ y = f y} ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin I x h₁
    apply Filter.mem_of_superset this fun y => _
    simp (config := { contextual := true }) only [hx, mfld_simps]
  · simp only [hx, mfld_simps]

theorem HasMFDerivWithinAt.congr_mono (h : HasMFDerivWithinAt I I' f s x f')
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasMFDerivWithinAt I I' f₁ t x f' :=
  (h.mono h₁).congr_of_eventuallyEq (Filter.mem_inf_of_right ht) hx

theorem HasMFDerivAt.congr_of_eventuallyEq (h : HasMFDerivAt I I' f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasMFDerivAt I I' f₁ x f' := by
  rw [← hasMFDerivWithinAt_univ] at h ⊢
  apply h.congr_of_eventuallyEq _ (mem_of_mem_nhds h₁ : _)
  rwa [nhdsWithin_univ]

theorem MDifferentiableWithinAt.congr_of_eventuallyEq (h : MDifferentiableWithinAt I I' f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : MDifferentiableWithinAt I I' f₁ s x :=
  (h.hasMFDerivWithinAt.congr_of_eventuallyEq h₁ hx).mdifferentiableWithinAt

variable (I I')

theorem Filter.EventuallyEq.mdifferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDifferentiableWithinAt I I' f s x ↔ MDifferentiableWithinAt I I' f₁ s x := by
  constructor
  · intro h
    apply h.congr_of_eventuallyEq h₁ hx
  · intro h
    apply h.congr_of_eventuallyEq _ hx.symm
    apply h₁.mono
    intro y
    apply Eq.symm

variable {I I'}

theorem MDifferentiableWithinAt.congr_mono (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
    MDifferentiableWithinAt I I' f₁ t x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx h₁).mdifferentiableWithinAt

theorem MDifferentiableWithinAt.congr (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) : MDifferentiableWithinAt I I' f₁ s x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx (Subset.refl _)).mdifferentiableWithinAt

theorem MDifferentiableOn.congr_mono (h : MDifferentiableOn I I' f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : MDifferentiableOn I I' f₁ t := fun x hx =>
  (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

theorem MDifferentiableAt.congr_of_eventuallyEq (h : MDifferentiableAt I I' f x)
    (hL : f₁ =ᶠ[𝓝 x] f) : MDifferentiableAt I I' f₁ x :=
  (h.hasMFDerivAt.congr_of_eventuallyEq hL).mdifferentiableAt

theorem MDifferentiableWithinAt.mfderivWithin_congr_mono (h : MDifferentiableWithinAt I I' f s x)
    (hs : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueMDiffWithinAt I t x) (h₁ : t ⊆ s) :
    mfderivWithin I I' f₁ t x = (mfderivWithin I I' f s x : _) :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt hs hx h₁).mfderivWithin hxt

theorem Filter.EventuallyEq.mfderivWithin_eq (hs : UniqueMDiffWithinAt I s x) (hL : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : mfderivWithin I I' f₁ s x = (mfderivWithin I I' f s x : _) := by
  by_cases h : MDifferentiableWithinAt I I' f s x
  · exact (h.hasMFDerivWithinAt.congr_of_eventuallyEq hL hx).mfderivWithin hs
  · unfold mfderivWithin
    rw [if_neg h, if_neg]
    rwa [← hL.mdifferentiableWithinAt_iff I I' hx]

theorem mfderivWithin_congr (hs : UniqueMDiffWithinAt I s x) (hL : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : mfderivWithin I I' f₁ s x = (mfderivWithin I I' f s x : _) :=
  Filter.EventuallyEq.mfderivWithin_eq hs (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

theorem tangentMapWithin_congr (h : ∀ x ∈ s, f x = f₁ x) (p : TangentBundle I M) (hp : p.1 ∈ s)
    (hs : UniqueMDiffWithinAt I s p.1) :
    tangentMapWithin I I' f s p = tangentMapWithin I I' f₁ s p := by
  refine TotalSpace.ext _ _ (h p.1 hp) ?_
  -- This used to be `simp only`, but we need `erw` after leanprover/lean4#2644
  rw [tangentMapWithin, h p.1 hp, tangentMapWithin, mfderivWithin_congr hs h (h _ hp)]

theorem Filter.EventuallyEq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) :
    mfderiv I I' f₁ x = (mfderiv I I' f x : _) := by
  have A : f₁ x = f x := (mem_of_mem_nhds hL : _)
  rw [← mfderivWithin_univ, ← mfderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.mfderivWithin_eq (uniqueMDiffWithinAt_univ I) A

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)` is
definitionally equal to `E'`. -/
theorem mfderiv_congr_point {x' : M} (h : x = x') :
    @Eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f x') := by subst h; rfl

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)` is
definitionally equal to `E'`. -/
theorem mfderiv_congr {f' : M → M'} (h : f = f') :
    @Eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f' x) := by subst h; rfl

/-! ### Composition lemmas -/

theorem writtenInExtChartAt_comp (h : ContinuousWithinAt f s x) :
    {y | writtenInExtChartAt I I'' x (g ∘ f) y =
          (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f) y} ∈
      𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x := by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (extChartAt_preimage_mem_nhdsWithin I x
        (h.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _ _)))
  mfld_set_tac

variable (x)

theorem HasMFDerivWithinAt.comp (hg : HasMFDerivWithinAt I' I'' g u (f x) g')
    (hf : HasMFDerivWithinAt I I' f s x f') (hst : s ⊆ f ⁻¹' u) :
    HasMFDerivWithinAt I I'' (g ∘ f) s x (g'.comp f') := by
  refine' ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, _⟩
  have A :
    HasFDerivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E →L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x) := by
    have :
      (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' (f x)).source) ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin I x
        (hf.1.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _ _))
    unfold HasMFDerivWithinAt at *
    rw [← hasFDerivWithinAt_inter' this, ← extChartAt_preimage_inter_eq] at hf ⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by
      simp only [mfld_simps]
    rw [← this] at hg
    apply HasFDerivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chartAt H x).symm : H → M) (I.symm y)) ∈ u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventuallyEq (writtenInExtChartAt_comp hf.1)
  simp only [mfld_simps]

/-- The chain rule. -/
theorem HasMFDerivAt.comp (hg : HasMFDerivAt I' I'' g (f x) g') (hf : HasMFDerivAt I I' f x f') :
    HasMFDerivAt I I'' (g ∘ f) x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

theorem HasMFDerivAt.comp_hasMFDerivWithinAt (hg : HasMFDerivAt I' I'' g (f x) g')
    (hf : HasMFDerivWithinAt I I' f s x f') :
    HasMFDerivWithinAt I I'' (g ∘ f) s x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

theorem MDifferentiableWithinAt.comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMFDerivWithinAt I I' f s x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMFDerivWithinAt I' I'' g u (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMFDerivWithinAt.comp x G F h).mdifferentiableWithinAt

theorem MDifferentiableAt.comp (hg : MDifferentiableAt I' I'' g (f x))
    (hf : MDifferentiableAt I I' f x) : MDifferentiableAt I I'' (g ∘ f) x :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mdifferentiableAt

theorem mfderivWithin_comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderivWithin I' I'' g u (f x)).comp (mfderivWithin I I' f s x) := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact HasMFDerivWithinAt.comp x hg.hasMFDerivWithinAt hf.hasMFDerivWithinAt h

theorem mfderiv_comp (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.hasMFDerivAt hf.hasMFDerivAt

theorem mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDifferentiableAt I' I'' g y)
    (hf : MDifferentiableAt I I' f x) (hy : f x = y) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  subst hy; exact mfderiv_comp x hg hf

theorem MDifferentiableOn.comp (hg : MDifferentiableOn I' I'' g u) (hf : MDifferentiableOn I I' f s)
    (st : s ⊆ f ⁻¹' u) : MDifferentiableOn I I'' (g ∘ f) s := fun x hx =>
  MDifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

theorem MDifferentiable.comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
    MDifferentiable I I'' (g ∘ f) := fun x => MDifferentiableAt.comp x (hg (f x)) (hf x)

theorem tangentMapWithin_comp_at (p : TangentBundle I M)
    (hg : MDifferentiableWithinAt I' I'' g u (f p.1)) (hf : MDifferentiableWithinAt I I' f s p.1)
    (h : s ⊆ f ⁻¹' u) (hps : UniqueMDiffWithinAt I s p.1) :
    tangentMapWithin I I'' (g ∘ f) s p =
      tangentMapWithin I' I'' g u (tangentMapWithin I I' f s p) := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_comp p.1 hg hf h hps]
  rfl

theorem tangentMap_comp_at (p : TangentBundle I M) (hg : MDifferentiableAt I' I'' g (f p.1))
    (hf : MDifferentiableAt I I' f p.1) :
    tangentMap I I'' (g ∘ f) p = tangentMap I' I'' g (tangentMap I I' f p) := by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl

theorem tangentMap_comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
    tangentMap I I'' (g ∘ f) = tangentMap I' I'' g ∘ tangentMap I I' f := by
  ext p : 1; exact tangentMap_comp_at _ (hg _) (hf _)

end DerivativesProperties

section MFDerivFderiv

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Frechet derivative `fderiv`. In this section, we prove
this and related statements.
-/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'}
  {s : Set E} {x : E}

theorem uniqueMDiffWithinAt_iff_uniqueDiffWithinAt :
    UniqueMDiffWithinAt 𝓘(𝕜, E) s x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp only [UniqueMDiffWithinAt, mfld_simps]

alias ⟨UniqueMDiffWithinAt.uniqueDiffWithinAt, UniqueDiffWithinAt.uniqueMDiffWithinAt⟩ :=
  uniqueMDiffWithinAt_iff_uniqueDiffWithinAt

theorem uniqueMDiffOn_iff_uniqueDiffOn : UniqueMDiffOn 𝓘(𝕜, E) s ↔ UniqueDiffOn 𝕜 s := by
  simp [UniqueMDiffOn, UniqueDiffOn, uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]

alias ⟨UniqueMDiffOn.uniqueDiffOn, UniqueDiffOn.uniqueMDiffOn⟩ := uniqueMDiffOn_iff_uniqueDiffOn

-- porting note: was `@[simp, mfld_simps]` but `simp` can prove it
theorem writtenInExtChartAt_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f = f :=
  rfl

theorem hasMFDerivWithinAt_iff_hasFDerivWithinAt {f'} :
    HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f' ↔ HasFDerivWithinAt f f' s x := by
  simpa only [HasMFDerivWithinAt, and_iff_right_iff_imp, mfld_simps] using
    HasFDerivWithinAt.continuousWithinAt

alias ⟨HasMFDerivWithinAt.hasFDerivWithinAt, HasFDerivWithinAt.hasMFDerivWithinAt⟩ :=
  hasMFDerivWithinAt_iff_hasFDerivWithinAt

theorem hasMFDerivAt_iff_hasFDerivAt {f'} :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f' ↔ HasFDerivAt f f' x := by
  rw [← hasMFDerivWithinAt_univ, hasMFDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt_univ]

alias ⟨HasMFDerivAt.hasFDerivAt, HasFDerivAt.hasMFDerivAt⟩ := hasMFDerivAt_iff_hasFDerivAt

/-- For maps between vector spaces, `MDifferentiableWithinAt` and `DifferentiableWithinAt`
coincide -/
theorem mdifferentiableWithinAt_iff_differentiableWithinAt :
    MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [MDifferentiableWithinAt, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousWithinAt, H⟩⟩

alias ⟨MDifferentiableWithinAt.differentiableWithinAt,
    DifferentiableWithinAt.mdifferentiableWithinAt⟩ :=
  mdifferentiableWithinAt_iff_differentiableWithinAt

/-- For maps between vector spaces, `MDifferentiableAt` and `DifferentiableAt` coincide -/
theorem mdifferentiableAt_iff_differentiableAt :
    MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x ↔ DifferentiableAt 𝕜 f x := by
  simp only [MDifferentiableAt, differentiableWithinAt_univ, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousAt, H⟩⟩

alias ⟨MDifferentiableAt.differentiableAt, DifferentiableAt.mdifferentiableAt⟩ :=
  mdifferentiableAt_iff_differentiableAt

/-- For maps between vector spaces, `MDifferentiableOn` and `DifferentiableOn` coincide -/
theorem mdifferentiableOn_iff_differentiableOn :
    MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s ↔ DifferentiableOn 𝕜 f s := by
  simp only [MDifferentiableOn, DifferentiableOn,
    mdifferentiableWithinAt_iff_differentiableWithinAt]

alias ⟨MDifferentiableOn.differentiableOn, DifferentiableOn.mdifferentiableOn⟩ :=
  mdifferentiableOn_iff_differentiableOn

/-- For maps between vector spaces, `MDifferentiable` and `Differentiable` coincide -/
theorem mdifferentiable_iff_differentiable :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f ↔ Differentiable 𝕜 f := by
  simp only [MDifferentiable, Differentiable, mdifferentiableAt_iff_differentiableAt]

alias ⟨MDifferentiable.differentiable, Differentiable.mdifferentiable⟩ :=
  mdifferentiable_iff_differentiable

/-- For maps between vector spaces, `mfderivWithin` and `fderivWithin` coincide -/
@[simp]
theorem mfderivWithin_eq_fderivWithin :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = fderivWithin 𝕜 f s x := by
  by_cases h : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x
  · simp only [mfderivWithin, h, if_pos, mfld_simps]
  · simp only [mfderivWithin, h, if_neg, not_false_iff]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at h
    exact (fderivWithin_zero_of_not_differentiableWithinAt h).symm

/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide -/
@[simp]
theorem mfderiv_eq_fderiv : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = fderiv 𝕜 f x := by
  rw [← mfderivWithin_univ, ← fderivWithin_univ]
  exact mfderivWithin_eq_fderivWithin

end MFDerivFderiv

section SpecificFunctions

/-! ### Differentiability of specific functions -/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M'] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] (I'' : ModelWithCorners 𝕜 E'' H'') {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I'' M'']

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = f :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = f :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x (f : E →L[𝕜] E') :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x (f : E →L[𝕜] E') :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = (f : E →L[𝕜] E') :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/

theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt I I (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) := by
  refine' ⟨continuousAt_id, _⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y
  · apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin I x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]

theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivWithinAt I I (@id M) s x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) :=
  (hasMFDerivAt_id I x).hasMFDerivWithinAt

theorem mdifferentiableAt_id : MDifferentiableAt I I (@id M) x :=
  (hasMFDerivAt_id I x).mdifferentiableAt

theorem mdifferentiableWithinAt_id : MDifferentiableWithinAt I I (@id M) s x :=
  (mdifferentiableAt_id I).mdifferentiableWithinAt

theorem mdifferentiable_id : MDifferentiable I I (@id M) := fun _ => mdifferentiableAt_id I

theorem mdifferentiableOn_id : MDifferentiableOn I I (@id M) s :=
  (mdifferentiable_id I).mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_id : mfderiv I I (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  HasMFDerivAt.mfderiv (hasMFDerivAt_id I x)

theorem mfderivWithin_id (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I (@id M) s x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  rw [MDifferentiable.mfderivWithin (mdifferentiableAt_id I) hxs]
  exact mfderiv_id I

@[simp, mfld_simps]
theorem tangentMap_id : tangentMap I I (id : M → M) = id := by ext1 ⟨x, v⟩; simp [tangentMap]

theorem tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffWithinAt I s p.proj) :
    tangentMapWithin I I (id : M → M) s p = p := by
  simp only [tangentMapWithin, id.def]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs

end id

section Const

/-! #### Constants -/


variable {c : M'}

theorem hasMFDerivAt_const (c : M') (x : M) :
    HasMFDerivAt I I' (fun _ : M => c) x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) := by
  refine' ⟨continuous_const.continuousAt, _⟩
  simp only [writtenInExtChartAt, (· ∘ ·), hasFDerivWithinAt_const]

theorem hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) :
    HasMFDerivWithinAt I I' (fun _ : M => c) s x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMFDerivAt_const I I' c x).hasMFDerivWithinAt

theorem mdifferentiableAt_const : MDifferentiableAt I I' (fun _ : M => c) x :=
  (hasMFDerivAt_const I I' c x).mdifferentiableAt

theorem mdifferentiableWithinAt_const : MDifferentiableWithinAt I I' (fun _ : M => c) s x :=
  (mdifferentiableAt_const I I').mdifferentiableWithinAt

theorem mdifferentiable_const : MDifferentiable I I' fun _ : M => c := fun _ =>
  mdifferentiableAt_const I I'

theorem mdifferentiableOn_const : MDifferentiableOn I I' (fun _ : M => c) s :=
  (mdifferentiable_const I I').mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_const :
    mfderiv I I' (fun _ : M => c) x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  HasMFDerivAt.mfderiv (hasMFDerivAt_const I I' c x)

theorem mfderivWithin_const (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I' (fun _ : M => c) s x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMFDerivWithinAt_const _ _ _ _ _).mfderivWithin hxs

end Const

section Prod

/-! ### Operations on the product of two manifolds -/

theorem hasMFDerivAt_fst (x : M × M') :
    HasMFDerivAt (I.prod I') I Prod.fst x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) := by
  refine' ⟨continuous_fst.continuousAt, _⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin (I.prod I') x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I x.1).right_inv hy.1
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_fst this
  -- porting note: next line was `simp only [mfld_simps]`
  exact (extChartAt I x.1).right_inv <| (extChartAt I x.1).map_source (mem_extChartAt_source _ _)

theorem hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') :
    HasMFDerivWithinAt (I.prod I') I Prod.fst s x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  (hasMFDerivAt_fst I I' x).hasMFDerivWithinAt

theorem mdifferentiableAt_fst {x : M × M'} : MDifferentiableAt (I.prod I') I Prod.fst x :=
  (hasMFDerivAt_fst I I' x).mdifferentiableAt

theorem mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} :
    MDifferentiableWithinAt (I.prod I') I Prod.fst s x :=
  (mdifferentiableAt_fst I I').mdifferentiableWithinAt

theorem mdifferentiable_fst : MDifferentiable (I.prod I') I (Prod.fst : M × M' → M) := fun _ =>
  mdifferentiableAt_fst I I'

theorem mdifferentiableOn_fst {s : Set (M × M')} : MDifferentiableOn (I.prod I') I Prod.fst s :=
  (mdifferentiable_fst I I').mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_fst {x : M × M'} :
    mfderiv (I.prod I') I Prod.fst x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  (hasMFDerivAt_fst I I' x).mfderiv

theorem mfderivWithin_fst {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffWithinAt (I.prod I') s x) :
    mfderivWithin (I.prod I') I Prod.fst s x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  by rw [MDifferentiable.mfderivWithin (mdifferentiableAt_fst I I') hxs]; exact mfderiv_fst I I'

@[simp, mfld_simps]
theorem tangentMap_prod_fst {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap (I.prod I') I Prod.fst p = ⟨p.proj.1, p.2.1⟩ := by
  -- porting note: `rfl` wasn't needed
  simp [tangentMap]; rfl

theorem tangentMapWithin_prod_fst {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffWithinAt (I.prod I') s p.proj) :
    tangentMapWithin (I.prod I') I Prod.fst s p = ⟨p.proj.1, p.2.1⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs

theorem hasMFDerivAt_snd (x : M × M') :
    HasMFDerivAt (I.prod I') I' Prod.snd x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) := by
  refine' ⟨continuous_snd.continuousAt, _⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin (I.prod I') x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I' x.2).right_inv hy.2
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_snd this
  -- porting note: the next line was `simp only [mfld_simps]`
  exact (extChartAt I' x.2).right_inv <| (extChartAt I' x.2).map_source (mem_extChartAt_source _ _)

theorem hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') :
    HasMFDerivWithinAt (I.prod I') I' Prod.snd s x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  (hasMFDerivAt_snd I I' x).hasMFDerivWithinAt

theorem mdifferentiableAt_snd {x : M × M'} : MDifferentiableAt (I.prod I') I' Prod.snd x :=
  (hasMFDerivAt_snd I I' x).mdifferentiableAt

theorem mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} :
    MDifferentiableWithinAt (I.prod I') I' Prod.snd s x :=
  (mdifferentiableAt_snd I I').mdifferentiableWithinAt

theorem mdifferentiable_snd : MDifferentiable (I.prod I') I' (Prod.snd : M × M' → M') := fun _ =>
  mdifferentiableAt_snd I I'

theorem mdifferentiableOn_snd {s : Set (M × M')} : MDifferentiableOn (I.prod I') I' Prod.snd s :=
  (mdifferentiable_snd I I').mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_snd {x : M × M'} :
    mfderiv (I.prod I') I' Prod.snd x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  (hasMFDerivAt_snd I I' x).mfderiv

theorem mfderivWithin_snd {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffWithinAt (I.prod I') s x) :
    mfderivWithin (I.prod I') I' Prod.snd s x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  by rw [MDifferentiable.mfderivWithin (mdifferentiableAt_snd I I') hxs]; exact mfderiv_snd I I'

@[simp, mfld_simps]
theorem tangentMap_prod_snd {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap (I.prod I') I' Prod.snd p = ⟨p.proj.2, p.2.2⟩ := by
  -- porting note: `rfl` wasn't needed
  simp [tangentMap]; rfl

theorem tangentMapWithin_prod_snd {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffWithinAt (I.prod I') s p.proj) :
    tangentMapWithin (I.prod I') I' Prod.snd s p = ⟨p.proj.2, p.2.2⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd]
  · rcases p with ⟨⟩; rfl
  · exact hs

variable {I I' I''}

theorem MDifferentiableAt.mfderiv_prod {f : M → M'} {g : M → M''} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I I'' g x) :
    mfderiv I (I'.prod I'') (fun x => (f x, g x)) x =
      (mfderiv I I' f x).prod (mfderiv I I'' g x) := by
  classical
  simp_rw [mfderiv, if_pos (hf.prod_mk hg), if_pos hf, if_pos hg]
  exact hf.2.fderivWithin_prod hg.2 (I.unique_diff _ (mem_range_self _))

variable (I I' I'')

theorem mfderiv_prod_left {x₀ : M} {y₀ : M'} :
    mfderiv I (I.prod I') (fun x => (x, y₀)) x₀ =
      ContinuousLinearMap.inl 𝕜 (TangentSpace I x₀) (TangentSpace I' y₀) := by
  refine' ((mdifferentiableAt_id I).mfderiv_prod (mdifferentiableAt_const I I')).trans _
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inl]

theorem mfderiv_prod_right {x₀ : M} {y₀ : M'} :
    mfderiv I' (I.prod I') (fun y => (x₀, y)) y₀ =
      ContinuousLinearMap.inr 𝕜 (TangentSpace I x₀) (TangentSpace I' y₀) := by
  refine' ((mdifferentiableAt_const I' I).mfderiv_prod (mdifferentiableAt_id I')).trans _
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inr]

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. -/
theorem mfderiv_prod_eq_add {f : M × M' → M''} {p : M × M'}
    (hf : MDifferentiableAt (I.prod I') I'' f p) :
    mfderiv (I.prod I') I'' f p =
      show E × E' →L[𝕜] E'' from
        mfderiv (I.prod I') I'' (fun z : M × M' => f (z.1, p.2)) p +
          mfderiv (I.prod I') I'' (fun z : M × M' => f (p.1, z.2)) p := by
  dsimp only
  erw [mfderiv_comp_of_eq hf ((mdifferentiableAt_fst I I').prod_mk (mdifferentiableAt_const _ _))
      rfl,
    mfderiv_comp_of_eq hf ((mdifferentiableAt_const _ _).prod_mk (mdifferentiableAt_snd I I')) rfl,
    ← ContinuousLinearMap.comp_add,
    (mdifferentiableAt_fst I I').mfderiv_prod (mdifferentiableAt_const (I.prod I') I'),
    (mdifferentiableAt_const (I.prod I') I).mfderiv_prod (mdifferentiableAt_snd I I'), mfderiv_fst,
    mfderiv_snd, mfderiv_const, mfderiv_const]
  symm
  convert ContinuousLinearMap.comp_id <| mfderiv (.prod I I') I'' f (p.1, p.2)
  · exact ContinuousLinearMap.coprod_inl_inr

end Prod

section Arithmetic

/-! #### Arithmetic

Note that in the `HasMFDerivAt` lemmas there is an abuse of the defeq between `E'` and
`TangentSpace 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
 -/

section Group

variable {I} {z : M} {f g : M → E'} {f' g' : TangentSpace I z →L[𝕜] E'}

theorem HasMFDerivAt.add (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f')
    (hg : HasMFDerivAt I 𝓘(𝕜, E') g z g') : HasMFDerivAt I 𝓘(𝕜, E') (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem MDifferentiableAt.add (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) : MDifferentiableAt I 𝓘(𝕜, E') (f + g) z :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiable.add (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E') g) : MDifferentiable I 𝓘(𝕜, E') (f + g) := fun x =>
  (hf x).add (hg x)

-- porting note: forcing types using `@Add.add`
theorem mfderiv_add (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) :
    (mfderiv I 𝓘(𝕜, E') (f + g) z : TangentSpace I z →L[𝕜] E') =
      @Add.add (TangentSpace I z →L[𝕜] E') _ (mfderiv I 𝓘(𝕜, E') f z) (mfderiv I 𝓘(𝕜, E') g z) :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

theorem HasMFDerivAt.const_smul (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f') (s : 𝕜) :
    HasMFDerivAt I 𝓘(𝕜, E') (s • f) z (s • f') :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩

theorem MDifferentiableAt.const_smul (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    MDifferentiableAt I 𝓘(𝕜, E') (s • f) z :=
  (hf.hasMFDerivAt.const_smul s).mdifferentiableAt

theorem MDifferentiable.const_smul (s : 𝕜) (hf : MDifferentiable I 𝓘(𝕜, E') f) :
    MDifferentiable I 𝓘(𝕜, E') (s • f) := fun x => (hf x).const_smul s

theorem const_smul_mfderiv (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    (mfderiv I 𝓘(𝕜, E') (s • f) z : TangentSpace I z →L[𝕜] E') =
      (s • mfderiv I 𝓘(𝕜, E') f z : TangentSpace I z →L[𝕜] E') :=
  (hf.hasMFDerivAt.const_smul s).mfderiv

theorem HasMFDerivAt.neg (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f') :
    HasMFDerivAt I 𝓘(𝕜, E') (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩

theorem hasMFDerivAt_neg : HasMFDerivAt I 𝓘(𝕜, E') (-f) z (-f') ↔ HasMFDerivAt I 𝓘(𝕜, E') f z f' :=
  ⟨fun hf => by convert hf.neg <;> rw [neg_neg], fun hf => hf.neg⟩

theorem MDifferentiableAt.neg (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) :
    MDifferentiableAt I 𝓘(𝕜, E') (-f) z :=
  hf.hasMFDerivAt.neg.mdifferentiableAt

theorem mdifferentiableAt_neg :
    MDifferentiableAt I 𝓘(𝕜, E') (-f) z ↔ MDifferentiableAt I 𝓘(𝕜, E') f z :=
  ⟨fun hf => by convert hf.neg; rw [neg_neg], fun hf => hf.neg⟩

theorem MDifferentiable.neg (hf : MDifferentiable I 𝓘(𝕜, E') f) : MDifferentiable I 𝓘(𝕜, E') (-f) :=
  fun x => (hf x).neg

theorem mfderiv_neg (f : M → E') (x : M) :
    (mfderiv I 𝓘(𝕜, E') (-f) x : TangentSpace I x →L[𝕜] E') =
      (-mfderiv I 𝓘(𝕜, E') f x : TangentSpace I x →L[𝕜] E') := by
  simp_rw [mfderiv]
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, E') f x
  · exact hf.hasMFDerivAt.neg.mfderiv
  · rw [if_neg hf]; rw [← mdifferentiableAt_neg] at hf; rw [if_neg hf, neg_zero]

theorem HasMFDerivAt.sub (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f')
    (hg : HasMFDerivAt I 𝓘(𝕜, E') g z g') : HasMFDerivAt I 𝓘(𝕜, E') (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem MDifferentiableAt.sub (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) : MDifferentiableAt I 𝓘(𝕜, E') (f - g) z :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiable.sub (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E') g) : MDifferentiable I 𝓘(𝕜, E') (f - g) := fun x =>
  (hf x).sub (hg x)

theorem mfderiv_sub (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) :
    (mfderiv I 𝓘(𝕜, E') (f - g) z : TangentSpace I z →L[𝕜] E') =
      @Sub.sub (TangentSpace I z →L[𝕜] E') _ (mfderiv I 𝓘(𝕜, E') f z) (mfderiv I 𝓘(𝕜, E') g z) :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

end Group

section AlgebraOverRing

variable {I} {z : M} {F' : Type*} [NormedRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

theorem HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + p'.smulRight (q z) : E →L[𝕜] F') :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using hp.2.mul' hq.2⟩

theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + p'.smulRight (q z) : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt

theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p * q) s z :=
  (hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s := fun x hx =>
  (hp x hx).mul <| hq x hx

theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q) := fun x =>
  (hp x).mul (hq x)

end AlgebraOverRing

section AlgebraOverCommRing

variable {I} {z : M} {F' : Type*} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

theorem HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + q z • p' : E →L[𝕜] F') := by
  convert hp.mul' hq; ext _; apply mul_comm

theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt

end AlgebraOverCommRing

end Arithmetic

namespace ModelWithCorners

/-! #### Model with corners -/


protected theorem hasMFDerivAt {x} : HasMFDerivAt I 𝓘(𝕜, E) I x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousAt, (hasFDerivWithinAt_id _ _).congr' I.rightInvOn (mem_range_self _)⟩

protected theorem hasMFDerivWithinAt {s x} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x (ContinuousLinearMap.id _ _) :=
  I.hasMFDerivAt.hasMFDerivWithinAt

protected theorem mdifferentiableWithinAt {s x} : MDifferentiableWithinAt I 𝓘(𝕜, E) I s x :=
  I.hasMFDerivWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableAt {x} : MDifferentiableAt I 𝓘(𝕜, E) I x :=
  I.hasMFDerivAt.mdifferentiableAt

protected theorem mdifferentiableOn {s} : MDifferentiableOn I 𝓘(𝕜, E) I s := fun _ _ =>
  I.mdifferentiableWithinAt

protected theorem mdifferentiable : MDifferentiable I 𝓘(𝕜, E) I := fun _ => I.mdifferentiableAt

theorem hasMFDerivWithinAt_symm {x} (hx : x ∈ range I) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I I.symm (range I) x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousWithinAt_symm,
    (hasFDerivWithinAt_id _ _).congr' (fun _y hy => I.rightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩

theorem mdifferentiableOn_symm : MDifferentiableOn 𝓘(𝕜, E) I I.symm (range I) := fun _x hx =>
  (I.hasMFDerivWithinAt_symm hx).mdifferentiableWithinAt

end ModelWithCorners

section Charts

variable {e : LocalHomeomorph M H}

theorem mdifferentiableAt_atlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) :
    MDifferentiableAt I I e x := by
  refine' ⟨(e.continuousOn x hx).continuousAt (IsOpen.mem_nhds e.open_source hx), _⟩
  have mem :
    I ((chartAt H x : M → H) x) ∈ I.symm ⁻¹' ((chartAt H x).symm ≫ₕ e).source ∩ range I := by
    simp only [hx, mfld_simps]
  have : (chartAt H x).symm.trans e ∈ contDiffGroupoid ∞ I :=
    HasGroupoid.compatible (chart_mem_atlas H x) h
  have A :
    ContDiffOn 𝕜 ∞ (I ∘ (chartAt H x).symm.trans e ∘ I.symm)
      (I.symm ⁻¹' ((chartAt H x).symm.trans e).source ∩ range I) :=
    this.1
  have B := A.differentiableOn le_top (I ((chartAt H x : M → H) x)) mem
  simp only [mfld_simps] at B
  rw [inter_comm, differentiableWithinAt_inter] at B
  · simpa only [mfld_simps]
  · apply IsOpen.mem_nhds ((LocalHomeomorph.open_source _).preimage I.continuous_symm) mem.1

theorem mdifferentiableOn_atlas (h : e ∈ atlas H M) : MDifferentiableOn I I e e.source :=
  fun _x hx => (mdifferentiableAt_atlas I h hx).mdifferentiableWithinAt

theorem mdifferentiableAt_atlas_symm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) :
    MDifferentiableAt I I e.symm x := by
  refine' ⟨(e.continuousOn_symm x hx).continuousAt (IsOpen.mem_nhds e.open_target hx), _⟩
  have mem : I x ∈ I.symm ⁻¹' (e.symm ≫ₕ chartAt H (e.symm x)).source ∩ range I := by
    simp only [hx, mfld_simps]
  have : e.symm.trans (chartAt H (e.symm x)) ∈ contDiffGroupoid ∞ I :=
    HasGroupoid.compatible h (chart_mem_atlas H _)
  have A :
    ContDiffOn 𝕜 ∞ (I ∘ e.symm.trans (chartAt H (e.symm x)) ∘ I.symm)
      (I.symm ⁻¹' (e.symm.trans (chartAt H (e.symm x))).source ∩ range I) :=
    this.1
  have B := A.differentiableOn le_top (I x) mem
  simp only [mfld_simps] at B
  rw [inter_comm, differentiableWithinAt_inter] at B
  · simpa only [mfld_simps]
  · apply IsOpen.mem_nhds ((LocalHomeomorph.open_source _).preimage I.continuous_symm) mem.1

theorem mdifferentiableOn_atlas_symm (h : e ∈ atlas H M) : MDifferentiableOn I I e.symm e.target :=
  fun _x hx => (mdifferentiableAt_atlas_symm I h hx).mdifferentiableWithinAt

theorem mdifferentiable_of_mem_atlas (h : e ∈ atlas H M) : e.MDifferentiable I I :=
  ⟨mdifferentiableOn_atlas I h, mdifferentiableOn_atlas_symm I h⟩

theorem mdifferentiable_chart (x : M) : (chartAt H x).MDifferentiable I I :=
  mdifferentiable_of_mem_atlas _ (chart_mem_atlas _ _)

/-- The derivative of the chart at a base point is the chart of the tangent bundle, composed with
the identification between the tangent bundle of the model space and the product space. -/
theorem tangentMap_chart {p q : TangentBundle I M} (h : q.1 ∈ (chartAt H p.1).source) :
    tangentMap I I (chartAt H p.1) q =
      (TotalSpace.toProd _ _).symm
        ((chartAt (ModelProd H E) p : TangentBundle I M → ModelProd H E) q) := by
  dsimp [tangentMap]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · exact mdifferentiableAt_atlas _ (chart_mem_atlas _ _) h

/-- The derivative of the inverse of the chart at a base point is the inverse of the chart of the
tangent bundle, composed with the identification between the tangent bundle of the model space and
the product space. -/
theorem tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H}
    (h : q.1 ∈ (chartAt H p.1).target) :
    tangentMap I I (chartAt H p.1).symm q =
      (chartAt (ModelProd H E) p).symm (TotalSpace.toProd H E q) := by
  dsimp only [tangentMap]
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas_symm _ (chart_mem_atlas _ _) h)]
  simp only [ContinuousLinearMap.coe_coe, TangentBundle.chartAt, h, tangentBundleCore,
    mfld_simps, (· ∘ ·)]
  -- `simp` fails to apply `LocalEquiv.prod_symm` with `ModelProd`
  congr
  exact ((chartAt H (TotalSpace.proj p)).right_inv h).symm

end Charts

end SpecificFunctions

/-! ### Differentiable local homeomorphisms -/

namespace LocalHomeomorph.MDifferentiable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] {e : LocalHomeomorph M M'}
  (he : e.MDifferentiable I I') {e' : LocalHomeomorph M' M''}

nonrec theorem symm : e.symm.MDifferentiable I' I := he.symm

protected theorem mdifferentiableAt {x : M} (hx : x ∈ e.source) : MDifferentiableAt I I' e x :=
  (he.1 x hx).mdifferentiableAt (IsOpen.mem_nhds e.open_source hx)

theorem mdifferentiableAt_symm {x : M'} (hx : x ∈ e.target) : MDifferentiableAt I' I e.symm x :=
  (he.2 x hx).mdifferentiableAt (IsOpen.mem_nhds e.open_target hx)

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']
  [SmoothManifoldWithCorners I'' M'']

theorem symm_comp_deriv {x : M} (hx : x ∈ e.source) :
    (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have : mfderiv I I (e.symm ∘ e) x = (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  rw [← this]
  have : mfderiv I I (_root_.id : M → M) x = ContinuousLinearMap.id _ _ := mfderiv_id I
  rw [← this]
  apply Filter.EventuallyEq.mfderiv_eq
  have : e.source ∈ 𝓝 x := IsOpen.mem_nhds e.open_source hx
  exact Filter.mem_of_superset this (by mfld_set_tac)

theorem comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
    (mfderiv I I' e (e.symm x)).comp (mfderiv I' I e.symm x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I' x) :=
  he.symm.symm_comp_deriv hx

/-- The derivative of a differentiable local homeomorphism, as a continuous linear equivalence
between the tangent spaces at `x` and `e x`. -/
protected def mfderiv {x : M} (hx : x ∈ e.source) : TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv I I' e x with
    invFun := mfderiv I' I e.symm (e x)
    continuous_toFun := (mfderiv I I' e x).cont
    continuous_invFun := (mfderiv I' I e.symm (e x)).cont
    left_inv := fun y => by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x →L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw [← this, ← he.symm_comp_deriv hx]
    right_inv := fun y => by
      have :
        (ContinuousLinearMap.id 𝕜 _ : TangentSpace I' (e x) →L[𝕜] TangentSpace I' (e x)) y = y :=
        rfl
      conv_rhs => rw [← this, ← he.comp_symm_deriv (e.map_source hx)]
      rw [e.left_inv hx]
      rfl }

theorem mfderiv_bijective {x : M} (hx : x ∈ e.source) : Function.Bijective (mfderiv I I' e x) :=
  (he.mfderiv hx).bijective

theorem mfderiv_injective {x : M} (hx : x ∈ e.source) : Function.Injective (mfderiv I I' e x) :=
  (he.mfderiv hx).injective

theorem mfderiv_surjective {x : M} (hx : x ∈ e.source) : Function.Surjective (mfderiv I I' e x) :=
  (he.mfderiv hx).surjective

theorem ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) : LinearMap.ker (mfderiv I I' e x) = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker

theorem range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) : LinearMap.range (mfderiv I I' e x) = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range

theorem range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) : range (mfderiv I I' e x) = univ :=
  (he.mfderiv_surjective hx).range_eq

theorem trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I'' := by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiableAt hx.2).comp _ (he.mdifferentiableAt hx.1)).mdifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiableAt hx.2).comp _
          (he'.symm.mdifferentiableAt hx.1)).mdifferentiableWithinAt

end LocalHomeomorph.MDifferentiable

/-! ### Differentiability of `extChartAt` -/

section extChartAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {s : Set M} {x y : M}

theorem hasMFDerivAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt I 𝓘(𝕜, E) (extChartAt I x) y (mfderiv I I (chartAt H x) y : _) :=
  I.hasMFDerivAt.comp y ((mdifferentiable_chart I x).mdifferentiableAt h).hasMFDerivAt

theorem hasMFDerivWithinAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivWithinAt I 𝓘(𝕜, E) (extChartAt I x) s y (mfderiv I I (chartAt H x) y : _) :=
  (hasMFDerivAt_extChartAt I h).hasMFDerivWithinAt

theorem mdifferentiableAt_extChartAt (h : y ∈ (chartAt H x).source) :
    MDifferentiableAt I 𝓘(𝕜, E) (extChartAt I x) y :=
  (hasMFDerivAt_extChartAt I h).mdifferentiableAt

theorem mdifferentiableOn_extChartAt :
    MDifferentiableOn I 𝓘(𝕜, E) (extChartAt I x) (chartAt H x).source := fun _y hy =>
  (hasMFDerivWithinAt_extChartAt I hy).mdifferentiableWithinAt

end extChartAt

/-! ### Unique derivative sets in manifolds -/

section UniqueMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M'] {s : Set M}

/-- If `s` has the unique differential property at `x`, `f` is differentiable within `s` at x` and
its derivative has Dense range, then `f '' s` has the Unique differential property at `f x`. -/
theorem UniqueMDiffWithinAt.image_denseRange (hs : UniqueMDiffWithinAt I s x)
    {f : M → M'} {f' : E →L[𝕜] E'} (hf : HasMFDerivWithinAt I I' f s x f')
    (hd : DenseRange f') : UniqueMDiffWithinAt I' (f '' s) (f x) := by
  /- Rewrite in coordinates, apply `HasFDerivWithinAt.uniqueDiffWithinAt`. -/
  have := hs.inter' <| hf.1 (extChartAt_source_mem_nhds I' (f x))
  refine (((hf.2.mono ?sub1).uniqueDiffWithinAt this hd).mono ?sub2).congr_pt ?pt
  case pt => simp only [mfld_simps]
  case sub1 => mfld_set_tac
  case sub2 =>
    rintro _ ⟨y, ⟨⟨hys, hfy⟩, -⟩, rfl⟩
    exact ⟨⟨_, hys, ((extChartAt I' (f x)).left_inv hfy).symm⟩, mem_range_self _⟩

/-- If `s` has the unique differential, `f` is differentiable on `s` and its derivative at every
point of `s` has dense range, then `f '' s` has the unique differential property. This version
uses `HaMFDerivWithinAt` predicate. -/
theorem UniqueMDiffOn.image_denseRange' (hs : UniqueMDiffOn I s) {f : M → M'}
    {f' : M → E →L[𝕜] E'} (hf : ∀ x ∈ s, HasMFDerivWithinAt I I' f s x (f' x))
    (hd : ∀ x ∈ s, DenseRange (f' x)) :
    UniqueMDiffOn I' (f '' s) :=
  ball_image_iff.2 fun x hx ↦ (hs x hx).image_denseRange (hf x hx) (hd x hx)

/-- If `s` has the unique differential, `f` is differentiable on `s` and its derivative at every
point of `s` has dense range, then `f '' s` has the unique differential property. -/
theorem UniqueMDiffOn.image_denseRange (hs : UniqueMDiffOn I s) {f : M → M'}
    (hf : MDifferentiableOn I I' f s) (hd : ∀ x ∈ s, DenseRange (mfderivWithin I I' f s x)) :
    UniqueMDiffOn I' (f '' s) :=
  hs.image_denseRange' (fun x hx ↦ (hf x hx).hasMFDerivWithinAt) hd

protected theorem UniqueMDiffWithinAt.preimage_localHomeomorph (hs : UniqueMDiffWithinAt I s x)
    {e : LocalHomeomorph M M'} (he : e.MDifferentiable I I') (hx : x ∈ e.source) :
    UniqueMDiffWithinAt I' (e.target ∩ e.symm ⁻¹' s) (e x) := by
  rw [← e.image_source_inter_eq', inter_comm]
  exact (hs.inter (e.open_source.mem_nhds hx)).image_denseRange
    (he.mdifferentiableAt hx).hasMFDerivAt.hasMFDerivWithinAt
    (he.mfderiv_surjective hx).denseRange

/-- If a set has the unique differential property, then its image under a local
diffeomorphism also has the unique differential property. -/
theorem UniqueMDiffOn.uniqueMDiffOn_preimage (hs : UniqueMDiffOn I s) {e : LocalHomeomorph M M'}
    (he : e.MDifferentiable I I') : UniqueMDiffOn I' (e.target ∩ e.symm ⁻¹' s) := fun _x hx ↦
  e.right_inv hx.1 ▸ (hs _ hx.2).preimage_localHomeomorph he (e.map_target hx.1)

/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
theorem UniqueMDiffOn.uniqueDiffOn_target_inter (hs : UniqueMDiffOn I s) (x : M) :
    UniqueDiffOn 𝕜 ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) := by
  -- this is just a reformulation of `UniqueMDiffOn.uniqueMDiffOn_preimage`, using as `e`
  -- the local chart at `x`.
  apply UniqueMDiffOn.uniqueDiffOn
  rw [← LocalEquiv.image_source_inter_eq', inter_comm, extChartAt_source]
  exact (hs.inter (chartAt H x).open_source).image_denseRange'
    (fun y hy ↦ hasMFDerivWithinAt_extChartAt I hy.2)
    fun y hy ↦ ((mdifferentiable_chart _ _).mfderiv_surjective hy.2).denseRange

/-- When considering functions between manifolds, this statement shows up often. It entails
the unique differential of the pullback in extended charts of the set where the function can
be read in the charts. -/
theorem UniqueMDiffOn.uniqueDiffOn_inter_preimage (hs : UniqueMDiffOn I s) (x : M) (y : M')
    {f : M → M'} (hf : ContinuousOn f s) :
    UniqueDiffOn 𝕜
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) :=
  haveI : UniqueMDiffOn I (s ∩ f ⁻¹' (extChartAt I' y).source) := by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhdsWithin
    exact (isOpen_extChartAt_source I' y).mem_nhds hz.2
  this.uniqueDiffOn_target_inter _

open Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {Z : M → Type*}
  [TopologicalSpace (TotalSpace F Z)] [∀ b, TopologicalSpace (Z b)] [∀ b, AddCommMonoid (Z b)]
  [∀ b, Module 𝕜 (Z b)] [FiberBundle F Z] [VectorBundle 𝕜 F Z] [SmoothVectorBundle F Z I]

theorem Trivialization.mdifferentiable (e : Trivialization F (π F Z)) [MemTrivializationAtlas e] :
    e.toLocalHomeomorph.MDifferentiable (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) :=
  ⟨(e.smoothOn I).mdifferentiableOn, (e.smoothOn_symm I).mdifferentiableOn⟩

theorem UniqueMDiffWithinAt.smooth_bundle_preimage {p : TotalSpace F Z}
    (hs : UniqueMDiffWithinAt I s p.proj) :
    UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) p := by
  set e := trivializationAt F Z p.proj
  have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have : UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (s ×ˢ univ) (e p)
  · rw [← Prod.mk.eta (p := e p), FiberBundle.trivializationAt_proj_fst]
    exact hs.prod (uniqueMDiffWithinAt_univ _)
  rw [← e.left_inv hp]
  refine (this.preimage_localHomeomorph e.mdifferentiable.symm (e.map_source hp)).mono ?_
  rintro y ⟨hy, hys, -⟩
  rwa [LocalHomeomorph.symm_symm, e.coe_coe, e.coe_fst hy] at hys

variable (Z)

theorem UniqueMDiffWithinAt.smooth_bundle_preimage' {b : M} (hs : UniqueMDiffWithinAt I s b)
    (x : Z b) : UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) ⟨b, x⟩ :=
  hs.smooth_bundle_preimage (p := ⟨b, x⟩)

/-- In a smooth fiber bundle, the preimage under the projection of a set with
unique differential in the basis also has unique differential. -/
theorem UniqueMDiffOn.smooth_bundle_preimage (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) := fun _p hp ↦
  (hs _ hp).smooth_bundle_preimage

/-- The preimage under the projection from the tangent bundle of a set with unique differential in
the basis also has unique differential. -/
theorem UniqueMDiffOn.tangentBundle_proj_preimage (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn I.tangent (π E (TangentSpace I) ⁻¹' s) :=
  hs.smooth_bundle_preimage _

end UniqueMDiff
