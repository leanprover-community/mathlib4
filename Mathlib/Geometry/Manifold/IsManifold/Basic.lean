/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# `C^n` manifolds (possibly with boundary or corners)

A `C^n` manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are `C^n` maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are `C^n` when read in `E` (for any regularity `n : WithTop ℕ∞`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`.

Some texts assume manifolds to be Hausdorff and second countable. We (in mathlib) assume neither,
but add these assumptions later as needed. (Quite a few results still do not require them.)

## Main definitions

* `ModelWithCorners 𝕜 E H` :
  a structure containing information on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a `C^n` manifold with model space `H`, and model vector space `E`.
* `modelWithCornersSelf 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `contDiffGroupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of partial homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `IsManifold I n M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^n` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `HasGroupoid M (contDiffGroupoid n I)`.

We define a few constructions of smooth manifolds:
* every empty type is a smooth manifold
* the product of two smooth manifolds
* the disjoint union of two manifolds (over the same charted space)

As specific examples of models with corners, we define (in `Geometry.Manifold.Instances.Real`)
* `modelWithCornersEuclideanHalfSpace n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` for the model space used to
  define `n`-dimensional real manifolds without boundary
  (with notation `𝓡 n` in the locale `Manifold`)
* `modelWithCornersEuclideanHalfSpace n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `Manifold`)
* `modelWithCornersEuclideanQuadrant n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional `C^∞` real manifold without boundary,
one could use

  `variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
   [IsManifold (𝓡 n) ∞ M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n))`
and not on `EuclideanSpace ℝ (Fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E E} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]`

Here, `I.Boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `modelWithCornersSelf`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `modelWithCornersSelf ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(fun p : E × F ↦ (p.1, p.2))` is not defeq to the identity).
So, it is important to use the above incantation to maximize the applicability of theorems.

Even better, if the result should apply in a parallel way to smooth manifolds and to analytic
manifolds, the last typeclass should be replaced with `[IsManifold I n M]`
for `n : WithTop ℕ∞`.

We also define `TangentSpace I (x : M)` as a type synonym of `E`, and `TangentBundle I M` as a
type synonym for `Π (x : M), TangentSpace I x` (in the form of an
abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`). Apart from basic typeclasses on
`TangentSpace I x`, nothing is proved about them in this file, but it is useful to have them
available as definitions early on to get a clean import structure below. The smooth bundle structure
is defined in `VectorBundle.Tangent`, while the definition is used to talk about manifold
derivatives in `MFDeriv.Basic`, and neither file needs import the other.

## Implementation notes

We want to talk about manifolds modelled on a vector space, but also on manifolds with
boundary, modelled on a half space (or even manifolds with corners). For the latter examples,
we still want to define smooth functions, tangent bundles, and so on. As smooth functions are
well defined on vector spaces or subsets of these, one could take for model space a subtype of a
vector space. With the drawback that the whole vector space itself (which is the most basic
example) is not directly a subtype of itself: the inclusion of `univ : Set E` in `Set E` would
show up in the definition, instead of `id`.

A good abstraction covering both cases it to have a vector
space `E` (with basic example the Euclidean space), a model space `H` (with basic example the upper
half space), and an embedding of `H` into `E` (which can be the identity for `H = E`, or
`Subtype.val` for manifolds with corners). We say that the pair `(E, H)` with their embedding is a
model with corners, and we encompass all the relevant properties (in particular the fact that the
image of `H` in `E` should have unique differentials) in the definition of `ModelWithCorners`.

I have considered using the model with corners `I` as a typeclass argument, possibly `outParam`, to
get lighter notations later on, but it did not turn out right, as on `E × F` there are two natural
model with corners, the trivial (identity) one, and the product one, and they are not defeq and one
needs to indicate to Lean which one we want to use.
This means that when talking on objects on manifolds one will most often need to specify the model
with corners one is using. For instance, the tangent bundle will be `TangentBundle I M` and the
derivative will be `mfderiv I I' f`, instead of the more natural notations `TangentBundle 𝕜 M` and
`mfderiv 𝕜 f` (the field has to be explicit anyway, as some manifolds could be considered both as
real and complex manifolds).
-/

open Topology

noncomputable section

universe u v w u' v' w'

open Set Filter Function

open scoped Manifold Topology ContDiff

/-! ### Models with corners. -/


/-- A structure containing information on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a `C^n` manifold with model space `H`, and model vector space `E`.

We require two conditions `uniqueDiffOn'` and `target_subset_closure_interior`, which
are satisfied in the relevant cases (where `range I = univ` or a half space or a quadrant) and
useful for technical reasons. The former makes sure that manifold derivatives are uniquely
defined, the latter ensures that for `C^2` maps the second derivatives are symmetric even for points
on the boundary, as these are limit points of interior points where symmetry holds. If further
conditions turn out to be useful, they can be added here.
-/
@[ext]
structure ModelWithCorners (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] extends
    PartialEquiv H E where
  source_eq : source = univ
  uniqueDiffOn' : UniqueDiffOn 𝕜 toPartialEquiv.target
  target_subset_closure_interior : toPartialEquiv.target ⊆ closure (interior toPartialEquiv.target)
  continuous_toFun : Continuous toFun := by continuity
  continuous_invFun : Continuous invFun := by continuity

attribute [simp, mfld_simps] ModelWithCorners.source_eq

/-- A vector space is a model with corners, denoted as `𝓘(𝕜, E)` within the `Manifold` namespace. -/
def modelWithCornersSelf (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : ModelWithCorners 𝕜 E E where
  toPartialEquiv := PartialEquiv.refl E
  source_eq := rfl
  uniqueDiffOn' := uniqueDiffOn_univ
  target_subset_closure_interior := by simp
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[inherit_doc] scoped[Manifold] notation "𝓘(" 𝕜 ", " E ")" => modelWithCornersSelf 𝕜 E

/-- A normed field is a model with corners. -/
scoped[Manifold] notation "𝓘(" 𝕜 ")" => modelWithCornersSelf 𝕜 𝕜

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)

namespace ModelWithCorners

/-- Coercion of a model with corners to a function. We don't use `e.toFun` because it is actually
`e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`. While we may want to
switch to this behavior later, doing it mid-port will break a lot of proofs. -/
@[coe] def toFun' (e : ModelWithCorners 𝕜 E H) : H → E := e.toFun

instance : CoeFun (ModelWithCorners 𝕜 E H) fun _ => H → E := ⟨toFun'⟩

/-- The inverse to a model with corners, only registered as a `PartialEquiv`. -/
protected def symm : PartialEquiv E H :=
  I.toPartialEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : H → E :=
  I

/-- See Note [custom simps projection] -/
def Simps.symm_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : E → H :=
  I.symm

initialize_simps_projections ModelWithCorners (toFun → apply, invFun → symm_apply)

-- Register a few lemmas to make sure that `simp` puts expressions in normal form
@[simp, mfld_simps]
theorem toPartialEquiv_coe : (I.toPartialEquiv : H → E) = I :=
  rfl

@[simp, mfld_simps]
theorem mk_coe (e : PartialEquiv H E) (a b c d d') :
    ((ModelWithCorners.mk e a b c d d' : ModelWithCorners 𝕜 E H) : H → E) = (e : H → E) :=
  rfl

@[simp, mfld_simps]
theorem toPartialEquiv_coe_symm : (I.toPartialEquiv.symm : E → H) = I.symm :=
  rfl

@[simp, mfld_simps]
theorem mk_symm (e : PartialEquiv H E) (a b c d d') :
    (ModelWithCorners.mk e a b c d d' : ModelWithCorners 𝕜 E H).symm = e.symm :=
  rfl

@[continuity]
protected theorem continuous : Continuous I :=
  I.continuous_toFun

protected theorem continuousAt {x} : ContinuousAt I x :=
  I.continuous.continuousAt

protected theorem continuousWithinAt {s x} : ContinuousWithinAt I s x :=
  I.continuousAt.continuousWithinAt

@[continuity]
theorem continuous_symm : Continuous I.symm :=
  I.continuous_invFun

theorem continuousAt_symm {x} : ContinuousAt I.symm x :=
  I.continuous_symm.continuousAt

theorem continuousWithinAt_symm {s x} : ContinuousWithinAt I.symm s x :=
  I.continuous_symm.continuousWithinAt

theorem continuousOn_symm {s} : ContinuousOn I.symm s :=
  I.continuous_symm.continuousOn

@[simp, mfld_simps]
theorem target_eq : I.target = range (I : H → E) := by
  rw [← image_univ, ← I.source_eq]
  exact I.image_source_eq_target.symm

protected theorem uniqueDiffOn : UniqueDiffOn 𝕜 (range I) :=
  I.target_eq ▸ I.uniqueDiffOn'

@[deprecated (since := "2024-09-30")]
protected alias unique_diff := ModelWithCorners.uniqueDiffOn

theorem range_subset_closure_interior : range I ⊆ closure (interior (range I)) := by
  rw [← I.target_eq]
  exact I.target_subset_closure_interior

@[simp, mfld_simps]
protected theorem left_inv (x : H) : I.symm (I x) = x := by refine I.left_inv' ?_; simp

protected theorem leftInverse : LeftInverse I.symm I :=
  I.left_inv

theorem injective : Injective I :=
  I.leftInverse.injective

@[simp, mfld_simps]
theorem symm_comp_self : I.symm ∘ I = id :=
  I.leftInverse.comp_eq_id

protected theorem rightInvOn : RightInvOn I.symm I (range I) :=
  I.leftInverse.rightInvOn_range

@[simp, mfld_simps]
protected theorem right_inv {x : E} (hx : x ∈ range I) : I (I.symm x) = x :=
  I.rightInvOn hx

theorem preimage_image (s : Set H) : I ⁻¹' (I '' s) = s :=
  I.injective.preimage_image s

protected theorem image_eq (s : Set H) : I '' s = I.symm ⁻¹' s ∩ range I := by
  refine (I.toPartialEquiv.image_eq_target_inter_inv_preimage ?_).trans ?_
  · rw [I.source_eq]; exact subset_univ _
  · rw [inter_comm, I.target_eq, I.toPartialEquiv_coe_symm]

theorem isClosedEmbedding : IsClosedEmbedding I :=
  I.leftInverse.isClosedEmbedding I.continuous_symm I.continuous

@[deprecated (since := "2024-10-20")]
alias closedEmbedding := isClosedEmbedding

theorem isClosed_range : IsClosed (range I) :=
  I.isClosedEmbedding.isClosed_range


theorem range_eq_closure_interior : range I = closure (interior (range I)) :=
  Subset.antisymm I.range_subset_closure_interior I.isClosed_range.closure_interior_subset

theorem map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[range I] I x :=
  I.isClosedEmbedding.isEmbedding.map_nhds_eq x

theorem map_nhdsWithin_eq (s : Set H) (x : H) : map I (𝓝[s] x) = 𝓝[I '' s] I x :=
  I.isClosedEmbedding.isEmbedding.map_nhdsWithin_eq s x

theorem image_mem_nhdsWithin {x : H} {s : Set H} (hs : s ∈ 𝓝 x) : I '' s ∈ 𝓝[range I] I x :=
  I.map_nhds_eq x ▸ image_mem_map hs

theorem symm_map_nhdsWithin_image {x : H} {s : Set H} : map I.symm (𝓝[I '' s] I x) = 𝓝[s] x := by
  rw [← I.map_nhdsWithin_eq, map_map, I.symm_comp_self, map_id]

theorem symm_map_nhdsWithin_range (x : H) : map I.symm (𝓝[range I] I x) = 𝓝 x := by
  rw [← I.map_nhds_eq, map_map, I.symm_comp_self, map_id]

theorem uniqueDiffOn_preimage {s : Set H} (hs : IsOpen s) :
    UniqueDiffOn 𝕜 (I.symm ⁻¹' s ∩ range I) := by
  rw [inter_comm]
  exact I.uniqueDiffOn.inter (hs.preimage I.continuous_invFun)

@[deprecated (since := "2024-09-30")]
alias unique_diff_preimage := uniqueDiffOn_preimage

theorem uniqueDiffOn_preimage_source {β : Type*} [TopologicalSpace β] {e : PartialHomeomorph H β} :
    UniqueDiffOn 𝕜 (I.symm ⁻¹' e.source ∩ range I) :=
  I.uniqueDiffOn_preimage e.open_source

@[deprecated (since := "2024-09-30")]
alias unique_diff_preimage_source := uniqueDiffOn_preimage_source

theorem uniqueDiffWithinAt_image {x : H} : UniqueDiffWithinAt 𝕜 (range I) (I x) :=
  I.uniqueDiffOn _ (mem_range_self _)

@[deprecated (since := "2024-09-30")]
alias unique_diff_at_image := uniqueDiffWithinAt_image

theorem symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {f : H → X} {s : Set H}
    {x : H} :
    ContinuousWithinAt (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) ↔ ContinuousWithinAt f s x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.comp I.continuousWithinAt (mapsTo_preimage _ _)
    simp_rw [preimage_inter, preimage_preimage, I.left_inv, preimage_id', preimage_range,
      inter_univ] at this
    rwa [Function.comp_assoc, I.symm_comp_self] at this
  · rw [← I.left_inv x] at h; exact h.comp I.continuousWithinAt_symm inter_subset_left

protected theorem locallyCompactSpace [LocallyCompactSpace E] (I : ModelWithCorners 𝕜 E H) :
    LocallyCompactSpace H := by
  have : ∀ x : H, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (I x) ∧ IsCompact s)
      fun s => I.symm '' (s ∩ range I) := fun x ↦ by
    rw [← I.symm_map_nhdsWithin_range]
    exact ((compact_basis_nhds (I x)).inf_principal _).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨-, hsc⟩
  exact (hsc.inter_right I.isClosed_range).image I.continuous_symm

open TopologicalSpace

protected theorem secondCountableTopology [SecondCountableTopology E] (I : ModelWithCorners 𝕜 E H) :
    SecondCountableTopology H :=
  I.isClosedEmbedding.isEmbedding.secondCountableTopology

include I in
/-- Every manifold is a Fréchet space (T1 space) -- regardless of whether it is
Hausdorff. -/
protected theorem t1Space (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : T1Space M := by
  have : T2Space H := I.isClosedEmbedding.toIsEmbedding.t2Space
  exact ChartedSpace.t1Space H M

end ModelWithCorners

section

variable (𝕜 E)

/-- In the trivial model with corners, the associated `PartialEquiv` is the identity. -/
@[simp, mfld_simps]
theorem modelWithCornersSelf_partialEquiv : 𝓘(𝕜, E).toPartialEquiv = PartialEquiv.refl E :=
  rfl

@[simp, mfld_simps]
theorem modelWithCornersSelf_coe : (𝓘(𝕜, E) : E → E) = id :=
  rfl

@[simp, mfld_simps]
theorem modelWithCornersSelf_coe_symm : (𝓘(𝕜, E).symm : E → E) = id :=
  rfl

end

end

section ModelWithCornersProd

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', ModelProd H H')`. This appears in particular for the manifold
structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on
`(E × E, H × E)`. See note [Manifold type tags] for explanation about `ModelProd H H'`
vs `H × H'`. -/
@[simps (config := .lemmasOnly)]
def ModelWithCorners.prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (ModelProd H H') :=
  { I.toPartialEquiv.prod I'.toPartialEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 ∈ I.source ∧ x.2 ∈ I'.source }
    source_eq := by simp only [setOf_true, mfld_simps]
    uniqueDiffOn' := I.uniqueDiffOn'.prod I'.uniqueDiffOn'
    target_subset_closure_interior := by
      simp only [PartialEquiv.prod_target, target_eq, interior_prod_eq, closure_prod_eq]
      exact Set.prod_mono I.range_subset_closure_interior I'.range_subset_closure_interior
    continuous_toFun := I.continuous_toFun.prodMap I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prodMap I'.continuous_invFun }

/-- Given a finite family of `ModelWithCorners` `I i` on `(E i, H i)`, we define the model with
corners `pi I` on `(Π i, E i, ModelPi H)`. See note [Manifold type tags] for explanation about
`ModelPi H`. -/
def ModelWithCorners.pi {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
    {E : ι → Type w} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {H : ι → Type u'}
    [∀ i, TopologicalSpace (H i)] (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    ModelWithCorners 𝕜 (∀ i, E i) (ModelPi H) where
  toPartialEquiv := PartialEquiv.pi fun i => (I i).toPartialEquiv
  source_eq := by simp only [pi_univ, mfld_simps]
  uniqueDiffOn' := UniqueDiffOn.pi ι E _ _ fun i _ => (I i).uniqueDiffOn'
  target_subset_closure_interior := by
    simp only [PartialEquiv.pi_target, target_eq, finite_univ, interior_pi_set, closure_pi_set]
    exact Set.pi_mono (fun i _ ↦ (I i).range_subset_closure_interior)
  continuous_toFun := continuous_pi fun i => (I i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
abbrev ModelWithCorners.tangent {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : ModelWithCorners 𝕜 (E × E) (ModelProd H E) :=
  I.prod 𝓘(𝕜, E)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] {G : Type*}
  [TopologicalSpace G] {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 F G}

@[simp, mfld_simps]
theorem modelWithCorners_prod_toPartialEquiv :
    (I.prod J).toPartialEquiv = I.toPartialEquiv.prod J.toPartialEquiv :=
  rfl

@[simp, mfld_simps]
theorem modelWithCorners_prod_coe (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    (I.prod I' : _ × _ → _ × _) = Prod.map I I' :=
  rfl

@[simp, mfld_simps]
theorem modelWithCorners_prod_coe_symm (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') :
    ((I.prod I').symm : _ × _ → _ × _) = Prod.map I.symm I'.symm :=
  rfl

/-- This lemma should be erased, or at least burn in hell, as it uses bad defeq: the left model
with corners is for `E times F`, the right one for `ModelProd E F`, and there's a good reason
we are distinguishing them. -/
theorem modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜, E).prod 𝓘(𝕜, F) := by ext1 <;> simp

theorem ModelWithCorners.range_prod : range (I.prod J) = range I ×ˢ range J := by
  simp_rw [← ModelWithCorners.target_eq]; rfl

end ModelWithCornersProd

section Boundaryless

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. This
differs from the more general `BoundarylessManifold`, which requires every point on the manifold
to be an interior point. -/
class ModelWithCorners.Boundaryless {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : Prop where
  range_eq_univ : range I = univ

theorem ModelWithCorners.range_eq_univ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] :
    range I = univ := ModelWithCorners.Boundaryless.range_eq_univ

/-- If `I` is a `ModelWithCorners.Boundaryless` model, then it is a homeomorphism. -/
@[simps (config := {simpRhs := true})]
def ModelWithCorners.toHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] : H ≃ₜ E where
  __ := I
  left_inv := I.left_inv
  right_inv _ := I.right_inv <| I.range_eq_univ.symm ▸ mem_univ _

/-- The trivial model with corners has no boundary -/
instance modelWithCornersSelf_boundaryless (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : (modelWithCornersSelf 𝕜 E).Boundaryless :=
  ⟨by simp⟩

/-- If two model with corners are boundaryless, their product also is -/
instance ModelWithCorners.range_eq_univ_prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] {E' : Type v'} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
    [I'.Boundaryless] : (I.prod I').Boundaryless := by
  constructor
  dsimp [ModelWithCorners.prod, ModelProd]
  rw [← prod_range_range_eq, ModelWithCorners.Boundaryless.range_eq_univ,
    ModelWithCorners.Boundaryless.range_eq_univ, univ_prod_univ]

end Boundaryless

section contDiffGroupoid

/-! ### `C^n` functions on models with corners -/


variable {m n : WithTop ℕ∞} {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]

variable (n I) in
/-- Given a model with corners `(E, H)`, we define the pregroupoid of `C^n` transformations of `H`
as the maps that are `C^n` when read in `E` through `I`. -/
def contDiffPregroupoid : Pregroupoid H where
  property f s := ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
  comp {f g u v} hf hg _ _ _ := by
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [this]
    refine hg.comp (hf.mono fun x ⟨hx1, hx2⟩ ↦ ⟨hx1.1, hx2⟩) ?_
    rintro x ⟨hx1, _⟩
    simp only [mfld_simps] at hx1 ⊢
    exact hx1.2
  id_mem := by
    apply ContDiffOn.congr contDiff_id.contDiffOn
    rintro x ⟨_, hx2⟩
    rcases mem_range.1 hx2 with ⟨y, hy⟩
    rw [← hy]
    simp only [mfld_simps]
  locality {f u} _ H := by
    apply contDiffOn_of_locally_contDiffOn
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩
    have : I.symm ⁻¹' (u ∩ v) ∩ range I = I.symm ⁻¹' u ∩ range I ∩ I.symm ⁻¹' v := by
      rw [preimage_inter, inter_assoc, inter_assoc]
      congr 1
      rw [inter_comm]
    rw [this] at hv
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  congr {f g u} _ fg hf := by
    apply hf.congr
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rw [fg _ hy1]

variable (n I) in
/-- Given a model with corners `(E, H)`, we define the groupoid of invertible `C^n` transformations
of `H` as the invertible maps that are `C^n` when read in `E` through `I`. -/
def contDiffGroupoid : StructureGroupoid H :=
  Pregroupoid.groupoid (contDiffPregroupoid n I)

/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
theorem contDiffGroupoid_le (h : m ≤ n) : contDiffGroupoid n I ≤ contDiffGroupoid m I := by
  rw [contDiffGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact ContDiffOn.of_le hfs h

/-- The groupoid of `0`-times continuously differentiable maps is just the groupoid of all
partial homeomorphisms -/
theorem contDiffGroupoid_zero_eq : contDiffGroupoid 0 I = continuousGroupoid H := by
  apply le_antisymm le_top
  intro u _
  -- we have to check that every partial homeomorphism belongs to `contDiffGroupoid 0 I`,
  -- by unfolding its definition
  change u ∈ contDiffGroupoid 0 I
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simp only [contDiffOn_zero]
  constructor
  · refine I.continuous.comp_continuousOn (u.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left
  · refine I.continuous.comp_continuousOn (u.symm.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left

-- FIXME: does this generalise to other groupoids? The argument is not specific
-- to C^n functions, but uses something about the groupoid's property that is not easy to abstract.
/-- Any change of coordinates with empty source belongs to `contDiffGroupoid`. -/
lemma ContDiffGroupoid.mem_of_source_eq_empty (f : PartialHomeomorph H H)
    (hf : f.source = ∅) : f ∈ contDiffGroupoid n I := by
  constructor
  · intro x ⟨hx, _⟩
    rw [mem_preimage] at hx
    simp_all only [mem_empty_iff_false]
  · intro x ⟨hx, _⟩
    have : f.target = ∅ := by simp [← f.image_source_eq_target, hf]
    simp_all [hx]

include I in
/-- Any change of coordinates with empty source belongs to `continuousGroupoid`. -/
lemma ContinuousGroupoid.mem_of_source_eq_empty (f : PartialHomeomorph H H)
    (hf : f.source = ∅) : f ∈ continuousGroupoid H := by
  rw [← contDiffGroupoid_zero_eq (I := I)]
  exact ContDiffGroupoid.mem_of_source_eq_empty f hf

/-- An identity partial homeomorphism belongs to the `C^n` groupoid. -/
theorem ofSet_mem_contDiffGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ contDiffGroupoid n I := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : ContDiffOn 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I) by
    simp [h, contDiffPregroupoid]
  have : ContDiffOn 𝕜 n id (univ : Set E) := contDiff_id.contDiffOn
  exact this.congr_mono (fun x hx => I.right_inv hx.2) (subset_univ _)

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
theorem symm_trans_mem_contDiffGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ contDiffGroupoid n I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_contDiffGroupoid e.open_target) this

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']

/-- The product of two `C^n` partial homeomorphisms is `C^n`. -/
theorem contDiffGroupoid_prod {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {e : PartialHomeomorph H H} {e' : PartialHomeomorph H' H'} (he : e ∈ contDiffGroupoid n I)
    (he' : e' ∈ contDiffGroupoid n I') : e.prod e' ∈ contDiffGroupoid n (I.prod I') := by
  obtain ⟨he, he_symm⟩ := he
  obtain ⟨he', he'_symm⟩ := he'
  constructor <;> simp only [PartialEquiv.prod_source, PartialHomeomorph.prod_toPartialEquiv,
    contDiffPregroupoid]
  · have h3 := ContDiffOn.prod_map he he'
    rw [← I.image_eq, ← I'.image_eq, prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
  · have h3 := ContDiffOn.prod_map he_symm he'_symm
    rw [← I.image_eq, ← I'.image_eq, prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3

/-- The `C^n` groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (contDiffGroupoid n I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      apply (contDiffGroupoid n I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_contDiffGroupoid hs)

end contDiffGroupoid

section IsManifold

/-! ### `C^n` manifolds (possibly with boundary or corners) -/

/-- Typeclass defining manifolds with respect to a model with corners, over a
field `𝕜`. This definition includes the model with corners `I` (which might allow boundary, corners,
or not, so this class covers both manifolds with boundary and manifolds without boundary), and
a smoothness parameter `n : WithTop ℕ∞` (where `n = 0` means topological manifold, `n = ∞` means
smooth manifold and `n = ω` means analytic manifold). -/
class IsManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] extends
    HasGroupoid M (contDiffGroupoid n I) : Prop

@[deprecated (since := "2025-01-09")] alias SmoothManifoldWithCorners := IsManifold

/-- Building a `C^n` manifold from a `HasGroupoid` assumption. -/
theorem IsManifold.mk' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [gr : HasGroupoid M (contDiffGroupoid n I)] : IsManifold I n M :=
  { gr with }

@[deprecated (since := "2025-01-09")] alias SmoothManifoldWithCorners.mk' := IsManifold.mk'

theorem isManifold_of_contDiffOn {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    (h : ∀ e e' : PartialHomeomorph M H, e ∈ atlas H M → e' ∈ atlas H M →
      ContDiffOn 𝕜 n (I ∘ e.symm ≫ₕ e' ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I)) :
    IsManifold I n M where
  compatible := by
    haveI : HasGroupoid M (contDiffGroupoid n I) := hasGroupoid_of_pregroupoid _ (h _ _)
    apply StructureGroupoid.compatible

@[deprecated (since := "2025-01-09")]
alias smoothManifoldWithCorners_of_contDiffOn := isManifold_of_contDiffOn

/-- For any model with corners, the model space is a `C^n` manifold -/
instance intIsManifoldModelSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞} : IsManifold I n H :=
  { hasGroupoid_model_space _ _ with }

end IsManifold

namespace IsManifold

/- We restate in the namespace `IsManifold` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`contDiffGroupoid n I` explicitly. -/
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

protected theorem of_le {m n : WithTop ℕ∞} (hmn : m ≤ n)
    [IsManifold I n M] : IsManifold I m M := by
  have : HasGroupoid M (contDiffGroupoid m I) :=
    hasGroupoid_of_le (G₁ := contDiffGroupoid n I) (by infer_instance)
      (contDiffGroupoid_le hmn)
  exact mk' I m M

/-- A typeclass registering that a smoothness exponent is smaller than `∞`. Used to deduce that
some manifolds are `C^n` when they are `C^∞`. -/
class _root_.ENat.LEInfty (m : WithTop ℕ∞) where
  out : m ≤ ∞

open ENat

instance (n : ℕ) : LEInfty (n : WithTop ℕ∞) := ⟨mod_cast le_top⟩
instance (n : ℕ) [n.AtLeastTwo] : LEInfty (no_index (OfNat.ofNat n) : WithTop ℕ∞) :=
  inferInstanceAs (LEInfty (n : WithTop ℕ∞))
instance : LEInfty (1 : WithTop ℕ∞) := inferInstanceAs (LEInfty ((1 : ℕ) : WithTop ℕ∞))
instance : LEInfty (0 : WithTop ℕ∞) := inferInstanceAs (LEInfty ((0 : ℕ) : WithTop ℕ∞))

instance {a : WithTop ℕ∞} [IsManifold I ∞ M] [h : LEInfty a] :
    IsManifold I a M :=
  IsManifold.of_le h.out

instance {a : WithTop ℕ∞} [IsManifold I ω M] :
    IsManifold I a M :=
  IsManifold.of_le le_top

instance : IsManifold I 0 M := by
  suffices HasGroupoid M (contDiffGroupoid 0 I) from mk' I 0 M
  constructor
  intro e e' he he'
  rw [contDiffGroupoid_zero_eq]
  trivial

instance [IsManifold I 2 M] :
    IsManifold I 1 M :=
  IsManifold.of_le one_le_two

variable (I n M) in
/-- The maximal atlas of `M` for the `C^n` manifold with corners structure corresponding to the
model with corners `I`. -/
def maximalAtlas :=
  (contDiffGroupoid n I).maximalAtlas M

theorem subset_maximalAtlas [IsManifold I n M] : atlas H M ⊆ maximalAtlas I n M :=
  StructureGroupoid.subset_maximalAtlas _

theorem chart_mem_maximalAtlas [IsManifold I n M] (x : M) :
    chartAt H x ∈ maximalAtlas I n M :=
  StructureGroupoid.chart_mem_maximalAtlas _ x

theorem compatible_of_mem_maximalAtlas {e e' : PartialHomeomorph M H} (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I n M) : e.symm.trans e' ∈ contDiffGroupoid n I :=
  StructureGroupoid.compatible_of_mem_maximalAtlas he he'

lemma maximalAtlas_subset_of_le {m n : WithTop ℕ∞} (h : m ≤ n) :
    maximalAtlas I n M ⊆ maximalAtlas I m M :=
  StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le h)

variable (n) in
/-- The empty set is a `C^n` manifold w.r.t. any charted space and model. -/
instance empty [IsEmpty M] : IsManifold I n M := by
  apply isManifold_of_contDiffOn
  intro e e' _ _ x hx
  set t := I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I
  -- Since `M` is empty, the condition about compatibility of transition maps is vacuous.
  have : (e.symm ≫ₕ e').source = ∅ := calc (e.symm ≫ₕ e').source
    _ = (e.symm.source) ∩ e.symm ⁻¹' e'.source := by rw [← PartialHomeomorph.trans_source]
    _ = (e.symm.source) ∩ e.symm ⁻¹' ∅ := by rw [eq_empty_of_isEmpty (e'.source)]
    _ = (e.symm.source) ∩ ∅ := by rw [preimage_empty]
    _ = ∅ := inter_empty e.symm.source
  have : t = ∅ := calc t
    _ = I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I := by
      rw [← Subtype.preimage_val_eq_preimage_val_iff]
    _ = ∅ ∩ range I := by rw [this, preimage_empty]
    _ = ∅ := empty_inter (range I)
  apply (this ▸ hx).elim

attribute [local instance] ChartedSpace.of_discreteTopology in
variable (n) in
def of_discreteTopology [DiscreteTopology M] [Unique E] :
    IsManifold (modelWithCornersSelf 𝕜 E) n M := by
  apply isManifold_of_contDiffOn _ _ _ (fun _ _ _ _ ↦ contDiff_of_subsingleton.contDiffOn)

attribute [local instance] ChartedSpace.of_discreteTopology in
example [Unique E] : IsManifold (𝓘(𝕜, E)) n (Fin 2) := of_discreteTopology _

/-- The product of two `C^n` manifolds is naturally a `C^n` manifold. -/
instance prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I n M] (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' n M'] :
    IsManifold (I.prod I') n (M × M') where
  compatible := by
    rintro f g ⟨f1, hf1, f2, hf2, rfl⟩ ⟨g1, hg1, g2, hg2, rfl⟩
    rw [PartialHomeomorph.prod_symm, PartialHomeomorph.prod_trans]
    have h1 := (contDiffGroupoid n I).compatible hf1 hg1
    have h2 := (contDiffGroupoid n I').compatible hf2 hg2
    exact contDiffGroupoid_prod h1 h2

section DisjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  [hM : IsManifold I n M] [hM' : IsManifold I n M']

/-- The disjoint union of two `C^n` manifolds modelled on `(E, H)`
is a `C^n` manifold modeled on `(E, H)`. -/
instance disjointUnion : IsManifold I n (M ⊕ M') where
  compatible {e} e' he he' := by
    obtain (h | h) := isEmpty_or_nonempty H
    · exact ContDiffGroupoid.mem_of_source_eq_empty _ (eq_empty_of_isEmpty _)
    obtain (⟨f, hf, hef⟩ | ⟨f, hf, hef⟩) := ChartedSpace.mem_atlas_sum he
    · obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inl]
        exact hM.compatible hf hf'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ ↦ by simp_all [hx₂], fun hx ↦ hx.elim⟩
    · -- Analogous argument to the first case: is there a way to deduplicate?
      obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ ↦ by simp_all [hx₂], fun hx ↦ hx.elim⟩
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inr]
        exact hM'.compatible hf hf'

end DisjointUnion

end IsManifold

theorem PartialHomeomorph.isManifold_singleton
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] (e : PartialHomeomorph M H) (h : e.source = Set.univ) :
    @IsManifold 𝕜 _ E _ _ H _ I n M _ (e.singletonChartedSpace h) :=
  @IsManifold.mk' _ _ _ _ _ _ _ _ _ _ _ (id _) <|
    e.singleton_hasGroupoid h (contDiffGroupoid n I)

@[deprecated (since := "2025-01-09")]
alias PartialHomeomorph.singleton_smoothManifoldWithCorners :=
  PartialHomeomorph.isManifold_singleton

theorem Topology.IsOpenEmbedding.isManifold_singleton {𝕜 E H : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [Nonempty M] {f : M → H} (h : IsOpenEmbedding f) :
    @IsManifold 𝕜 _ E _ _ H _ I n M _ h.singletonChartedSpace :=
  (h.toPartialHomeomorph f).isManifold_singleton (by simp)

@[deprecated (since := "2025-01-09")]
alias Topology.IsOpenEmbedding.singleton_smoothManifoldWithCorners :=
  Topology.IsOpenEmbedding.isManifold_singleton

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.singleton_smoothManifoldWithCorners :=
  Topology.IsOpenEmbedding.isManifold_singleton

namespace TopologicalSpace.Opens

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  (s : Opens M)

instance : IsManifold I n s :=
  { s.instHasGroupoid (contDiffGroupoid n I) with }

end TopologicalSpace.Opens

section TangentSpace

/- We define the tangent space to `M` modelled on `I : ModelWithCorners 𝕜 E H` as a type synonym
for `E`. This is enough to define linear maps between tangent spaces, for instance derivatives,
but the interesting part is to define a manifold structure on the whole tangent bundle, which
requires that `M` is a `C^n` manifold. The definition is put here to avoid importing
all the smooth bundle structure when defining manifold derivatives. -/

set_option linter.unusedVariables false in
/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangentBundleCore I M).to_topological_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unusedArguments]
def TangentSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (_x : M) : Type u := E
-- Porting note: was deriving TopologicalSpace, AddCommGroup, IsTopologicalAddGroup

/- In general, the definition of `TangentSpace` is not reducible, so that type class inference
does not pick wrong instances. We record the right instances for them. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

instance : TopologicalSpace (TangentSpace I x) := inferInstanceAs (TopologicalSpace E)
instance : AddCommGroup (TangentSpace I x) := inferInstanceAs (AddCommGroup E)
instance : IsTopologicalAddGroup (TangentSpace I x) := inferInstanceAs (IsTopologicalAddGroup E)
instance : Module 𝕜 (TangentSpace I x) := inferInstanceAs (Module 𝕜 E)
instance : Inhabited (TangentSpace I x) := ⟨0⟩

variable (M) in
-- is empty if the base manifold is empty
/-- The tangent bundle to a manifold, as a Sigma type. Defined in terms of
`Bundle.TotalSpace` to be able to put a suitable topology on it. -/
abbrev TangentBundle := Bundle.TotalSpace E (TangentSpace I : M → Type _)

end TangentSpace

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

instance : PathConnectedSpace (TangentSpace I x) := inferInstanceAs (PathConnectedSpace E)

end Real
