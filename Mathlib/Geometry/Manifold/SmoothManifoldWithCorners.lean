/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic

#align_import geometry.manifold.smooth_manifold_with_corners from "leanprover-community/mathlib"@"ddec54a71a0dd025c05445d467f1a2b7d586a3ba"

/-!
# Smooth manifolds (possibly with boundary or corners)

A smooth manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are smooth maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are smooth when read in `E` (for any regularity `n : ℕ∞`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`. We also introduce a
specific type class for `C^∞` manifolds as these are the most commonly used.

Some texts assume manifolds to be Hausdorff and secound countable. We (in mathlib) assume neither,
but add these assumptions later as needed. (Quite a few results still do not require them.)

## Main definitions

* `ModelWithCorners 𝕜 E H` :
  a structure containing informations on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a smooth manifold with model space `H`, and model vector space `E`.
* `modelWithCornersSelf 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `contDiffGroupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of partial homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `SmoothManifoldWithCorners I M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^∞` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `HasGroupoid M (contDiffGroupoid ∞ I)`.
* `extChartAt I x`:
  in a smooth manifold with corners with the model `I` on `(E, H)`, the charts take values in `H`,
  but often we may want to use their `E`-valued version, obtained by composing the charts with `I`.
  Since the target is in general not open, we can not register them as partial homeomorphisms, but
  we register them as `PartialEquiv`s.
  `extChartAt I x` is the canonical such partial equiv around `x`.

As specific examples of models with corners, we define (in `Geometry.Manifold.Instances.Real`)
* `modelWithCornersSelf ℝ (EuclideanSpace (Fin n))` for the model space used to define
  `n`-dimensional real manifolds without boundary (with notation `𝓡 n` in the locale `Manifold`)
* `ModelWithCorners ℝ (EuclideanSpace (Fin n)) (EuclideanHalfSpace n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `Manifold`)
* `ModelWithCorners ℝ (EuclideanSpace (Fin n)) (EuclideanQuadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional real manifold without boundary,
one could use

  `variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace (Fin n)) M]
   [SmoothManifoldWithCorners (𝓡 n) M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(EuclideanSpace (Fin n)) × (EuclideanSpace (Fin n))` and not on `EuclideanSpace (Fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(EuclideanSpace (Fin n)) × (EuclideanSpace (Fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E E} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [SmoothManifoldWithCorners I M]`

Here, `I.Boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `modelWithCornersSelf`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `modelWithCornersSelf ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(fun p : E × F ↦ (p.1, p.2))` is not defeq to the identity).
So, it is important to use the above incantation to maximize the applicability of theorems.

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

We concentrate on `C^∞` manifolds: all the definitions work equally well for `C^n` manifolds, but
later on it is a pain to carry all over the smoothness parameter, especially when one wants to deal
with `C^k` functions as there would be additional conditions `k ≤ n` everywhere. Since one deals
almost all the time with `C^∞` (or analytic) manifolds, this seems to be a reasonable choice that
one could revisit later if needed. `C^k` manifolds are still available, but they should be called
using `HasGroupoid M (contDiffGroupoid k I)` where `I` is the model with corners.

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

noncomputable section

universe u v w u' v' w'

open Set Filter Function

open scoped Manifold Filter Topology

/-- The extended natural number `∞` -/
scoped[Manifold] notation "∞" => (⊤ : ℕ∞)

/-! ### Models with corners. -/


/-- A structure containing informations on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a smooth manifold with model space `H`, and model vector space `E`.
-/
@[ext] -- Porting note(#5171): was nolint has_nonempty_instance
structure ModelWithCorners (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] extends
    PartialEquiv H E where
  source_eq : source = univ
  unique_diff' : UniqueDiffOn 𝕜 toPartialEquiv.target
  continuous_toFun : Continuous toFun := by continuity
  continuous_invFun : Continuous invFun := by continuity
#align model_with_corners ModelWithCorners

attribute [simp, mfld_simps] ModelWithCorners.source_eq

/-- A vector space is a model with corners. -/
def modelWithCornersSelf (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : ModelWithCorners 𝕜 E E where
  toPartialEquiv := PartialEquiv.refl E
  source_eq := rfl
  unique_diff' := uniqueDiffOn_univ
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
#align model_with_corners_self modelWithCornersSelf

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
#align model_with_corners.symm ModelWithCorners.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : H → E :=
  I
#align model_with_corners.simps.apply ModelWithCorners.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symm_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : E → H :=
  I.symm
#align model_with_corners.simps.symm_apply ModelWithCorners.Simps.symm_apply

initialize_simps_projections ModelWithCorners (toFun → apply, invFun → symm_apply)

-- Register a few lemmas to make sure that `simp` puts expressions in normal form
@[simp, mfld_simps]
theorem toPartialEquiv_coe : (I.toPartialEquiv : H → E) = I :=
  rfl
#align model_with_corners.to_local_equiv_coe ModelWithCorners.toPartialEquiv_coe

@[simp, mfld_simps]
theorem mk_coe (e : PartialEquiv H E) (a b c d) :
    ((ModelWithCorners.mk e a b c d : ModelWithCorners 𝕜 E H) : H → E) = (e : H → E) :=
  rfl
#align model_with_corners.mk_coe ModelWithCorners.mk_coe

@[simp, mfld_simps]
theorem toPartialEquiv_coe_symm : (I.toPartialEquiv.symm : E → H) = I.symm :=
  rfl
#align model_with_corners.to_local_equiv_coe_symm ModelWithCorners.toPartialEquiv_coe_symm

@[simp, mfld_simps]
theorem mk_symm (e : PartialEquiv H E) (a b c d) :
    (ModelWithCorners.mk e a b c d : ModelWithCorners 𝕜 E H).symm = e.symm :=
  rfl
#align model_with_corners.mk_symm ModelWithCorners.mk_symm

@[continuity]
protected theorem continuous : Continuous I :=
  I.continuous_toFun
#align model_with_corners.continuous ModelWithCorners.continuous

protected theorem continuousAt {x} : ContinuousAt I x :=
  I.continuous.continuousAt
#align model_with_corners.continuous_at ModelWithCorners.continuousAt

protected theorem continuousWithinAt {s x} : ContinuousWithinAt I s x :=
  I.continuousAt.continuousWithinAt
#align model_with_corners.continuous_within_at ModelWithCorners.continuousWithinAt

@[continuity]
theorem continuous_symm : Continuous I.symm :=
  I.continuous_invFun
#align model_with_corners.continuous_symm ModelWithCorners.continuous_symm

theorem continuousAt_symm {x} : ContinuousAt I.symm x :=
  I.continuous_symm.continuousAt
#align model_with_corners.continuous_at_symm ModelWithCorners.continuousAt_symm

theorem continuousWithinAt_symm {s x} : ContinuousWithinAt I.symm s x :=
  I.continuous_symm.continuousWithinAt
#align model_with_corners.continuous_within_at_symm ModelWithCorners.continuousWithinAt_symm

theorem continuousOn_symm {s} : ContinuousOn I.symm s :=
  I.continuous_symm.continuousOn
#align model_with_corners.continuous_on_symm ModelWithCorners.continuousOn_symm

@[simp, mfld_simps]
theorem target_eq : I.target = range (I : H → E) := by
  rw [← image_univ, ← I.source_eq]
  exact I.image_source_eq_target.symm
#align model_with_corners.target_eq ModelWithCorners.target_eq

protected theorem unique_diff : UniqueDiffOn 𝕜 (range I) :=
  I.target_eq ▸ I.unique_diff'
#align model_with_corners.unique_diff ModelWithCorners.unique_diff

@[simp, mfld_simps]
protected theorem left_inv (x : H) : I.symm (I x) = x := by refine I.left_inv' ?_; simp
#align model_with_corners.left_inv ModelWithCorners.left_inv

protected theorem leftInverse : LeftInverse I.symm I :=
  I.left_inv
#align model_with_corners.left_inverse ModelWithCorners.leftInverse

theorem injective : Injective I :=
  I.leftInverse.injective
#align model_with_corners.injective ModelWithCorners.injective

@[simp, mfld_simps]
theorem symm_comp_self : I.symm ∘ I = id :=
  I.leftInverse.comp_eq_id
#align model_with_corners.symm_comp_self ModelWithCorners.symm_comp_self

protected theorem rightInvOn : RightInvOn I.symm I (range I) :=
  I.leftInverse.rightInvOn_range
#align model_with_corners.right_inv_on ModelWithCorners.rightInvOn

@[simp, mfld_simps]
protected theorem right_inv {x : E} (hx : x ∈ range I) : I (I.symm x) = x :=
  I.rightInvOn hx
#align model_with_corners.right_inv ModelWithCorners.right_inv

theorem preimage_image (s : Set H) : I ⁻¹' (I '' s) = s :=
  I.injective.preimage_image s
#align model_with_corners.preimage_image ModelWithCorners.preimage_image

protected theorem image_eq (s : Set H) : I '' s = I.symm ⁻¹' s ∩ range I := by
  refine (I.toPartialEquiv.image_eq_target_inter_inv_preimage ?_).trans ?_
  · rw [I.source_eq]; exact subset_univ _
  · rw [inter_comm, I.target_eq, I.toPartialEquiv_coe_symm]
#align model_with_corners.image_eq ModelWithCorners.image_eq

protected theorem closedEmbedding : ClosedEmbedding I :=
  I.leftInverse.closedEmbedding I.continuous_symm I.continuous
#align model_with_corners.closed_embedding ModelWithCorners.closedEmbedding

theorem isClosed_range : IsClosed (range I) :=
  I.closedEmbedding.isClosed_range
#align model_with_corners.closed_range ModelWithCorners.isClosed_range

@[deprecated] alias closed_range := isClosed_range -- 2024-03-17

theorem map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[range I] I x :=
  I.closedEmbedding.toEmbedding.map_nhds_eq x
#align model_with_corners.map_nhds_eq ModelWithCorners.map_nhds_eq

theorem map_nhdsWithin_eq (s : Set H) (x : H) : map I (𝓝[s] x) = 𝓝[I '' s] I x :=
  I.closedEmbedding.toEmbedding.map_nhdsWithin_eq s x
#align model_with_corners.map_nhds_within_eq ModelWithCorners.map_nhdsWithin_eq

theorem image_mem_nhdsWithin {x : H} {s : Set H} (hs : s ∈ 𝓝 x) : I '' s ∈ 𝓝[range I] I x :=
  I.map_nhds_eq x ▸ image_mem_map hs
#align model_with_corners.image_mem_nhds_within ModelWithCorners.image_mem_nhdsWithin

theorem symm_map_nhdsWithin_image {x : H} {s : Set H} : map I.symm (𝓝[I '' s] I x) = 𝓝[s] x := by
  rw [← I.map_nhdsWithin_eq, map_map, I.symm_comp_self, map_id]
#align model_with_corners.symm_map_nhds_within_image ModelWithCorners.symm_map_nhdsWithin_image

theorem symm_map_nhdsWithin_range (x : H) : map I.symm (𝓝[range I] I x) = 𝓝 x := by
  rw [← I.map_nhds_eq, map_map, I.symm_comp_self, map_id]
#align model_with_corners.symm_map_nhds_within_range ModelWithCorners.symm_map_nhdsWithin_range

theorem unique_diff_preimage {s : Set H} (hs : IsOpen s) :
    UniqueDiffOn 𝕜 (I.symm ⁻¹' s ∩ range I) := by
  rw [inter_comm]
  exact I.unique_diff.inter (hs.preimage I.continuous_invFun)
#align model_with_corners.unique_diff_preimage ModelWithCorners.unique_diff_preimage

theorem unique_diff_preimage_source {β : Type*} [TopologicalSpace β] {e : PartialHomeomorph H β} :
    UniqueDiffOn 𝕜 (I.symm ⁻¹' e.source ∩ range I) :=
  I.unique_diff_preimage e.open_source
#align model_with_corners.unique_diff_preimage_source ModelWithCorners.unique_diff_preimage_source

theorem unique_diff_at_image {x : H} : UniqueDiffWithinAt 𝕜 (range I) (I x) :=
  I.unique_diff _ (mem_range_self _)
#align model_with_corners.unique_diff_at_image ModelWithCorners.unique_diff_at_image

theorem symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {f : H → X} {s : Set H}
    {x : H} :
    ContinuousWithinAt (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) ↔ ContinuousWithinAt f s x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.comp I.continuousWithinAt (mapsTo_preimage _ _)
    simp_rw [preimage_inter, preimage_preimage, I.left_inv, preimage_id', preimage_range,
      inter_univ] at this
    rwa [Function.comp.assoc, I.symm_comp_self] at this
  · rw [← I.left_inv x] at h; exact h.comp I.continuousWithinAt_symm (inter_subset_left _ _)
#align model_with_corners.symm_continuous_within_at_comp_right_iff ModelWithCorners.symm_continuousWithinAt_comp_right_iff

protected theorem locallyCompactSpace [LocallyCompactSpace E] (I : ModelWithCorners 𝕜 E H) :
    LocallyCompactSpace H := by
  have : ∀ x : H, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (I x) ∧ IsCompact s)
      fun s => I.symm '' (s ∩ range I) := fun x ↦ by
    rw [← I.symm_map_nhdsWithin_range]
    exact ((compact_basis_nhds (I x)).inf_principal _).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨-, hsc⟩
  exact (hsc.inter_right I.isClosed_range).image I.continuous_symm
#align model_with_corners.locally_compact ModelWithCorners.locallyCompactSpace

open TopologicalSpace

protected theorem secondCountableTopology [SecondCountableTopology E] (I : ModelWithCorners 𝕜 E H) :
    SecondCountableTopology H :=
  I.closedEmbedding.toEmbedding.secondCountableTopology
#align model_with_corners.second_countable_topology ModelWithCorners.secondCountableTopology

end ModelWithCorners

section

variable (𝕜 E)

/-- In the trivial model with corners, the associated `PartialEquiv` is the identity. -/
@[simp, mfld_simps]
theorem modelWithCornersSelf_partialEquiv : 𝓘(𝕜, E).toPartialEquiv = PartialEquiv.refl E :=
  rfl
#align model_with_corners_self_local_equiv modelWithCornersSelf_partialEquiv

@[simp, mfld_simps]
theorem modelWithCornersSelf_coe : (𝓘(𝕜, E) : E → E) = id :=
  rfl
#align model_with_corners_self_coe modelWithCornersSelf_coe

@[simp, mfld_simps]
theorem modelWithCornersSelf_coe_symm : (𝓘(𝕜, E).symm : E → E) = id :=
  rfl
#align model_with_corners_self_coe_symm modelWithCornersSelf_coe_symm

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
    unique_diff' := I.unique_diff'.prod I'.unique_diff'
    continuous_toFun := I.continuous_toFun.prod_map I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prod_map I'.continuous_invFun }
#align model_with_corners.prod ModelWithCorners.prod

/-- Given a finite family of `ModelWithCorners` `I i` on `(E i, H i)`, we define the model with
corners `pi I` on `(Π i, E i, ModelPi H)`. See note [Manifold type tags] for explanation about
`ModelPi H`. -/
def ModelWithCorners.pi {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
    {E : ι → Type w} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {H : ι → Type u'}
    [∀ i, TopologicalSpace (H i)] (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    ModelWithCorners 𝕜 (∀ i, E i) (ModelPi H) where
  toPartialEquiv := PartialEquiv.pi fun i => (I i).toPartialEquiv
  source_eq := by simp only [pi_univ, mfld_simps]
  unique_diff' := UniqueDiffOn.pi ι E _ _ fun i _ => (I i).unique_diff'
  continuous_toFun := continuous_pi fun i => (I i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)
#align model_with_corners.pi ModelWithCorners.pi

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
abbrev ModelWithCorners.tangent {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : ModelWithCorners 𝕜 (E × E) (ModelProd H E) :=
  I.prod 𝓘(𝕜, E)
#align model_with_corners.tangent ModelWithCorners.tangent

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] {G : Type*}
  [TopologicalSpace G] {G' : Type*} [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 F G}

@[simp, mfld_simps]
theorem modelWithCorners_prod_toPartialEquiv :
    (I.prod J).toPartialEquiv = I.toPartialEquiv.prod J.toPartialEquiv :=
  rfl
#align model_with_corners_prod_to_local_equiv modelWithCorners_prod_toPartialEquiv

@[simp, mfld_simps]
theorem modelWithCorners_prod_coe (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    (I.prod I' : _ × _ → _ × _) = Prod.map I I' :=
  rfl
#align model_with_corners_prod_coe modelWithCorners_prod_coe

@[simp, mfld_simps]
theorem modelWithCorners_prod_coe_symm (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') :
    ((I.prod I').symm : _ × _ → _ × _) = Prod.map I.symm I'.symm :=
  rfl
#align model_with_corners_prod_coe_symm modelWithCorners_prod_coe_symm

theorem modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜, E).prod 𝓘(𝕜, F) := by ext1 <;> simp
#align model_with_corners_self_prod modelWithCornersSelf_prod

theorem ModelWithCorners.range_prod : range (I.prod J) = range I ×ˢ range J := by
  simp_rw [← ModelWithCorners.target_eq]; rfl
#align model_with_corners.range_prod ModelWithCorners.range_prod

end ModelWithCornersProd

section Boundaryless

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. This
  differs from the more general `BoundarylessManifold`, which requires every point on the manifold
  to be an interior point.  -/
class ModelWithCorners.Boundaryless {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : Prop where
  range_eq_univ : range I = univ
#align model_with_corners.boundaryless ModelWithCorners.Boundaryless

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
#align model_with_corners_self_boundaryless modelWithCornersSelf_boundaryless

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
#align model_with_corners.range_eq_univ_prod ModelWithCorners.range_eq_univ_prod

end Boundaryless

section contDiffGroupoid

/-! ### Smooth functions on models with corners -/


variable {m n : ℕ∞} {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M]

variable (n)

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

/-- Given a model with corners `(E, H)`, we define the groupoid of invertible `C^n` transformations
  of `H` as the invertible maps that are `C^n` when read in `E` through `I`. -/
def contDiffGroupoid : StructureGroupoid H :=
  Pregroupoid.groupoid (contDiffPregroupoid n I)
#align cont_diff_groupoid contDiffGroupoid

variable {n}

/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
theorem contDiffGroupoid_le (h : m ≤ n) : contDiffGroupoid n I ≤ contDiffGroupoid m I := by
  rw [contDiffGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact ContDiffOn.of_le hfs h
#align cont_diff_groupoid_le contDiffGroupoid_le

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
    exact (mapsTo_preimage _ _).mono_left (inter_subset_left _ _)
  · refine I.continuous.comp_continuousOn (u.symm.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left (inter_subset_left _ _)
#align cont_diff_groupoid_zero_eq contDiffGroupoid_zero_eq

variable (n)

/-- An identity partial homeomorphism belongs to the `C^n` groupoid. -/
theorem ofSet_mem_contDiffGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ contDiffGroupoid n I := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : ContDiffOn 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I) by
    simp [h, contDiffPregroupoid]
  have : ContDiffOn 𝕜 n id (univ : Set E) := contDiff_id.contDiffOn
  exact this.congr_mono (fun x hx => I.right_inv hx.2) (subset_univ _)
#align of_set_mem_cont_diff_groupoid ofSet_mem_contDiffGroupoid

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
theorem symm_trans_mem_contDiffGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ contDiffGroupoid n I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_contDiffGroupoid n I e.open_target) this
#align symm_trans_mem_cont_diff_groupoid symm_trans_mem_contDiffGroupoid

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']

/-- The product of two smooth partial homeomorphisms is smooth. -/
theorem contDiffGroupoid_prod {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {e : PartialHomeomorph H H} {e' : PartialHomeomorph H' H'} (he : e ∈ contDiffGroupoid ⊤ I)
    (he' : e' ∈ contDiffGroupoid ⊤ I') : e.prod e' ∈ contDiffGroupoid ⊤ (I.prod I') := by
  cases' he with he he_symm
  cases' he' with he' he'_symm
  simp only at he he_symm he' he'_symm
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
#align cont_diff_groupoid_prod contDiffGroupoid_prod

/-- The `C^n` groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (contDiffGroupoid n I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      apply (contDiffGroupoid n I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_contDiffGroupoid n I hs)

end contDiffGroupoid

section analyticGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M]

/-- Given a model with corners `(E, H)`, we define the groupoid of analytic transformations of `H`
as the maps that are analytic and map interior to interior when read in `E` through `I`. We also
explicitly define that they are `C^∞` on the whole domain, since we are only requiring
analyticity on the interior of the domain. -/
def analyticGroupoid : StructureGroupoid H :=
  (contDiffGroupoid ∞ I) ⊓ Pregroupoid.groupoid
    { property := fun f s => AnalyticOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
        (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)
      comp := fun {f g u v} hf hg _ _ _ => by
        simp only [] at hf hg ⊢
        have comp : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
        apply And.intro
        · simp only [comp, preimage_inter]
          refine hg.left.comp (hf.left.mono ?_) ?_
          · simp only [subset_inter_iff, inter_subset_right]
            rw [inter_assoc]
            simp
          · intro x hx
            apply And.intro
            · rw [mem_preimage, comp_apply, I.left_inv]
              exact hx.left.right
            · apply hf.right
              rw [mem_image]
              exact ⟨x, ⟨⟨hx.left.left, hx.right⟩, rfl⟩⟩
        · simp only [comp]
          rw [image_comp]
          intro x hx
          rw [mem_image] at hx
          rcases hx with ⟨x', hx'⟩
          refine hg.right ⟨x', And.intro ?_ hx'.right⟩
          apply And.intro
          · have hx'1 : x' ∈ ((v.preimage f).preimage (I.symm)).image (I ∘ f ∘ I.symm) := by
              refine image_subset (I ∘ f ∘ I.symm) ?_ hx'.left
              rw [preimage_inter]
              refine Subset.trans ?_ (inter_subset_right (u.preimage I.symm)
                ((v.preimage f).preimage I.symm))
              apply inter_subset_left
            rcases hx'1 with ⟨x'', hx''⟩
            rw [hx''.right.symm]
            simp only [comp_apply, mem_preimage, I.left_inv]
            exact hx''.left
          · rw [mem_image] at hx'
            rcases hx'.left with ⟨x'', hx''⟩
            exact hf.right ⟨x'', ⟨⟨hx''.left.left.left, hx''.left.right⟩, hx''.right⟩⟩
      id_mem := by
        apply And.intro
        · simp only [preimage_univ, univ_inter]
          exact AnalyticOn.congr isOpen_interior
            (f := (1 : E →L[𝕜] E)) (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
            (fun z hz => (I.right_inv (interior_subset hz)).symm)
        · intro x hx
          simp only [id_comp, comp_apply, preimage_univ, univ_inter, mem_image] at hx
          rcases hx with ⟨y, hy⟩
          rw [← hy.right, I.right_inv (interior_subset hy.left)]
          exact hy.left
      locality := fun {f u} _ h => by
        simp only [] at h
        simp only [AnalyticOn]
        apply And.intro
        · intro x hx
          rcases h (I.symm x) (mem_preimage.mp hx.left) with ⟨v, hv⟩
          exact hv.right.right.left x ⟨mem_preimage.mpr ⟨hx.left, hv.right.left⟩, hx.right⟩
        · apply mapsTo'.mp
          simp only [MapsTo]
          intro x hx
          rcases h (I.symm x) hx.left with ⟨v, hv⟩
          apply hv.right.right.right
          rw [mem_image]
          have hx' := And.intro hx (mem_preimage.mpr hv.right.left)
          rw [← mem_inter_iff, inter_comm, ← inter_assoc, ← preimage_inter, inter_comm v u] at hx'
          exact ⟨x, ⟨hx', rfl⟩⟩
      congr := fun {f g u} hu fg hf => by
        simp only [] at hf ⊢
        apply And.intro
        · refine AnalyticOn.congr (IsOpen.inter (hu.preimage I.continuous_symm) isOpen_interior)
            hf.left ?_
          intro z hz
          simp only [comp_apply]
          rw [fg (I.symm z) hz.left]
        · intro x hx
          apply hf.right
          rw [mem_image] at hx ⊢
          rcases hx with ⟨y, hy⟩
          refine ⟨y, ⟨hy.left, ?_⟩⟩
          rw [comp_apply, comp_apply, fg (I.symm y) hy.left.left] at hy
          exact hy.right }

/-- An identity partial homeomorphism belongs to the analytic groupoid. -/
theorem ofSet_mem_analyticGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ analyticGroupoid I := by
  rw [analyticGroupoid]
  refine And.intro (ofSet_mem_contDiffGroupoid ∞ I hs) ?_
  apply mem_groupoid_of_pregroupoid.mpr
  suffices h : AnalyticOn 𝕜 (I ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
      (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ I.symm) ⊆ interior (range I) by
    simp only [PartialHomeomorph.ofSet_apply, id_comp, PartialHomeomorph.ofSet_toPartialEquiv,
      PartialEquiv.ofSet_source, h, comp_apply, mem_range, image_subset_iff, true_and,
      PartialHomeomorph.ofSet_symm, PartialEquiv.ofSet_target, and_self]
    intro x hx
    refine mem_preimage.mpr ?_
    rw [← I.right_inv (interior_subset hx.right)] at hx
    exact hx.right
  apply And.intro
  · have : AnalyticOn 𝕜 (1 : E →L[𝕜] E) (univ : Set E) := (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
    exact (this.mono (subset_univ (s.preimage (I.symm) ∩ interior (range I)))).congr
      ((hs.preimage I.continuous_symm).inter isOpen_interior)
      fun z hz => (I.right_inv (interior_subset hz.right)).symm
  · intro x hx
    simp only [comp_apply, mem_image] at hx
    rcases hx with ⟨y, hy⟩
    rw [← hy.right, I.right_inv (interior_subset hy.left.right)]
    exact hy.left.right

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the analytic groupoid. -/
theorem symm_trans_mem_analyticGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ analyticGroupoid I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_analyticGroupoid I e.open_target) this

/-- The analytic groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (analyticGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      apply (analyticGroupoid I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_analyticGroupoid I hs)

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem mem_analyticGroupoid_of_boundaryless [CompleteSpace E] [I.Boundaryless]
    (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOn 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
    AnalyticOn 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  apply Iff.intro
  · intro he
    have := mem_groupoid_of_pregroupoid.mp he.right
    simp only [I.image_eq, I.range_eq_univ, interior_univ, subset_univ, and_true] at this ⊢
    exact this
  · intro he
    apply And.intro
    all_goals apply mem_groupoid_of_pregroupoid.mpr; simp only [I.image_eq, I.range_eq_univ,
      interior_univ, subset_univ, and_true, contDiffPregroupoid] at he ⊢
    · exact ⟨he.left.contDiffOn, he.right.contDiffOn⟩
    · exact he

end analyticGroupoid

section SmoothManifoldWithCorners

/-! ### Smooth manifolds with corners -/


/-- Typeclass defining smooth manifolds with corners with respect to a model with corners, over a
field `𝕜` and with infinite smoothness to simplify typeclass search and statements later on. -/
class SmoothManifoldWithCorners {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] extends
    HasGroupoid M (contDiffGroupoid ∞ I) : Prop
#align smooth_manifold_with_corners SmoothManifoldWithCorners

theorem SmoothManifoldWithCorners.mk' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [gr : HasGroupoid M (contDiffGroupoid ∞ I)] : SmoothManifoldWithCorners I M :=
  { gr with }
#align smooth_manifold_with_corners.mk' SmoothManifoldWithCorners.mk'

theorem smoothManifoldWithCorners_of_contDiffOn {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (h : ∀ e e' : PartialHomeomorph M H, e ∈ atlas H M → e' ∈ atlas H M →
      ContDiffOn 𝕜 ⊤ (I ∘ e.symm ≫ₕ e' ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I)) :
    SmoothManifoldWithCorners I M where
  compatible := by
    haveI : HasGroupoid M (contDiffGroupoid ∞ I) := hasGroupoid_of_pregroupoid _ (h _ _)
    apply StructureGroupoid.compatible
#align smooth_manifold_with_corners_of_cont_diff_on smoothManifoldWithCorners_of_contDiffOn

/-- For any model with corners, the model space is a smooth manifold -/
instance model_space_smooth {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} : SmoothManifoldWithCorners I H :=
  { hasGroupoid_model_space _ _ with }
#align model_space_smooth model_space_smooth

end SmoothManifoldWithCorners

namespace SmoothManifoldWithCorners

/- We restate in the namespace `SmoothManifoldWithCorners` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`contDiffGroupoid ∞ I` explicitly. -/
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M]

/-- The maximal atlas of `M` for the smooth manifold with corners structure corresponding to the
model with corners `I`. -/
def maximalAtlas :=
  (contDiffGroupoid ∞ I).maximalAtlas M
#align smooth_manifold_with_corners.maximal_atlas SmoothManifoldWithCorners.maximalAtlas

variable {M}

theorem subset_maximalAtlas [SmoothManifoldWithCorners I M] : atlas H M ⊆ maximalAtlas I M :=
  StructureGroupoid.subset_maximalAtlas _
#align smooth_manifold_with_corners.subset_maximal_atlas SmoothManifoldWithCorners.subset_maximalAtlas

theorem chart_mem_maximalAtlas [SmoothManifoldWithCorners I M] (x : M) :
    chartAt H x ∈ maximalAtlas I M :=
  StructureGroupoid.chart_mem_maximalAtlas _ x
#align smooth_manifold_with_corners.chart_mem_maximal_atlas SmoothManifoldWithCorners.chart_mem_maximalAtlas

variable {I}

theorem compatible_of_mem_maximalAtlas {e e' : PartialHomeomorph M H} (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I M) : e.symm.trans e' ∈ contDiffGroupoid ∞ I :=
  StructureGroupoid.compatible_of_mem_maximalAtlas he he'
#align smooth_manifold_with_corners.compatible_of_mem_maximal_atlas SmoothManifoldWithCorners.compatible_of_mem_maximalAtlas

/-- The product of two smooth manifolds with corners is naturally a smooth manifold with corners. -/
instance prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']
    [SmoothManifoldWithCorners I' M'] : SmoothManifoldWithCorners (I.prod I') (M × M') where
  compatible := by
    rintro f g ⟨f1, hf1, f2, hf2, rfl⟩ ⟨g1, hg1, g2, hg2, rfl⟩
    rw [PartialHomeomorph.prod_symm, PartialHomeomorph.prod_trans]
    have h1 := (contDiffGroupoid ⊤ I).compatible hf1 hg1
    have h2 := (contDiffGroupoid ⊤ I').compatible hf2 hg2
    exact contDiffGroupoid_prod h1 h2
#align smooth_manifold_with_corners.prod SmoothManifoldWithCorners.prod

end SmoothManifoldWithCorners

theorem PartialHomeomorph.singleton_smoothManifoldWithCorners
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] (e : PartialHomeomorph M H) (h : e.source = Set.univ) :
    @SmoothManifoldWithCorners 𝕜 _ E _ _ H _ I M _ (e.singletonChartedSpace h) :=
  @SmoothManifoldWithCorners.mk' _ _ _ _ _ _ _ _ _ _ (id _) <|
    e.singleton_hasGroupoid h (contDiffGroupoid ∞ I)
#align local_homeomorph.singleton_smooth_manifold_with_corners PartialHomeomorph.singleton_smoothManifoldWithCorners

theorem OpenEmbedding.singleton_smoothManifoldWithCorners {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [Nonempty M] {f : M → H}
    (h : OpenEmbedding f) :
    @SmoothManifoldWithCorners 𝕜 _ E _ _ H _ I M _ h.singletonChartedSpace :=
  (h.toPartialHomeomorph f).singleton_smoothManifoldWithCorners I (by simp)
#align open_embedding.singleton_smooth_manifold_with_corners OpenEmbedding.singleton_smoothManifoldWithCorners

namespace TopologicalSpace.Opens

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] (s : Opens M)

instance : SmoothManifoldWithCorners I s :=
  { s.instHasGroupoid (contDiffGroupoid ∞ I) with }

end TopologicalSpace.Opens

section ExtendedCharts

open scoped Topology

variable {𝕜 E M H E' M' H' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] (f f' : PartialHomeomorph M H)
  (I : ModelWithCorners 𝕜 E H) [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [TopologicalSpace M'] (I' : ModelWithCorners 𝕜 E' H') {s t : Set M}

/-!
### Extended charts

In a smooth manifold with corners, the model space is the space `H`. However, we will also
need to use extended charts taking values in the model vector space `E`. These extended charts are
not `PartialHomeomorph` as the target is not open in `E` in general, but we can still register them
as `PartialEquiv`.
-/


namespace PartialHomeomorph

/-- Given a chart `f` on a manifold with corners, `f.extend I` is the extended chart to the model
vector space. -/
@[simp, mfld_simps]
def extend : PartialEquiv M E :=
  f.toPartialEquiv ≫ I.toPartialEquiv
#align local_homeomorph.extend PartialHomeomorph.extend

theorem extend_coe : ⇑(f.extend I) = I ∘ f :=
  rfl
#align local_homeomorph.extend_coe PartialHomeomorph.extend_coe

theorem extend_coe_symm : ⇑(f.extend I).symm = f.symm ∘ I.symm :=
  rfl
#align local_homeomorph.extend_coe_symm PartialHomeomorph.extend_coe_symm

theorem extend_source : (f.extend I).source = f.source := by
  rw [extend, PartialEquiv.trans_source, I.source_eq, preimage_univ, inter_univ]
#align local_homeomorph.extend_source PartialHomeomorph.extend_source

theorem isOpen_extend_source : IsOpen (f.extend I).source := by
  rw [extend_source]
  exact f.open_source
#align local_homeomorph.is_open_extend_source PartialHomeomorph.isOpen_extend_source

theorem extend_target : (f.extend I).target = I.symm ⁻¹' f.target ∩ range I := by
  simp_rw [extend, PartialEquiv.trans_target, I.target_eq, I.toPartialEquiv_coe_symm, inter_comm]
#align local_homeomorph.extend_target PartialHomeomorph.extend_target

theorem extend_target' : (f.extend I).target = I '' f.target := by
  rw [extend, PartialEquiv.trans_target'', I.source_eq, univ_inter, I.toPartialEquiv_coe]

lemma isOpen_extend_target [I.Boundaryless] : IsOpen (f.extend I).target := by
  rw [extend_target, I.range_eq_univ, inter_univ]
  exact I.continuous_symm.isOpen_preimage _ f.open_target

theorem mapsTo_extend (hs : s ⊆ f.source) :
    MapsTo (f.extend I) s ((f.extend I).symm ⁻¹' s ∩ range I) := by
  rw [mapsTo', extend_coe, extend_coe_symm, preimage_comp, ← I.image_eq, image_comp,
    f.image_eq_target_inter_inv_preimage hs]
  exact image_subset _ (inter_subset_right _ _)
#align local_homeomorph.maps_to_extend PartialHomeomorph.mapsTo_extend

theorem extend_left_inv {x : M} (hxf : x ∈ f.source) : (f.extend I).symm (f.extend I x) = x :=
  (f.extend I).left_inv <| by rwa [f.extend_source]
#align local_homeomorph.extend_left_inv PartialHomeomorph.extend_left_inv

/-- Variant of `f.extend_left_inv I`, stated in terms of images. -/
lemma extend_left_inv' (ht: t ⊆ f.source) : ((f.extend I).symm ∘ (f.extend I)) '' t = t :=
  EqOn.image_eq_self (fun _ hx ↦ f.extend_left_inv I (ht hx))

theorem extend_source_mem_nhds {x : M} (h : x ∈ f.source) : (f.extend I).source ∈ 𝓝 x :=
  (isOpen_extend_source f I).mem_nhds <| by rwa [f.extend_source I]
#align local_homeomorph.extend_source_mem_nhds PartialHomeomorph.extend_source_mem_nhds

theorem extend_source_mem_nhdsWithin {x : M} (h : x ∈ f.source) : (f.extend I).source ∈ 𝓝[s] x :=
  mem_nhdsWithin_of_mem_nhds <| extend_source_mem_nhds f I h
#align local_homeomorph.extend_source_mem_nhds_within PartialHomeomorph.extend_source_mem_nhdsWithin

theorem continuousOn_extend : ContinuousOn (f.extend I) (f.extend I).source := by
  refine I.continuous.comp_continuousOn ?_
  rw [extend_source]
  exact f.continuousOn
#align local_homeomorph.continuous_on_extend PartialHomeomorph.continuousOn_extend

theorem continuousAt_extend {x : M} (h : x ∈ f.source) : ContinuousAt (f.extend I) x :=
  (continuousOn_extend f I).continuousAt <| extend_source_mem_nhds f I h
#align local_homeomorph.continuous_at_extend PartialHomeomorph.continuousAt_extend

theorem map_extend_nhds {x : M} (hy : x ∈ f.source) :
    map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x := by
  rwa [extend_coe, comp_apply, ← I.map_nhds_eq, ← f.map_nhds_eq, map_map]
#align local_homeomorph.map_extend_nhds PartialHomeomorph.map_extend_nhds

theorem map_extend_nhds_of_boundaryless [I.Boundaryless] {x : M} (hx : x ∈ f.source) :
    map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x) := by
  rw [f.map_extend_nhds _ hx, I.range_eq_univ, nhdsWithin_univ]

theorem extend_target_mem_nhdsWithin {y : M} (hy : y ∈ f.source) :
    (f.extend I).target ∈ 𝓝[range I] f.extend I y := by
  rw [← PartialEquiv.image_source_eq_target, ← map_extend_nhds f I hy]
  exact image_mem_map (extend_source_mem_nhds _ _ hy)
#align local_homeomorph.extend_target_mem_nhds_within PartialHomeomorph.extend_target_mem_nhdsWithin

theorem extend_image_nhd_mem_nhds_of_boundaryless [I.Boundaryless] {x} (hx : x ∈ f.source)
    {s : Set M} (h : s ∈ 𝓝 x) : (f.extend I) '' s ∈ 𝓝 ((f.extend I) x) := by
  rw [← f.map_extend_nhds_of_boundaryless _ hx, Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

theorem extend_target_subset_range : (f.extend I).target ⊆ range I := by simp only [mfld_simps]
#align local_homeomorph.extend_target_subset_range PartialHomeomorph.extend_target_subset_range

lemma interior_extend_target_subset_interior_range :
    interior (f.extend I).target ⊆ interior (range I) := by
  rw [f.extend_target, interior_inter, (f.open_target.preimage I.continuous_symm).interior_eq]
  exact inter_subset_right _ _

/-- If `y ∈ f.target` and `I y ∈ interior (range I)`,
  then `I y` is an interior point of `(I ∘ f).target`. -/
lemma mem_interior_extend_target {y : H} (hy : y ∈ f.target)
    (hy' : I y ∈ interior (range I)) : I y ∈ interior (f.extend I).target := by
  rw [f.extend_target, interior_inter, (f.open_target.preimage I.continuous_symm).interior_eq,
    mem_inter_iff, mem_preimage]
  exact ⟨mem_of_eq_of_mem (I.left_inv (y)) hy, hy'⟩

theorem nhdsWithin_extend_target_eq {y : M} (hy : y ∈ f.source) :
    𝓝[(f.extend I).target] f.extend I y = 𝓝[range I] f.extend I y :=
  (nhdsWithin_mono _ (extend_target_subset_range _ _)).antisymm <|
    nhdsWithin_le_of_mem (extend_target_mem_nhdsWithin _ _ hy)
#align local_homeomorph.nhds_within_extend_target_eq PartialHomeomorph.nhdsWithin_extend_target_eq

theorem continuousAt_extend_symm' {x : E} (h : x ∈ (f.extend I).target) :
    ContinuousAt (f.extend I).symm x :=
  (f.continuousAt_symm h.2).comp I.continuous_symm.continuousAt
#align local_homeomorph.continuous_at_extend_symm' PartialHomeomorph.continuousAt_extend_symm'

theorem continuousAt_extend_symm {x : M} (h : x ∈ f.source) :
    ContinuousAt (f.extend I).symm (f.extend I x) :=
  continuousAt_extend_symm' f I <| (f.extend I).map_source <| by rwa [f.extend_source]
#align local_homeomorph.continuous_at_extend_symm PartialHomeomorph.continuousAt_extend_symm

theorem continuousOn_extend_symm : ContinuousOn (f.extend I).symm (f.extend I).target := fun _ h =>
  (continuousAt_extend_symm' _ _ h).continuousWithinAt
#align local_homeomorph.continuous_on_extend_symm PartialHomeomorph.continuousOn_extend_symm

theorem extend_symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {g : M → X}
    {s : Set M} {x : M} :
    ContinuousWithinAt (g ∘ (f.extend I).symm) ((f.extend I).symm ⁻¹' s ∩ range I) (f.extend I x) ↔
      ContinuousWithinAt (g ∘ f.symm) (f.symm ⁻¹' s) (f x) := by
  rw [← I.symm_continuousWithinAt_comp_right_iff]; rfl
#align local_homeomorph.extend_symm_continuous_within_at_comp_right_iff PartialHomeomorph.extend_symm_continuousWithinAt_comp_right_iff

theorem isOpen_extend_preimage' {s : Set E} (hs : IsOpen s) :
    IsOpen ((f.extend I).source ∩ f.extend I ⁻¹' s) :=
  (continuousOn_extend f I).isOpen_inter_preimage (isOpen_extend_source _ _) hs
#align local_homeomorph.is_open_extend_preimage' PartialHomeomorph.isOpen_extend_preimage'

theorem isOpen_extend_preimage {s : Set E} (hs : IsOpen s) :
    IsOpen (f.source ∩ f.extend I ⁻¹' s) := by
  rw [← extend_source f I]; exact isOpen_extend_preimage' f I hs
#align local_homeomorph.is_open_extend_preimage PartialHomeomorph.isOpen_extend_preimage

theorem map_extend_nhdsWithin_eq_image {y : M} (hy : y ∈ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' ((f.extend I).source ∩ s)] f.extend I y := by
  set e := f.extend I
  calc
    map e (𝓝[s] y) = map e (𝓝[e.source ∩ s] y) :=
      congr_arg (map e) (nhdsWithin_inter_of_mem (extend_source_mem_nhdsWithin f I hy)).symm
    _ = 𝓝[e '' (e.source ∩ s)] e y :=
      ((f.extend I).leftInvOn.mono <| inter_subset_left _ _).map_nhdsWithin_eq
        ((f.extend I).left_inv <| by rwa [f.extend_source])
        (continuousAt_extend_symm f I hy).continuousWithinAt
        (continuousAt_extend f I hy).continuousWithinAt
#align local_homeomorph.map_extend_nhds_within_eq_image PartialHomeomorph.map_extend_nhdsWithin_eq_image

theorem map_extend_nhdsWithin_eq_image_of_subset {y : M} (hy : y ∈ f.source) (hs : s ⊆ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' s] f.extend I y := by
  rw [map_extend_nhdsWithin_eq_image _ _ hy, inter_eq_self_of_subset_right]
  rwa [extend_source]

theorem map_extend_nhdsWithin {y : M} (hy : y ∈ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I y := by
  rw [map_extend_nhdsWithin_eq_image f I hy, nhdsWithin_inter, ←
    nhdsWithin_extend_target_eq _ _ hy, ← nhdsWithin_inter, (f.extend I).image_source_inter_eq',
    inter_comm]
#align local_homeomorph.map_extend_nhds_within PartialHomeomorph.map_extend_nhdsWithin

theorem map_extend_symm_nhdsWithin {y : M} (hy : y ∈ f.source) :
    map (f.extend I).symm (𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I y) = 𝓝[s] y := by
  rw [← map_extend_nhdsWithin f I hy, map_map, Filter.map_congr, map_id]
  exact (f.extend I).leftInvOn.eqOn.eventuallyEq_of_mem (extend_source_mem_nhdsWithin _ _ hy)
#align local_homeomorph.map_extend_symm_nhds_within PartialHomeomorph.map_extend_symm_nhdsWithin

theorem map_extend_symm_nhdsWithin_range {y : M} (hy : y ∈ f.source) :
    map (f.extend I).symm (𝓝[range I] f.extend I y) = 𝓝 y := by
  rw [← nhdsWithin_univ, ← map_extend_symm_nhdsWithin f I hy, preimage_univ, univ_inter]
#align local_homeomorph.map_extend_symm_nhds_within_range PartialHomeomorph.map_extend_symm_nhdsWithin_range

theorem tendsto_extend_comp_iff {α : Type*} {l : Filter α} {g : α → M}
    (hg : ∀ᶠ z in l, g z ∈ f.source) {y : M} (hy : y ∈ f.source) :
    Tendsto (f.extend I ∘ g) l (𝓝 (f.extend I y)) ↔ Tendsto g l (𝓝 y) := by
  refine ⟨fun h u hu ↦ mem_map.2 ?_, (continuousAt_extend _ _ hy).tendsto.comp⟩
  have := (f.continuousAt_extend_symm I hy).tendsto.comp h
  rw [extend_left_inv _ _ hy] at this
  filter_upwards [hg, mem_map.1 (this hu)] with z hz hzu
  simpa only [(· ∘ ·), extend_left_inv _ _ hz, mem_preimage] using hzu

-- there is no definition `writtenInExtend` but we already use some made-up names in this file
theorem continuousWithinAt_writtenInExtend_iff {f' : PartialHomeomorph M' H'} {g : M → M'} {y : M}
    (hy : y ∈ f.source) (hgy : g y ∈ f'.source) (hmaps : MapsTo g s f'.source) :
    ContinuousWithinAt (f'.extend I' ∘ g ∘ (f.extend I).symm)
      ((f.extend I).symm ⁻¹' s ∩ range I) (f.extend I y) ↔ ContinuousWithinAt g s y := by
  unfold ContinuousWithinAt
  simp only [comp_apply]
  rw [extend_left_inv _ _ hy, f'.tendsto_extend_comp_iff _ _ hgy,
    ← f.map_extend_symm_nhdsWithin I hy, tendsto_map'_iff]
  rw [← f.map_extend_nhdsWithin I hy, eventually_map]
  filter_upwards [inter_mem_nhdsWithin _ (f.open_source.mem_nhds hy)] with z hz
  rw [comp_apply, extend_left_inv _ _ hz.2]
  exact hmaps hz.1

-- there is no definition `writtenInExtend` but we already use some made-up names in this file

/-- If `s ⊆ f.source` and `g x ∈ f'.source` whenever `x ∈ s`, then `g` is continuous on `s` if and
only if `g` written in charts `f.extend I` and `f'.extend I'` is continuous on `f.extend I '' s`. -/
theorem continuousOn_writtenInExtend_iff {f' : PartialHomeomorph M' H'} {g : M → M'}
    (hs : s ⊆ f.source) (hmaps : MapsTo g s f'.source) :
    ContinuousOn (f'.extend I' ∘ g ∘ (f.extend I).symm) (f.extend I '' s) ↔ ContinuousOn g s := by
  refine forall_mem_image.trans <| forall₂_congr fun x hx ↦ ?_
  refine (continuousWithinAt_congr_nhds ?_).trans
    (continuousWithinAt_writtenInExtend_iff _ _ _ (hs hx) (hmaps hx) hmaps)
  rw [← map_extend_nhdsWithin_eq_image_of_subset, ← map_extend_nhdsWithin]
  exacts [hs hx, hs hx, hs]

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
theorem extend_preimage_mem_nhdsWithin {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝[s] x) :
    (f.extend I).symm ⁻¹' t ∈ 𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I x := by
  rwa [← map_extend_symm_nhdsWithin f I h, mem_map] at ht
#align local_homeomorph.extend_preimage_mem_nhds_within PartialHomeomorph.extend_preimage_mem_nhdsWithin

theorem extend_preimage_mem_nhds {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝 x) :
    (f.extend I).symm ⁻¹' t ∈ 𝓝 (f.extend I x) := by
  apply (continuousAt_extend_symm f I h).preimage_mem_nhds
  rwa [(f.extend I).left_inv]
  rwa [f.extend_source]
#align local_homeomorph.extend_preimage_mem_nhds PartialHomeomorph.extend_preimage_mem_nhds

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
theorem extend_preimage_inter_eq :
    (f.extend I).symm ⁻¹' (s ∩ t) ∩ range I =
      (f.extend I).symm ⁻¹' s ∩ range I ∩ (f.extend I).symm ⁻¹' t := by
  mfld_set_tac
#align local_homeomorph.extend_preimage_inter_eq PartialHomeomorph.extend_preimage_inter_eq

-- Porting note: an `aux` lemma that is no longer needed. Delete?
theorem extend_symm_preimage_inter_range_eventuallyEq_aux {s : Set M} {x : M} (hx : x ∈ f.source) :
    ((f.extend I).symm ⁻¹' s ∩ range I : Set _) =ᶠ[𝓝 (f.extend I x)]
      ((f.extend I).target ∩ (f.extend I).symm ⁻¹' s : Set _) := by
  rw [f.extend_target, inter_assoc, inter_comm (range I)]
  conv =>
    congr
    · skip
    rw [← univ_inter (_ ∩ range I)]
  refine (eventuallyEq_univ.mpr ?_).symm.inter EventuallyEq.rfl
  refine I.continuousAt_symm.preimage_mem_nhds (f.open_target.mem_nhds ?_)
  simp_rw [f.extend_coe, Function.comp_apply, I.left_inv, f.mapsTo hx]
#align local_homeomorph.extend_symm_preimage_inter_range_eventually_eq_aux PartialHomeomorph.extend_symm_preimage_inter_range_eventuallyEq_aux

theorem extend_symm_preimage_inter_range_eventuallyEq {s : Set M} {x : M} (hs : s ⊆ f.source)
    (hx : x ∈ f.source) :
    ((f.extend I).symm ⁻¹' s ∩ range I : Set _) =ᶠ[𝓝 (f.extend I x)] f.extend I '' s := by
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← map_extend_nhdsWithin _ _ hx,
    map_extend_nhdsWithin_eq_image_of_subset _ _ hx hs]
#align local_homeomorph.extend_symm_preimage_inter_range_eventually_eq PartialHomeomorph.extend_symm_preimage_inter_range_eventuallyEq

/-! We use the name `extend_coord_change` for `(f'.extend I).symm ≫ f.extend I`. -/

theorem extend_coord_change_source :
    ((f.extend I).symm ≫ f'.extend I).source = I '' (f.symm ≫ₕ f').source := by
  simp_rw [PartialEquiv.trans_source, I.image_eq, extend_source, PartialEquiv.symm_source,
    extend_target, inter_right_comm _ (range I)]
  rfl
#align local_homeomorph.extend_coord_change_source PartialHomeomorph.extend_coord_change_source

theorem extend_image_source_inter :
    f.extend I '' (f.source ∩ f'.source) = ((f.extend I).symm ≫ f'.extend I).source := by
  simp_rw [f.extend_coord_change_source, f.extend_coe, image_comp I f, trans_source'', symm_symm,
    symm_target]
#align local_homeomorph.extend_image_source_inter PartialHomeomorph.extend_image_source_inter

theorem extend_coord_change_source_mem_nhdsWithin {x : E}
    (hx : x ∈ ((f.extend I).symm ≫ f'.extend I).source) :
    ((f.extend I).symm ≫ f'.extend I).source ∈ 𝓝[range I] x := by
  rw [f.extend_coord_change_source] at hx ⊢
  obtain ⟨x, hx, rfl⟩ := hx
  refine I.image_mem_nhdsWithin ?_
  exact (PartialHomeomorph.open_source _).mem_nhds hx
#align local_homeomorph.extend_coord_change_source_mem_nhds_within PartialHomeomorph.extend_coord_change_source_mem_nhdsWithin

theorem extend_coord_change_source_mem_nhdsWithin' {x : M} (hxf : x ∈ f.source)
    (hxf' : x ∈ f'.source) :
    ((f.extend I).symm ≫ f'.extend I).source ∈ 𝓝[range I] f.extend I x := by
  apply extend_coord_change_source_mem_nhdsWithin
  rw [← extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxf, hxf'⟩
#align local_homeomorph.extend_coord_change_source_mem_nhds_within' PartialHomeomorph.extend_coord_change_source_mem_nhdsWithin'

variable {f f'}

open SmoothManifoldWithCorners

theorem contDiffOn_extend_coord_change [ChartedSpace H M] (hf : f ∈ maximalAtlas I M)
    (hf' : f' ∈ maximalAtlas I M) :
    ContDiffOn 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm) ((f'.extend I).symm ≫ f.extend I).source := by
  rw [extend_coord_change_source, I.image_eq]
  exact (StructureGroupoid.compatible_of_mem_maximalAtlas hf' hf).1
#align local_homeomorph.cont_diff_on_extend_coord_change PartialHomeomorph.contDiffOn_extend_coord_change

theorem contDiffWithinAt_extend_coord_change [ChartedSpace H M] (hf : f ∈ maximalAtlas I M)
    (hf' : f' ∈ maximalAtlas I M) {x : E} (hx : x ∈ ((f'.extend I).symm ≫ f.extend I).source) :
    ContDiffWithinAt 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm) (range I) x := by
  apply (contDiffOn_extend_coord_change I hf hf' x hx).mono_of_mem
  rw [extend_coord_change_source] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  exact I.image_mem_nhdsWithin ((PartialHomeomorph.open_source _).mem_nhds hz)
#align local_homeomorph.cont_diff_within_at_extend_coord_change PartialHomeomorph.contDiffWithinAt_extend_coord_change

theorem contDiffWithinAt_extend_coord_change' [ChartedSpace H M] (hf : f ∈ maximalAtlas I M)
    (hf' : f' ∈ maximalAtlas I M) {x : M} (hxf : x ∈ f.source) (hxf' : x ∈ f'.source) :
    ContDiffWithinAt 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm) (range I) (f'.extend I x) := by
  refine contDiffWithinAt_extend_coord_change I hf hf' ?_
  rw [← extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxf', hxf⟩
#align local_homeomorph.cont_diff_within_at_extend_coord_change' PartialHomeomorph.contDiffWithinAt_extend_coord_change'

end PartialHomeomorph

open PartialHomeomorph

variable [ChartedSpace H M] [ChartedSpace H' M']

/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp, mfld_simps]
def extChartAt (x : M) : PartialEquiv M E :=
  (chartAt H x).extend I
#align ext_chart_at extChartAt

theorem extChartAt_coe (x : M) : ⇑(extChartAt I x) = I ∘ chartAt H x :=
  rfl
#align ext_chart_at_coe extChartAt_coe

theorem extChartAt_coe_symm (x : M) : ⇑(extChartAt I x).symm = (chartAt H x).symm ∘ I.symm :=
  rfl
#align ext_chart_at_coe_symm extChartAt_coe_symm

theorem extChartAt_source (x : M) : (extChartAt I x).source = (chartAt H x).source :=
  extend_source _ _
#align ext_chart_at_source extChartAt_source

theorem isOpen_extChartAt_source (x : M) : IsOpen (extChartAt I x).source :=
  isOpen_extend_source _ _
#align is_open_ext_chart_at_source isOpen_extChartAt_source

theorem mem_extChartAt_source (x : M) : x ∈ (extChartAt I x).source := by
  simp only [extChartAt_source, mem_chart_source]
#align mem_ext_chart_source mem_extChartAt_source

theorem mem_extChartAt_target (x : M) : extChartAt I x x ∈ (extChartAt I x).target :=
  (extChartAt I x).map_source <| mem_extChartAt_source _ _

theorem extChartAt_target (x : M) :
    (extChartAt I x).target = I.symm ⁻¹' (chartAt H x).target ∩ range I :=
  extend_target _ _
#align ext_chart_at_target extChartAt_target

theorem uniqueDiffOn_extChartAt_target (x : M) : UniqueDiffOn 𝕜 (extChartAt I x).target := by
  rw [extChartAt_target]
  exact I.unique_diff_preimage (chartAt H x).open_target

theorem uniqueDiffWithinAt_extChartAt_target (x : M) :
    UniqueDiffWithinAt 𝕜 (extChartAt I x).target (extChartAt I x x) :=
  uniqueDiffOn_extChartAt_target I x _ <| mem_extChartAt_target I x

theorem extChartAt_to_inv (x : M) : (extChartAt I x).symm ((extChartAt I x) x) = x :=
  (extChartAt I x).left_inv (mem_extChartAt_source I x)
#align ext_chart_at_to_inv extChartAt_to_inv

theorem mapsTo_extChartAt {x : M} (hs : s ⊆ (chartAt H x).source) :
    MapsTo (extChartAt I x) s ((extChartAt I x).symm ⁻¹' s ∩ range I) :=
  mapsTo_extend _ _ hs
#align maps_to_ext_chart_at mapsTo_extChartAt

theorem extChartAt_source_mem_nhds' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    (extChartAt I x).source ∈ 𝓝 x' :=
  extend_source_mem_nhds _ _ <| by rwa [← extChartAt_source I]
#align ext_chart_at_source_mem_nhds' extChartAt_source_mem_nhds'

theorem extChartAt_source_mem_nhds (x : M) : (extChartAt I x).source ∈ 𝓝 x :=
  extChartAt_source_mem_nhds' I (mem_extChartAt_source I x)
#align ext_chart_at_source_mem_nhds extChartAt_source_mem_nhds

theorem extChartAt_source_mem_nhdsWithin' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    (extChartAt I x).source ∈ 𝓝[s] x' :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds' I h)
#align ext_chart_at_source_mem_nhds_within' extChartAt_source_mem_nhdsWithin'

theorem extChartAt_source_mem_nhdsWithin (x : M) : (extChartAt I x).source ∈ 𝓝[s] x :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds I x)
#align ext_chart_at_source_mem_nhds_within extChartAt_source_mem_nhdsWithin

theorem continuousOn_extChartAt (x : M) : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
  continuousOn_extend _ _
#align continuous_on_ext_chart_at continuousOn_extChartAt

theorem continuousAt_extChartAt' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    ContinuousAt (extChartAt I x) x' :=
  continuousAt_extend _ _ <| by rwa [← extChartAt_source I]
#align continuous_at_ext_chart_at' continuousAt_extChartAt'

theorem continuousAt_extChartAt (x : M) : ContinuousAt (extChartAt I x) x :=
  continuousAt_extChartAt' _ (mem_extChartAt_source I x)
#align continuous_at_ext_chart_at continuousAt_extChartAt

theorem map_extChartAt_nhds' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝 y) = 𝓝[range I] extChartAt I x y :=
  map_extend_nhds _ _ <| by rwa [← extChartAt_source I]
#align map_ext_chart_at_nhds' map_extChartAt_nhds'

theorem map_extChartAt_nhds (x : M) : map (extChartAt I x) (𝓝 x) = 𝓝[range I] extChartAt I x x :=
  map_extChartAt_nhds' I <| mem_extChartAt_source I x
#align map_ext_chart_at_nhds map_extChartAt_nhds

theorem map_extChartAt_nhds_of_boundaryless [I.Boundaryless] (x : M) :
    map (extChartAt I x) (𝓝 x) = 𝓝 (extChartAt I x x) := by
  rw [extChartAt]
  exact map_extend_nhds_of_boundaryless (chartAt H x) I (mem_chart_source H x)

variable {x} in
theorem extChartAt_image_nhd_mem_nhds_of_boundaryless [I.Boundaryless]
    {x : M} (hx : s ∈ 𝓝 x) : extChartAt I x '' s ∈ 𝓝 (extChartAt I x x) := by
  rw [extChartAt]
  exact extend_image_nhd_mem_nhds_of_boundaryless _ I (mem_chart_source H x) hx

theorem extChartAt_target_mem_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    (extChartAt I x).target ∈ 𝓝[range I] extChartAt I x y :=
  extend_target_mem_nhdsWithin _ _ <| by rwa [← extChartAt_source I]
#align ext_chart_at_target_mem_nhds_within' extChartAt_target_mem_nhdsWithin'

theorem extChartAt_target_mem_nhdsWithin (x : M) :
    (extChartAt I x).target ∈ 𝓝[range I] extChartAt I x x :=
  extChartAt_target_mem_nhdsWithin' I (mem_extChartAt_source I x)
#align ext_chart_at_target_mem_nhds_within extChartAt_target_mem_nhdsWithin

/-- If we're boundaryless, `extChartAt` has open target -/
theorem isOpen_extChartAt_target [I.Boundaryless] (x : M) : IsOpen (extChartAt I x).target := by
  simp_rw [extChartAt_target, I.range_eq_univ, inter_univ]
  exact (PartialHomeomorph.open_target _).preimage I.continuous_symm

/-- If we're boundaryless, `(extChartAt I x).target` is a neighborhood of the key point -/
theorem extChartAt_target_mem_nhds [I.Boundaryless] (x : M) :
    (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) := by
  convert extChartAt_target_mem_nhdsWithin I x
  simp only [I.range_eq_univ, nhdsWithin_univ]

/-- If we're boundaryless, `(extChartAt I x).target` is a neighborhood of any of its points -/
theorem extChartAt_target_mem_nhds' [I.Boundaryless] {x : M} {y : E}
    (m : y ∈ (extChartAt I x).target) : (extChartAt I x).target ∈ 𝓝 y :=
  (isOpen_extChartAt_target I x).mem_nhds m

theorem extChartAt_target_subset_range (x : M) : (extChartAt I x).target ⊆ range I := by
  simp only [mfld_simps]
#align ext_chart_at_target_subset_range extChartAt_target_subset_range

theorem nhdsWithin_extChartAt_target_eq' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    𝓝[(extChartAt I x).target] extChartAt I x y = 𝓝[range I] extChartAt I x y :=
  nhdsWithin_extend_target_eq _ _ <| by rwa [← extChartAt_source I]
#align nhds_within_ext_chart_at_target_eq' nhdsWithin_extChartAt_target_eq'

theorem nhdsWithin_extChartAt_target_eq (x : M) :
    𝓝[(extChartAt I x).target] (extChartAt I x) x = 𝓝[range I] (extChartAt I x) x :=
  nhdsWithin_extChartAt_target_eq' I (mem_extChartAt_source I x)
#align nhds_within_ext_chart_at_target_eq nhdsWithin_extChartAt_target_eq

theorem continuousAt_extChartAt_symm'' {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    ContinuousAt (extChartAt I x).symm y :=
  continuousAt_extend_symm' _ _ h
#align continuous_at_ext_chart_at_symm'' continuousAt_extChartAt_symm''

theorem continuousAt_extChartAt_symm' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    ContinuousAt (extChartAt I x).symm (extChartAt I x x') :=
  continuousAt_extChartAt_symm'' I <| (extChartAt I x).map_source h
#align continuous_at_ext_chart_at_symm' continuousAt_extChartAt_symm'

theorem continuousAt_extChartAt_symm (x : M) :
    ContinuousAt (extChartAt I x).symm ((extChartAt I x) x) :=
  continuousAt_extChartAt_symm' I (mem_extChartAt_source I x)
#align continuous_at_ext_chart_at_symm continuousAt_extChartAt_symm

theorem continuousOn_extChartAt_symm (x : M) :
    ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
  fun _y hy => (continuousAt_extChartAt_symm'' _ hy).continuousWithinAt
#align continuous_on_ext_chart_at_symm continuousOn_extChartAt_symm

theorem isOpen_extChartAt_preimage' (x : M) {s : Set E} (hs : IsOpen s) :
    IsOpen ((extChartAt I x).source ∩ extChartAt I x ⁻¹' s) :=
  isOpen_extend_preimage' _ _ hs
#align is_open_ext_chart_at_preimage' isOpen_extChartAt_preimage'

theorem isOpen_extChartAt_preimage (x : M) {s : Set E} (hs : IsOpen s) :
    IsOpen ((chartAt H x).source ∩ extChartAt I x ⁻¹' s) := by
  rw [← extChartAt_source I]
  exact isOpen_extChartAt_preimage' I x hs
#align is_open_ext_chart_at_preimage isOpen_extChartAt_preimage

theorem map_extChartAt_nhdsWithin_eq_image' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) =
      𝓝[extChartAt I x '' ((extChartAt I x).source ∩ s)] extChartAt I x y :=
  map_extend_nhdsWithin_eq_image _ _ <| by rwa [← extChartAt_source I]
#align map_ext_chart_at_nhds_within_eq_image' map_extChartAt_nhdsWithin_eq_image'

theorem map_extChartAt_nhdsWithin_eq_image (x : M) :
    map (extChartAt I x) (𝓝[s] x) =
      𝓝[extChartAt I x '' ((extChartAt I x).source ∩ s)] extChartAt I x x :=
  map_extChartAt_nhdsWithin_eq_image' I (mem_extChartAt_source I x)
#align map_ext_chart_at_nhds_within_eq_image map_extChartAt_nhdsWithin_eq_image

theorem map_extChartAt_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x y :=
  map_extend_nhdsWithin _ _ <| by rwa [← extChartAt_source I]
#align map_ext_chart_at_nhds_within' map_extChartAt_nhdsWithin'

theorem map_extChartAt_nhdsWithin (x : M) :
    map (extChartAt I x) (𝓝[s] x) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x x :=
  map_extChartAt_nhdsWithin' I (mem_extChartAt_source I x)
#align map_ext_chart_at_nhds_within map_extChartAt_nhdsWithin

theorem map_extChartAt_symm_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x y) =
      𝓝[s] y :=
  map_extend_symm_nhdsWithin _ _ <| by rwa [← extChartAt_source I]
#align map_ext_chart_at_symm_nhds_within' map_extChartAt_symm_nhdsWithin'

theorem map_extChartAt_symm_nhdsWithin_range' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x y) = 𝓝 y :=
  map_extend_symm_nhdsWithin_range _ _ <| by rwa [← extChartAt_source I]
#align map_ext_chart_at_symm_nhds_within_range' map_extChartAt_symm_nhdsWithin_range'

theorem map_extChartAt_symm_nhdsWithin (x : M) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x x) =
      𝓝[s] x :=
  map_extChartAt_symm_nhdsWithin' I (mem_extChartAt_source I x)
#align map_ext_chart_at_symm_nhds_within map_extChartAt_symm_nhdsWithin

theorem map_extChartAt_symm_nhdsWithin_range (x : M) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x x) = 𝓝 x :=
  map_extChartAt_symm_nhdsWithin_range' I (mem_extChartAt_source I x)
#align map_ext_chart_at_symm_nhds_within_range map_extChartAt_symm_nhdsWithin_range

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
theorem extChartAt_preimage_mem_nhdsWithin' {x x' : M} (h : x' ∈ (extChartAt I x).source)
    (ht : t ∈ 𝓝[s] x') :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x' := by
  rwa [← map_extChartAt_symm_nhdsWithin' I h, mem_map] at ht
#align ext_chart_at_preimage_mem_nhds_within' extChartAt_preimage_mem_nhdsWithin'

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
theorem extChartAt_preimage_mem_nhdsWithin {x : M} (ht : t ∈ 𝓝[s] x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
  extChartAt_preimage_mem_nhdsWithin' I (mem_extChartAt_source I x) ht
#align ext_chart_at_preimage_mem_nhds_within extChartAt_preimage_mem_nhdsWithin

theorem extChartAt_preimage_mem_nhds' {x x' : M} (h : x' ∈ (extChartAt I x).source)
    (ht : t ∈ 𝓝 x') : (extChartAt I x).symm ⁻¹' t ∈ 𝓝 (extChartAt I x x') :=
  extend_preimage_mem_nhds _ _ (by rwa [← extChartAt_source I]) ht
#align ext_chart_at_preimage_mem_nhds' extChartAt_preimage_mem_nhds'

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
theorem extChartAt_preimage_mem_nhds {x : M} (ht : t ∈ 𝓝 x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝 ((extChartAt I x) x) := by
  apply (continuousAt_extChartAt_symm I x).preimage_mem_nhds
  rwa [(extChartAt I x).left_inv (mem_extChartAt_source _ _)]
#align ext_chart_at_preimage_mem_nhds extChartAt_preimage_mem_nhds

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
theorem extChartAt_preimage_inter_eq (x : M) :
    (extChartAt I x).symm ⁻¹' (s ∩ t) ∩ range I =
      (extChartAt I x).symm ⁻¹' s ∩ range I ∩ (extChartAt I x).symm ⁻¹' t := by
  mfld_set_tac
#align ext_chart_at_preimage_inter_eq extChartAt_preimage_inter_eq

theorem ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range
    {f : M → M'} {x : M} (hc : ContinuousWithinAt f s x) :
    𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x x) =
      𝓝[(extChartAt I x).target ∩
        (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source)] (extChartAt I x x) := by
  rw [← (extChartAt I x).image_source_inter_eq', ← map_extChartAt_nhdsWithin_eq_image,
    ← map_extChartAt_nhdsWithin, nhdsWithin_inter_of_mem']
  exact hc (extChartAt_source_mem_nhds _ _)

/-! We use the name `ext_coord_change` for `(extChartAt I x').symm ≫ extChartAt I x`. -/

theorem ext_coord_change_source (x x' : M) :
    ((extChartAt I x').symm ≫ extChartAt I x).source =
      I '' ((chartAt H x').symm ≫ₕ chartAt H x).source :=
  extend_coord_change_source _ _ _
#align ext_coord_change_source ext_coord_change_source

open SmoothManifoldWithCorners

theorem contDiffOn_ext_coord_change [SmoothManifoldWithCorners I M] (x x' : M) :
    ContDiffOn 𝕜 ⊤ (extChartAt I x ∘ (extChartAt I x').symm)
      ((extChartAt I x').symm ≫ extChartAt I x).source :=
  contDiffOn_extend_coord_change I (chart_mem_maximalAtlas I x) (chart_mem_maximalAtlas I x')
#align cont_diff_on_ext_coord_change contDiffOn_ext_coord_change

theorem contDiffWithinAt_ext_coord_change [SmoothManifoldWithCorners I M] (x x' : M) {y : E}
    (hy : y ∈ ((extChartAt I x').symm ≫ extChartAt I x).source) :
    ContDiffWithinAt 𝕜 ⊤ (extChartAt I x ∘ (extChartAt I x').symm) (range I) y :=
  contDiffWithinAt_extend_coord_change I (chart_mem_maximalAtlas I x) (chart_mem_maximalAtlas I x')
    hy
#align cont_diff_within_at_ext_coord_change contDiffWithinAt_ext_coord_change

/-- Conjugating a function to write it in the preferred charts around `x`.
The manifold derivative of `f` will just be the derivative of this conjugated function. -/
@[simp, mfld_simps]
def writtenInExtChartAt (x : M) (f : M → M') : E → E' :=
  extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm
#align written_in_ext_chart_at writtenInExtChartAt

theorem writtenInExtChartAt_chartAt {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I I x (chartAt H x) y = y := by simp_all only [mfld_simps]

theorem writtenInExtChartAt_chartAt_symm {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I I (chartAt H x x) (chartAt H x).symm y = y := by
  simp_all only [mfld_simps]

theorem writtenInExtChartAt_extChartAt {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I 𝓘(𝕜, E) x (extChartAt I x) y = y := by
  simp_all only [mfld_simps]

theorem writtenInExtChartAt_extChartAt_symm {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt 𝓘(𝕜, E) I (extChartAt I x x) (extChartAt I x).symm y = y := by
  simp_all only [mfld_simps]

variable (𝕜)

theorem extChartAt_self_eq {x : H} : ⇑(extChartAt I x) = I :=
  rfl
#align ext_chart_at_self_eq extChartAt_self_eq

theorem extChartAt_self_apply {x y : H} : extChartAt I x y = I y :=
  rfl
#align ext_chart_at_self_apply extChartAt_self_apply

/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity. -/
theorem extChartAt_model_space_eq_id (x : E) : extChartAt 𝓘(𝕜, E) x = PartialEquiv.refl E := by
  simp only [mfld_simps]
#align ext_chart_at_model_space_eq_id extChartAt_model_space_eq_id

theorem ext_chart_model_space_apply {x y : E} : extChartAt 𝓘(𝕜, E) x y = y :=
  rfl
#align ext_chart_model_space_apply ext_chart_model_space_apply

variable {𝕜}

theorem extChartAt_prod (x : M × M') :
    extChartAt (I.prod I') x = (extChartAt I x.1).prod (extChartAt I' x.2) := by
  simp only [mfld_simps]
  -- Porting note: `simp` can't use `PartialEquiv.prod_trans` here because of a type
  -- synonym
  rw [PartialEquiv.prod_trans]
#align ext_chart_at_prod extChartAt_prod

theorem extChartAt_comp [ChartedSpace H H'] (x : M') :
    (letI := ChartedSpace.comp H H' M'; extChartAt I x) =
      (chartAt H' x).toPartialEquiv ≫ extChartAt I (chartAt H' x x) :=
  PartialEquiv.trans_assoc ..

theorem writtenInExtChartAt_chartAt_comp [ChartedSpace H H'] (x : M') {y}
    (hy : y ∈ letI := ChartedSpace.comp H H' M'; (extChartAt I x).target) :
    (letI := ChartedSpace.comp H H' M'; writtenInExtChartAt I I x (chartAt H' x) y) = y := by
  letI := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

theorem writtenInExtChartAt_chartAt_symm_comp [ChartedSpace H H'] (x : M') {y}
    (hy : y ∈ letI := ChartedSpace.comp H H' M'; (extChartAt I x).target) :
    ( letI := ChartedSpace.comp H H' M'
      writtenInExtChartAt I I (chartAt H' x x) (chartAt H' x).symm y) = y := by
  letI := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

end ExtendedCharts

section Topology
-- Let `M` be a topological manifold over the field 𝕜.
variable
  {E : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [HasGroupoid M (contDiffGroupoid 0 I)]

/-- A finite-dimensional manifold modelled on a locally compact field
  (such as ℝ, ℂ or the `p`-adic numbers) is locally compact. -/
lemma Manifold.locallyCompact_of_finiteDimensional [LocallyCompactSpace 𝕜]
    [FiniteDimensional 𝕜 E] : LocallyCompactSpace M := by
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  have : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

end Topology
