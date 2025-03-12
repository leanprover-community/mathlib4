/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.TangentConeDef
import Mathlib.Logic.Equiv.PartialEquiv

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

open Topology Set Filter Function

noncomputable section

assert_not_exists NormedSpace


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
structure ModelWithCorners (𝕜 : Type*) [NormedField 𝕜] (E : Type*)
    [SeminormedAddCommGroup E] [Module 𝕜 E] (H : Type*) [TopologicalSpace H] extends
    PartialEquiv H E where
  source_eq : source = univ
  uniqueDiffOn' : toPartialEquiv.target = univ ∨ UniqueDiffOn 𝕜 toPartialEquiv.target
  target_subset_closure_interior : toPartialEquiv.target ⊆ closure (interior toPartialEquiv.target)
  continuous_toFun : Continuous toFun := by continuity
  continuous_invFun : Continuous invFun := by continuity

attribute [simp, mfld_simps] ModelWithCorners.source_eq

/-- A topological vector space is a model with corners, using the identity. Do *not* use this one,
but instead the one provided in the definition of normed space, called `modelWithCornersSelf` and
which enjoys better defeq properties. -/
def modelWithCornersSelfId (𝕜 : Type*) [NormedField 𝕜] (E : Type*)
    [SeminormedAddCommGroup E] [Module 𝕜 E] : ModelWithCorners 𝕜 E E where
  toPartialEquiv := PartialEquiv.refl E
  source_eq := rfl
  uniqueDiffOn' := by simp
  target_subset_closure_interior := by simp
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id


section

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [Module 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)

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
def Simps.apply (𝕜 : Type*) [NormedField 𝕜] (E : Type*) [SeminormedAddCommGroup E]
    [Module 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : H → E :=
  I

/-- See Note [custom simps projection] -/
def Simps.symm_apply (𝕜 : Type*) [NormedField 𝕜] (E : Type*) [SeminormedAddCommGroup E]
    [Module 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : E → H :=
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

@[simp, mfld_simps]
theorem target_eq : I.target = range (I : H → E) := by
  rw [← image_univ, ← I.source_eq]
  exact I.image_source_eq_target.symm

theorem range_subset_closure_interior : range I ⊆ closure (interior (range I)) := by
  rw [← I.target_eq]
  exact I.target_subset_closure_interior

end ModelWithCorners

end
