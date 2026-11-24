import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial

/-!
# Differential geometry cheat sheet

How do I say certain basic things in Lean?
For each of them, include a variable block. Can verso do this already?
-/

open Set

open scoped ContDiff -- needed for ∞ and ω notation for smooth and analytic

open scoped Manifold -- needed for the 𝓘 notation for `modelWithCornersSelf`

open scoped Topology -- needed for the 𝓝 notation for `nhds`

/-! ## Manifolds -/

section -- Let M be a C^k manifold where k could be ∞ or ω.

variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {k : WithTop ℕ∞}
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I k M]

end

section -- Let M be a C^k *real* manifold.

variable {E M H : Type*} {k : WithTop ℕ∞} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I k M]

-- TODO: explain what each piece means.
end

/-! ## Tangent space -/

section

universe u v w t
variable
  -- Given a non-trivially normed field 𝕜
  {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  -- A manifold M over 𝕜
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type t} [TopologicalSpace M] [ChartedSpace H M]
  -- A point in M
  (x : M)

-- a Type (in the same universe as `E` because it is secretly `E` itself)
#check TangentSpace I x
#check TangentSpace% x -- FIXME: we miss a delaborator here!

/-
It is a topological vector space over `𝕜` but, crucially, it does not inherit any norm from `E`,
leaving room for a potential Riemannian norm for instance.
-/
#synth Module 𝕜 (TangentSpace% x)
#synth IsTopologicalAddGroup (TangentSpace% x)
#synth ContinuousSMul 𝕜 (TangentSpace% x)


/-
The tangent space is a dependent type, so `TangentSpace% x = TangentSpace% y` only when `x` is
*definitionally* equal to `y`. Otherwise, one need to explictly use an isomorphism. Due to
implementation details, this isomorphism doesn’t actually asks for an equality proof, but
its value when `x ≠ y` should be considered a junk value.
-/
variable (y : M) in
#check (tangentSpaceCast I x y : TangentSpace% x ≃L[𝕜] TangentSpace% y)

/-
The various tangent spaces fit together into the total space `TangentBundle I M`
-/
#check TangentBundle I M  --FIXME don’t we have an elaborator for this?


/-
In the special case of a vector space `E`, each tangent bundle is canonically isomorphic to `E`.
The current implementation actually makes this a definitional equality, but using it is a defeq
abuse that leads to all sorts of issues.
-/

variable (e : E)
example : TangentSpace% e = E := rfl -- this should not be relied on

#check (NormedSpace.fromTangentSpace e : TangentSpace% e ≃L[𝕜] E) -- this is good
end

/-! ## Differentiability of functions between manifolds -/

section

variable
  -- Given a non-trivially normed field 𝕜
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- A manifold M over 𝕜
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- A manifold M' over 𝕜
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- A function from M to M' and x in M
  (f : M → M') (x : M) (s : Set M)

section


/-
As in calculus between vector spaces, the primary notation is “f has derivative F at x”.
-/

variable (F : TangentSpace I x →L[𝕜] TangentSpace I' (f x))

-- Version within a set `s`
#check HasMFDerivWithinAt I I' f s x F -- or `HasMFDerivAt[s] f x F`

#check HasMFDerivAt I I' f x F -- or `HasMFDerivAt% f x F`

/-

In those names, “M” stands for manifold and “F” for Fréchet.

Important note: the definition of `HasMFDeriv I I' f x F` does not assume the source and target
manifolds are C^1.
This is possible because the `ChartedSpace` structure carries a prefered chart for each
point. But this is a junk value without assumptions `[IsManifold I 1 M]` and `[IsManifold I' 1 M']`.
So one can expect lemmas that don’t apply without those assumptions.

Patrick wonders whether we should have a linter warning us when a statement mentions
`MDiffAt` or its friends without such assumptions. The linter could shut up after a proof is
completed.
-/

/-!
### Links:
-/

-- The absolute version is stronger than the relative one
example (h : HasMFDerivAt% f x F) : HasMFDerivAt[s] f x F := h.hasMFDerivWithinAt

-- The converse holds for interior points
example (h : HasMFDerivAt[s] f x F) (hxs : s ∈ 𝓝 x) : HasMFDerivAt% f x F := h.hasMFDerivAt hxs

-- When the source and targets are vector spaces, we get back the elementary notion

example (f : E → E') (F : E →L[𝕜] E') (e : E) : HasMFDerivAt% f e F ↔ HasFDerivAt f F e :=
  hasMFDerivAt_iff_hasFDerivAt

/-!
### Congruence

Since differential geometry is full of partially defined functions (coming from charts and local
trivialization), it is crucial that congruence lemmas only assume local equality.
Note that getting a type-correct statement then requires using `tangentSpaceCast` (coerced from
continuous linear equivalence to continuous linear map).
-/

example (g : M → M') (hfg : g =ᶠ[𝓝 x] f) (hf : HasMFDerivAt% f x F) :
    HasMFDerivAt% g x
    ((tangentSpaceCast I' (f x) (g x) : TangentSpace% (f x) →L[𝕜] TangentSpace% (g x)) ∘L F) :=
  hf.congr_of_eventuallyEq hfg
end

section

-- `f` is differentiable at `x` within `s`
#check MDifferentiableWithinAt I I' f s x -- or `MDiffAt[s] f x`

-- `f` is differentiable on `s`
#check MDifferentiableOn I I' f s  -- or `MDiff[s] f`

-- `f` is differentiable at `x`
#check MDifferentiableAt I I' f x -- or `MDiffAt f x`

-- `f` is differentiable everywhere
#check MDifferentiable I I' f -- or `MDiff f`

-- the derivative of `f` at `x`
#check mfderiv I I' f x -- or `mfderiv% f x`

-- One can also bundle all `mfderiv` at various points to get a map from the
-- tangent bundle of `M` to the tangent bundle of `M'`:
#check (tangentMap I I' f : TangentBundle I M → TangentBundle I' M')

/-
Important note: the definition of `MDiffAt I I'` does not assume the source and target manifolds
are C^1. See the note about `HasMFDeriv`.
-/

/-! ### Links: -/

-- The absolute version is stronger than the relative one
example (h : MDiffAt f x) : MDiffAt[s] f x := h.mdifferentiableWithinAt

-- The converse holds for interior points
example (h : MDiffAt[s] f x) (hxs : s ∈ 𝓝 x) : MDiffAt f x := h.mdifferentiableAt hxs

example : MDiff[s] f ↔ ∀ x ∈ s, MDiffAt[s] f x := Iff.rfl

example : MDiffAt f x ↔ MDiffAt[univ] f x := Iff.rfl

example : MDiff f ↔ ∀ x, MDiffAt f x := Iff.rfl

/-
When the target is a vector space `E'`, one can post-compose `mfderiv` by
`NormedSpace.fromTangentSpace` to get a linear map langing into `E'`.
This is very common on paper when `E'` is the base field.
-/

open NormedSpace in
example (g : M → E') :
    mvfderiv I g x = (fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv% g x) := rfl

/-
The “v” in `mvfderiv` stands for “vector”. This can also be spelled `d% g x`, which is the usual
notation when `E' = 𝕜`.
-/

/-! ### Congruence

Again, the abundance of partially defined functions makes the following local congruence lemma
crucial.
-/

example (f g : M → M') (hfg : g =ᶠ[𝓝 x] f) (hf : MDiffAt f x) : MDiffAt g x :=
  hf.congr_of_eventuallyEq hfg

-- The version within a set `x` requires the extra assumption `g x = f x` in case `x` is not in `s`…
example (f g : M → M') (hfg : g =ᶠ[𝓝[s] x] f) (hgfx : g x = f x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] g x :=
  hf.congr_of_eventuallyEq hfg hgfx

/-
Again, when stating the corresponding equality of derivatives,
getting a type-correct statement then requires using `tangentSpaceCast` (coerced from
continuous linear equivalence to continuous linear map).

TODO: understand why the elaborator doesn’t need help to insert the coercion here, but needs helps
above.
-/
example (f g : M → M') (hfg : g =ᶠ[𝓝 x] f) :
    mfderiv% g x = (tangentSpaceCast I' (f x) (g x)) ∘L mfderiv% f x  :=
  hfg.mfderiv_eq

/-! ### Composition: -/

variable
  -- A manifold M'' over 𝕜
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] (I'' : ModelWithCorners 𝕜 E'' H'')
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  (g : M' → M'')

-- Note how elaboration often needs help to understand what is `x` (why??), so it is an explicit
-- argument.
example (hf : MDiffAt f x) (hg : MDiffAt g (f x)) : MDiffAt (g ∘ f) x :=
  hg.comp x hf

example (hf : MDiffAt f x) (hg : MDiffAt g (f x)) :
    mfderiv% (g ∘ f) x = mfderiv% g (f x) ∘L (mfderiv% f x) :=
  mfderiv_comp x hg  hf


-- The following “generalizations” are mathematically empty, but technically convenient when
-- `f x = y` is not definitional
example (hf : MDiffAt f x) {y : M'} (hy : f x = y) (hg : MDiffAt g y) : MDiffAt (g ∘ f) x :=
  hg.comp_of_eq x hf hy

example (hf : MDiffAt f x) {y : M'} (hy : f x = y) (hg : MDiffAt g y) :
    mfderiv% (g ∘ f) x = mfderiv% g (f x) ∘L (mfderiv% f x) :=
  mfderiv_comp_of_eq hg hf hy

end

/-! ## Continuously differentiable maps

We now consider maps with class C^n.

TODO: check we don’t have a definition saying n times differentiable without being n times
*continuously* differentiable.
-/
section
variable (n : WithTop ℕ∞) -- regularity parameter, including ∞ and ω, with notation in `ContDiff`

-- `f` is `n` times continuously differentiable at `x`
#check ContMDiffAt I I' n f x -- or `CMDiffAt n f x`

-- `f` is `n` times continuously differentiable at `x` within `s`
#check ContMDiffWithinAt I I' n f s x -- or `CMDiffAt[s] n f`

-- `f` is `n` times continuously differentiable on `s`
#check ContMDiffOn I I' n f s -- or `CMDiff[s] n f`

-- `f` is `n` times continuously differentiable everywhere
#check ContMDiff I I' n f -- or `CMDiff n f`

-- FIXME: It seems we don’t have a delaborator for all those!

/-
Important note: the definition of `ContMDiff I I' n` does not assume the source and target
manifolds are C^n. See the corresponding note about `MDifferentiableAt I I' n` .

The pointwise version `ContMDiffAt` and  `ContMDiffWithinAt` are a bit tricky
because of course iterated derivatives at `x` require differentiability near `x`.
However this “near x” can depend on the order of differentiation, which matters when `n`
is `∞` (but not when `n` is `ω` because in that case we require a neighborhood that works for the
whole power series). Note also the assumptions that `M` and `M'` are of class C^n, without which
this would be a junk claim anyway.
-/

example [IsManifold I n M] [IsManifold I' n M']
    (h : CMDiffAt n f x) (hn : n ≠ ∞) : ∀ᶠ x' in 𝓝 x, CMDiffAt n f x' :=
  (contMDiffAt_iff_contMDiffAt_nhds hn).mp h

-- The absolute version is stronger than the relative one
example (h : CMDiffAt n f x) : CMDiffAt[s] n f x := h.contMDiffWithinAt

-- The converse holds for interior points
example (h : CMDiffAt[s] n f x) (hxs : s ∈ 𝓝 x) : CMDiffAt n f x := h.contMDiffAt hxs

example : CMDiff[s] n f ↔ ∀ x ∈ s, CMDiffAt[s] n f x := Iff.rfl

example : CMDiffAt n f x ↔ CMDiffAt[univ] n f x := Iff.rfl

example : CMDiff n f ↔ ∀ x, CMDiffAt n f x := Iff.rfl

-- All those conditions are antitone in `n`, and the corresponding lemma is always called `of_le`,
-- in the relvant namespace. For instance:

-- `n ↦ CMDiffAt[s] n` in antitone
example (h : CMDiffAt[s] n f x) {n' : WithTop ℕ∞} (hnn' : n' ≤ n) : CMDiffAt[s] n' f x :=
  h.of_le hnn'

-- `n ↦ CMDiffAt n` in antitone
example (h : CMDiffAt n f x) {n' : WithTop ℕ∞} (hnn' : n' ≤ n) : CMDiffAt n' f x :=
  h.of_le hnn'

-- They also propagate to `tangentMap` with the corresponding regularity. The following is that
-- global version. Other versions are a bit more tricky to state (and versions within a set `s`
-- exclude the junk case where function don’t have unique derivatives on `s`). Some versions seem to
-- be missing as well. Explore around the lemma quoted below for more information.

example [IsManifold I 1 M] [IsManifold I' 1 M']
    (h : CMDiff n f) {n' : WithTop ℕ∞} (hnn' : n' + 1 ≤ n) : CMDiff n' (tangentMap% f) :=
  h.contMDiff_tangentMap hnn'

-- There is a corresponding family of statements for `mvfderiv` where the target is a vector space,
-- except we only have some of them, as can be seen in the proof below.
-- FIXME: it seems `T% (d% g)` doesn’t work
-- FIXME: `CMDiff` elaborator fails in the statement below
-- FIXME: the shape of the next lemma is inconsistent with the above one
-- FIXME: we really need to find a way to get rid of those multiple `IsManifold I ? M` assumptions.

-- Note the conditions on `𝕜` and `E` below
open Bundle TotalSpace in
example [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [IsManifold I 1 M] [IsManifold I (n + 1) M]
    {g : M → E'} (h : CMDiff (n + 1) g)
    : ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E')) n (fun x ↦ mk' (E →L[𝕜] E') x (d% g x)) :=
  fun x ↦ (h x).mvfderiv'

-- All those conditions imply the corresponding continuity condition. For instance:

example (h : CMDiff n f) : Continuous f := h.continuous

example (h : CMDiffAt n f x) : ContinuousAt f x := h.continuousAt

-- And they imply differentiability if `n ≠ 0`. For instance:

example (h : CMDiff n f) (hnn' : n ≠ 0) : MDiff f :=
  h.mdifferentiable hnn'

example (h : CMDiff[s] n f) (hnn' : n ≠ 0) : MDiff[s] f :=
  h.mdifferentiableOn hnn'

-- When the source and targets are vector spaces, we get back the elementary notions. For instance:

example (f : E → E') (u : Set E) (e : E) : CMDiffAt[u] n f e ↔ ContDiffWithinAt 𝕜 n f u e :=
  contMDiffWithinAt_iff_contDiffWithinAt

example (g : E → E') (e : E) : CMDiffAt n g e ↔ ContDiffAt 𝕜 n g e :=
  contMDiffAt_iff_contDiffAt

end
end

/-! ## More stuff to be written

Consider the product manifold M \times N.


Let \phi be the preferred chart at x\in M.

Let \phi be any (compatible) chart on M.

--------

Let E\to M be a topological vector bundle.

Let E\to M be a smooth vector bundle.

Let s be a section of E.

variable (s : Π x : M, V x)

Let X be a vector field on `M`

(X : Π x : M, TangentSpace I x)


Let s be a C^k section of E. / The section s of E is C^k.

ContMDiff I (I.prod 𝓘(𝕜, F)) (k + 1) (fun x ↦ TotalSpace.mk' F x (σ x))


Let `X` be a C^k vector field on M.

variable {X : Π x : M, TangentSpace I x}
-- TODO: this doesn't work!
-- variable (___hX: ContMDiff I I.tangent 2 (fun x ↦ (X x : TangentBundle I M)))


Let \phi be the preferred local trivialisation at x\in E.
Let \phi be any compatible trivialisation on M.

Consider the tangent bundle TM of M.

Let X be a C^k vector field on M.

explain TotalSpace.mk' somewhere in here...


-- Let `cov` be a covariant derivative on `V`.



**Basic API lemmas**
- testing smoothness of a map in charts: the standard charts; any charts

- testing smoothness of a section in trivialisations: the standard charts; any charts


**constructions**
- product manifold (tricky!)
- disjoint union

- product bundle (how difficult?)
- Lie bracket of vector fields
-/
