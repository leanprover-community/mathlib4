/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Instances.Real

/-!
## (Unoriented) bordism theory

This file defines the beginnings of unoriented bordism theory. We define singular manifolds,
the building blocks of unoriented bordism groups. Future pull requests will define bordisms
and the bordism groups of a topological space, and prove these are abelian groups.

The basic notion of bordism theory is that of a bordism between smooth manifolds.
Two compact smooth `n`-dimensional manifolds `M` and `N` are **bordant** if there exists a smooth
**bordism** between them: this is a compact `n+1`-dimensional manifold `W` whose boundary is
(diffeomorphic to) the disjoint union `M ⊕ N`. Being bordant is an equivalence relation
(transitivity follows from the collar neighbourhood theorem). The set of equivalence classes has an
abelian group structure, with the group operation given as disjoint union of manifolds,
and is called the `n`-th (unoriented) bordism group.

This construction can be generalised one step further, to produce an extraordinary homology theory.
Given a topological space `X`, a **singular manifold** on `X` is a closed smooth manifold `M`
together with a continuous map `M → F`. (The word *singular* does not refer to singularities,
but is by analogy to singular chains in the definition of singular homology.)

Given two `n`-dimensional singular manifolds `s` and `t`, an (oriented) bordism between `s` and `t`
is a compact smooth `n+1`-dimensional manifold `W` whose boundary is (diffeomorphic to) the disjoint
union of `s` and `t`, together with a map `W → X` which restricts to the maps on `s` and `t`.
We call `s` and `t` bordant if there exists a bordism between them: again, this defines an
equivalence relation. The `n`-th bordism group of `X` is the set of bordism classes of
`n`-dimensional singular manifolds on `X`. If `X` is a single point, this recovers the bordism
groups from the preceding paragraph.

These absolute bordism groups can be generalised further to relative bordism groups, for each
topological pair `(X, A)`; in fact, these define an extra-ordinary homology theory.

## Main definitions

- **SingularManifold X k I**: a singular manifold on a topological space `X`, is a pair `(M, f)` of
  a closed `C^k`-manifold `M` modelled on `I` together with a continuous map `M → X`.
  We don't assume `M` to be modelled on `ℝⁿ`, but add the model topological space `H`,
  the vector space `E` and the model with corners `I` as type parameters.
  If we wish to emphasize the model, with will speak of a singular `I`-manifold.
  To define a disjoint unions of singular manifolds, we require their domains to be manifolds
  over the same model with corners: this is why we make the model explicit.

## Main results

- `SingularManifold.map`: a map `X → Y` of topological spaces induces a map between the spaces
  of singular manifolds. This will be used to define functoriality of bordism groups.
- `SingularManifold.comap`: if `(N, f)` is a singular manifold on `X`
  and `φ : M → N` is continuous, the `comap` of `(N, f)` and `φ`
  is the induced singular manifold `(M, f ∘ φ)` on `X`.
- `SingularManifold.empty`: the empty set `M`, viewed as a manifold,
  as a singular manifold over any space `X`.
- `SingularManifold.toPUnit`: a smooth manifold induces a singular manifold on the one-point space.
- `SingularManifold.prod`: the product of a singular `I`-manifold and a singular `J`-manifold
  on the one-point space, is a singular `I.prod J`-manifold on the one-point space.
- `SingularManifold.sum`: the disjoint union of two singular `I`-manifolds
  is a singular `I`-manifold.

## Implementation notes

* We choose a bundled design for singular manifolds (and also for bordisms): to construct the
  group structure on the set of bordism classes, having that be a type is useful.
* The underlying model with corners is a type parameter, as defining a disjoint union of singular
  manifolds requires their domains to be manifolds over the same model with corners.
  Thus, either we restrict to manifolds modelled over `𝓡n` (which we prefer not to),
  or the model must be a type parameter.
* Having `SingularManifold` contain the type `M` as explicit structure field is not ideal,
  as this adds a universe parameter to the structure. However, this is the best solution we found:
  we generally cannot have `M` live in the same universe as `X` (a common case is `X` being
  `PUnit`), and determining the universe of `M` from the universes of `E` and `H` would make
  `SingularManifold.map` painful to state (as that would require `ULift`ing `M`).

## TODO
- define bordisms and prove basic constructions (e.g. reflexivity, symmetry, transitivity)
  and operations (e.g. disjoint union, sum with the empty set)
- define the bordism relation and prove it is an equivalence relation
- define the unoriented bordism group (the set of bordism classes) and prove it is an abelian group
- for bordisms on a one-point space, define multiplication and prove the bordism ring structure
- define relative bordism groups (generalising the previous three points)
- prove that relative unoriented bordism groups define an extraordinary homology theory

## Tags

singular manifold, bordism, bordism group
-/

open scoped Manifold
open Module Set

suppress_compilation

/-- A **singular manifold** on a topological space `X` is a pair `(M, f)` of a closed
`C^k`-manifold `M` modelled on `I` together with a continuous map `M → X`.
If we wish to emphasize the model, with will speak of a singular `I`-manifold.

In practice, one commonly wants to take `k=∞` (as then e.g. the intersection form is a powerful tool
to compute bordism groups; for the definition, this makes no difference.)

This is parametrised on the universe `M` lives in; ensure `u` is the first universe argument. -/
structure SingularManifold.{u} (X : Type*) [TopologicalSpace X] (k : WithTop ℕ∞)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) where
  /-- The manifold `M` of a singular `n`-manifold `(M, f)` -/
  M : Type u
  /-- The manifold `M` is a topological space. -/
  [topSpaceM : TopologicalSpace M]
  /-- The manifold `M` is a charted space over `H`. -/
  [chartedSpace : ChartedSpace H M]
  /-- `M` is a `C^k` manifold. -/
  [isManifold : IsManifold I k M]
  [compactSpace : CompactSpace M]
  [boundaryless : BoundarylessManifold I M]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M, f)` on `X` -/
  f : M → X
  hf : Continuous f

namespace SingularManifold

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {k : WithTop ℕ∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I k M] [CompactSpace M] [BoundarylessManifold I M]

instance {s : SingularManifold X k I} : TopologicalSpace s.M := s.topSpaceM

instance {s : SingularManifold X k I} : ChartedSpace H s.M := s.chartedSpace

instance {s : SingularManifold X k I} : IsManifold I k s.M := s.isManifold

instance {s : SingularManifold X k I} : CompactSpace s.M := s.compactSpace

instance {s : SingularManifold X k I} : BoundarylessManifold I s.M := s.boundaryless

/-- A map of topological spaces induces a corresponding map of singular manifolds. -/
-- This is part of proving functoriality of the bordism groups.
def map.{u} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} (s : SingularManifold.{u} X k I)
    {φ : X → Y} (hφ : Continuous φ) : SingularManifold.{u} Y k I where
  M := s.M
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp, mfld_simps]
lemma map_f (s : SingularManifold X k I) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f :=
  rfl

@[simp, mfld_simps]
lemma map_M (s : SingularManifold X k I) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).M = s.M :=
  rfl

lemma map_comp (s : SingularManifold X k I)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ((s.map hφ).map hψ).f = (ψ ∘ φ) ∘ s.f := by
  simp [Function.comp_def]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']

variable (M I) in
/-- If `M` is a closed `C^k` manifold, it is a singular manifold over itself. -/
noncomputable def refl : SingularManifold M k I where
  M := M
  f := id
  hf := continuous_id

/-- If `(N, f)` is a singular manifold on `X` and `M` another `C^k` manifold,
a continuous map `φ : M → N` induces a singular manifold structure `(M, f ∘ φ)` on `X`. -/
noncomputable def comap (s : SingularManifold X k I)
    {φ : M → s.M} (hφ : Continuous φ) : SingularManifold X k I where
  M := M
  f := s.f ∘ φ
  hf := s.hf.comp hφ

@[simp, mfld_simps]
lemma comap_M (s : SingularManifold X k I) {φ : M → s.M} (hφ : Continuous φ) :
    (s.comap hφ).M = M := rfl

@[simp, mfld_simps]
lemma comap_f (s : SingularManifold X k I) {φ : M → s.M} (hφ : Continuous φ) :
    (s.comap hφ).f = s.f ∘ φ :=
  rfl

variable (X) in
/-- The canonical singular manifold associated to the empty set (seen as a smooth manifold) -/
def empty.{u} (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I k M] [IsEmpty M] : SingularManifold X k I where
  M := M
  f x := (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim

omit [CompactSpace M] [BoundarylessManifold I M] in
@[simp, mfld_simps]
lemma empty_M [IsEmpty M] : (empty X M I (k := k)).M = M := rfl

instance [IsEmpty M] : IsEmpty (SingularManifold.empty X M I (k := k)).M := by
  unfold SingularManifold.empty
  infer_instance

variable (M I) in
/-- A smooth manifold induces a singular manifold on the one-point space. -/
def toPUnit : SingularManifold PUnit k I where
  M := M
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

variable {I' : ModelWithCorners ℝ E' H'} [FiniteDimensional ℝ E']

/--
The product of a singular `I`- and a singular `J`-manifold into a one-point space
is a singular `I.prod J`-manifold.
This construction is used to prove that the bordism group of `PUnit` is a graded commutative ring.

NB. This definition as written makes sense more generally, for `SingularManifold X k I` whenever `X`
is a topological (additive) group. However, this would not be the correct definition if `X` is not
`(P)Unit`: the bordism ring can be defined for every `C^k` manifold `X`, but the product of two
singular manifolds `(M, f)` and `(N, g)` is the fibre product of `M` and `N` w.r.t. `f` and `g`,
with its induced map into `X`.
(If `f` and `g` intersect transversely, this fibre product is a smooth manifold, of dimension
`dim M + dim N - dim X`. Otherwise, the transversality theorem proves that `f` (or `g`) admits an
arbitrarily small perturbation `f'` so `f'` and `g` are transverse. One can prove that different
perturbations yield bordant manifolds.)
-/
def prod (s : SingularManifold PUnit k I) (t : SingularManifold PUnit k I') :
    SingularManifold PUnit k (I.prod I') where
  M := s.M × t.M
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

variable (s t : SingularManifold X k I)

/-- The disjoint union of two singular `I`-manifolds on `X` is a singular `I`-manifold on `X`. -/
def sum (s t : SingularManifold X k I) : SingularManifold X k I where
  M := s.M ⊕ t.M
  f := Sum.elim s.f t.f
  hf := s.hf.sumElim t.hf

@[simp, mfld_simps]
lemma sum_M (s t : SingularManifold X k I) : (s.sum t).M = (s.M ⊕ t.M) := rfl

@[simp, mfld_simps]
lemma sum_f (s t : SingularManifold X k I) : (s.sum t).f = Sum.elim s.f t.f := rfl

end SingularManifold
