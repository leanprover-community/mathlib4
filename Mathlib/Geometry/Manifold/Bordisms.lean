/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Instances.Real

/-!
## (Unoriented) bordism theory

This file defines the beginnings of (unoriented) bordism theory. For the full definition of
smooth oriented bordism groups, a number of prerequisites are missing from mathlib. However,
a significant amount of this work is already possible.

Currently, this file only contains the definition of *singular *n*-manifolds*:
bordism classes are the equivalence classes of singular n-manifolds w.r.t. the (co)bordism relation
and will be added in a future PR, as well as the definition of the (unoriented) bordism groups.

## Main definitions

- **SingularNManifold**: a singular `n`-manifold on a topological space `X`, for `n ∈ ℕ`, is a pair
`(M, f)` of a closed `n`-dimensional smooth manifold `M` together with a continuous map `M → X`.
We don't assume `M` to be modelled on `ℝ^n`, but add the model topological space `H`,
the vector space `E` and the model with corners `I` as type parameters.
- `SingularNManifold.map`: a map `X → Y` of topological spaces induces a map between the spaces
of singular n-manifolds
- `SingularNManifold.comap`: if `(N,f)` is a singular n-manifold on `X` and `φ: M → N` is smooth,
the `comap` of `(N,f)` and `φ` is the induced singular n-manifold `(M, f ∘ φ)` on `X`.
- `SingularNManifold.empty`: the empty set `M`, viewed as an `n`-manifold,
as a singular `n`-manifold over any space `X`.
- `SingularNManifold.trivial`: an `n`-dimensional manifold induces a singular `n`-manifold
on the one-point space.
- `SingularNManifold.prod`: the product of a singular `n`-manifold and a singular `m`-manifold
on the one-point space, is a singular `n+m`-manifold on the one-point space.
- `SingularNManifold.sum`: the disjoint union of two singular `n`-manifolds
is a singular `n`-manifold.

## Implementation notes

To be written! Document the design decisions and why they were made.

## TODO
- define cobordisms and the cobordism relation
- prove that the cobordisms relation is an equivalence relation
- define unoriented bordisms groups (as a set of equivalence classes),
prove they are a group
- define relative bordism groups (generalising the previous three points)
- prove that relative unoriented bordism groups define an extraordinary homology theory

## Tags

singular n-manifold, cobordism
-/

open scoped Manifold
open Module Set

noncomputable section

/-- A **singular `n`-manifold** on a topological space `X`, for `n ∈ ℕ`, is a pair `(M, f)`
of a closed `n`-dimensional `C^k` manifold `M` together with a continuous map `M → X`.
We assume that `M` is a manifold over the pair `(E, H)` with model `I`.

In practice, one commonly wants to take `k=∞` (as then e.g. the intersection form is a powerful tool
to compute bordism groups; for the definition, this makes no difference.) -/
structure SingularNManifold (X : Type*) [TopologicalSpace X] (n : ℕ) (k : ℕ∞)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) where
  /-- The manifold `M` of a singular `n`-manifold `(M, f)` -/
  M : Type*
  /-- The manifold `M` is a topological space. -/
  [topSpaceM : TopologicalSpace M]
  /-- The manifold `M` is a charted space over `H`. -/
  [chartedSpace : ChartedSpace H M]
  /-- `M` is a `C^k` manifold. -/
  [isManifold : IsManifold I k M]
  [compactSpace : CompactSpace M]
  [boundaryless : BoundarylessManifold I M]
  /-- `M` is `n`-dimensional, as its model space `E` is -/
  dimension : finrank ℝ E = n
  /-- The underlying map `M → X` of a singular `n`-manifold `(M, f)` on `X` -/
  f : M → X
  hf : Continuous f

namespace SingularNManifold

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {n : ℕ} {k : ℕ∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I k M] [CompactSpace M] [BoundarylessManifold I M]

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k I} : TopologicalSpace s.M := s.topSpaceM

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k I} : ChartedSpace H s.M := s.chartedSpace

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k I} : IsManifold I k s.M := s.isManifold

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k I} : CompactSpace s.M := s.compactSpace

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k I} : BoundarylessManifold I s.M :=
  s.boundaryless

/-- A map of topological spaces induces a corresponding map of singular n-manifolds. -/
-- This is part of proving functoriality of the bordism groups.
noncomputable def map (s : SingularNManifold X n k I)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y n k I where
  f := φ ∘ s.f
  hf := hφ.comp s.hf
  dimension := s.dimension

@[simp]
lemma map_f (s : SingularNManifold X n k I) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f :=
  rfl

lemma map_comp (s : SingularNManifold X n k I)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ((s.map hφ).map hψ).f = (ψ ∘ φ) ∘ s.f := by
  simp [Function.comp_def]
  rfl

-- Let M' and W be real C^k manifolds.
variable {E' E'' E''' H' H'' H''' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [IsManifold I' k M']
  [BoundarylessManifold I' M'] [CompactSpace M'] [FiniteDimensional ℝ E']

variable (M I) in
/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself.-/
noncomputable def refl (hdim : finrank ℝ E = n) :
    SingularNManifold M n k I where
  dimension := hdim
  f := id
  hf := continuous_id

/-- If `(N, f)` is a singular `n`-manifold on `X` and `M` another `n`-dimensional manifold,
a smooth map `φ : M → N` induces a singular `n`-manifold structure `(M, f ∘ φ)` on `X`. -/
noncomputable def comap [h : Fact (finrank ℝ E' = n)]
    (s : SingularNManifold X n k I)
    {φ : M' → s.M} (hφ : ContMDiff I' I n φ) : SingularNManifold X n k I' where
  f := s.f ∘ φ
  hf := s.hf.comp hφ.continuous
  dimension := h.out

@[simp]
lemma comap_f [Fact (finrank ℝ E' = n)]
    (s : SingularNManifold X n k I) {φ : M' → s.M} (hφ : ContMDiff I' I n φ) :
    (s.comap hφ).f = s.f ∘ φ :=
  rfl

variable (M I) in
/-- The canonical singular `n`-manifold associated to the empty set (seen as an `n`-dimensional
manifold, i.e. modelled on an `n`-dimensional space). -/
def empty [h : Fact (finrank ℝ E = n)] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [IsManifold I k M] [IsEmpty M] : SingularNManifold X n k I where
  M := M
  dimension := h.out
  f := fun x ↦ (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim

variable (M I) in
/-- An `n`-dimensional manifold induces a singular `n`-manifold on the one-point space. -/
def trivial [h : Fact (finrank ℝ E = n)] : SingularNManifold PUnit n k I where
  M := M
  dimension := h.out
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

/-- The product of a singular `n`- and a singular `m`-manifold into a one-point space
is a singular `n+m`-manifold. -/
-- FUTURE: prove that this observation induces a commutative ring structure
-- on the unoriented bordism group `Ω_n^O = Ω_n^O(pt)`.
def prod {m n : ℕ} (s : SingularNManifold PUnit n k I) (t : SingularNManifold PUnit m k I') :
    SingularNManifold PUnit (n + m) k (I.prod I') where
  M := s.M × t.M
  f := fun _ ↦ PUnit.unit
  hf := continuous_const
  dimension := by rw [finrank_prod, s.dimension, t.dimension]

variable (s t : SingularNManifold X n k I)

/-- The disjoint union of two singular `n`-manifolds on `X` is a singular `n`-manifold on `X`. -/
-- We need to choose a model space for the disjoint union (as a priori `s` and `t` could be
-- modelled on very different spaces: for simplicity, we choose `ℝ^n`; all real work is contained
-- in the two instances above.
def sum {n : ℕ} (s t : SingularNManifold X n k I) [finrank : Fact (finrank ℝ E = n)] :
    SingularNManifold X n k I where
  M := s.M ⊕ t.M
  dimension := finrank.out
  f := Sum.elim s.f t.f
  hf := s.hf.sum_elim t.hf

end SingularNManifold
