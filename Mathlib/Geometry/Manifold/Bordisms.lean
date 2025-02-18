/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Diffeomorph
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
We don't assume `M` to be modelled on `ℝ^n` (nor to be using with the standard model),
but instead add the model topological space `H`, the vector space `E` and the model with corners `I`
as type parameters.
- `SingularNManifold.map`: a map `X → Y` of topological spaces induces a map between the spaces
of singular n-manifolds
- `SingularNManifold.comap`: if `(N,f)` is a singular n-manifold on `X` and `φ: M → N` is smooth,
the `comap` of `(N,f)` and `φ` is the induced singular n-manifold `(M, f ∘ φ)` on `X`.
- `SingularNManifold.empty`: the empty set `M`, viewed as an `n`-manifold,
as a singular `n`-manifold over any space `X`
- `SingularNManifold.trivial`: an `n`-dimensional manifold induces a singular `n`-manifold
on the one-point space.
- `SingularNManifold.prod`: the product of a singular `n`-manifold and a singular `m`-manifold
on the one-point space, is a singular `n+m`-manifold on the one-point space.
- `SingularNManifold.sum`: the disjoint union of two singular `n`-manifolds
is a singular `n`-manifold

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

In practice, one commonly wants to take `k=∞` (as then e.g. the intersection form is a powerful tool
to compute bordism groups; for the definition, this makes no difference.) -/
structure SingularNManifold.{u, v, w} (X : Type w) [TopologicalSpace X] (n : ℕ) (k : ℕ∞) where
  /-- The normed space on which the manifold `M` is modeled. -/
  E : Type v
  /-- `E` is normed (additive) abelian group -/
  [normedAddCommGroup : NormedAddCommGroup E]
  /-- `E` is a real normed space -/
  [normedSpace: NormedSpace ℝ E]
  /-- The smooth manifold `M` of a singular `n`-manifold `(M, f)` -/
  M : Type u
  /-- The smooth manifold `M` is a topological space -/
  [topSpaceM : TopologicalSpace M]
  /-- The topological space on which the manifold `M` is modeled -/
  H : Type v
  /-- `H` is a topological space -/
  [topSpaceH : TopologicalSpace H]
  /-- The smooth manifold `M` is a charted space over `H` -/
  [chartedSpace : ChartedSpace H M]
  /-- A homeomorphism `H ≃ₜ ℝ^n`: this is used to define disjoint unions of singular n-manifolds -/
  modelSpace_homeo_euclideanSpace : H ≃ₜ EuclideanSpace ℝ (Fin n)
  /-- The model with corners for the manifold `M` -/
  I : ModelWithCorners ℝ E H
  /-- `M` is a smooth manifold with corners -/
  [smoothMfd : IsManifold I k M]
  /-- `M` is compact -/
  [compactSpace : CompactSpace M]
  /-- `M` is boundaryless -/
  [boundaryless: BoundarylessManifold I M]
  /-- `M` is finite-dimensional, as its model space `E` is -/
  [findim: FiniteDimensional ℝ E]
  /-- `M` is `n`-dimensional, as its model space `E` is -/
  dimension : finrank ℝ E = n
  /-- The underlying map `M → X` of a singular `n`-manifold `(M, f)` on `X` -/
  f : M → X
  hf : Continuous f

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : NormedAddCommGroup s.E :=
  s.normedAddCommGroup

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : NormedSpace ℝ s.E := s.normedSpace

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : TopologicalSpace s.M := s.topSpaceM

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : TopologicalSpace s.H := s.topSpaceH

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : ChartedSpace s.H s.M := s.chartedSpace

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : IsManifold s.I k s.M := s.smoothMfd

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : CompactSpace s.M := s.compactSpace

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : BoundarylessManifold s.I s.M :=
  s.boundaryless

instance {n : ℕ} {k : ℕ∞} {s : SingularNManifold X n k} : FiniteDimensional ℝ s.E := s.findim

namespace SingularNManifold

variable {n : ℕ} {k : ℕ∞}

/-- A map of topological spaces induces a corresponding map of singular n-manifolds. -/
-- This is part of proving functoriality of the bordism groups.
noncomputable def map (s : SingularNManifold X n k)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y n k where
  modelSpace_homeo_euclideanSpace := s.modelSpace_homeo_euclideanSpace
  I := s.I
  f := φ ∘ s.f
  hf := hφ.comp s.hf
  dimension := s.dimension

@[simp]
lemma map_f (s : SingularNManifold X n k) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f :=
  rfl

lemma map_comp (s : SingularNManifold X n k)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ((s.map hφ).map hψ).f = (ψ ∘ φ) ∘ s.f := by
  simp [Function.comp_def]
  rfl

-- Let M, M' and W be smooth manifolds.
universe u
variable {E E' E'' E''' H H' H'' H''' : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I k M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [IsManifold I' k M']
  [BoundarylessManifold I M] [CompactSpace M] [FiniteDimensional ℝ E]
  [BoundarylessManifold I' M'] [CompactSpace M'] [FiniteDimensional ℝ E']

variable (M) in
/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself.

On paper, it is apparent that `M` is modelled on `n`-dimensional Euclidean space.
However, abstractly constructing such an equivalence requires a non-canonical choice:
thus, we prefer to pass in this assumption external.
For constructions modelled on `ℝ^n`, this homeomorphism is trivial to supply,
i.e. this requirement does not pose an issue in practice. -/
noncomputable def refl (hequiv : H ≃ₜ EuclideanSpace ℝ (Fin n)) (hdim : finrank ℝ E = n) :
    SingularNManifold M n k where
  modelSpace_homeo_euclideanSpace := hequiv
  H := H
  I := I
  dimension := hdim
  f := id
  hf := continuous_id

/-- If `(N, f)` is a singular `n`-manifold on `X` and `M` another `n`-dimensional smooth manifold,
a smooth map `φ : M → N` induces a singular `n`-manifold structure `(M, f ∘ φ)` on `X`. -/
noncomputable def comap (hequiv : H ≃ₜ EuclideanSpace ℝ (Fin n)) [h : Fact (finrank ℝ E = n)]
    (s : SingularNManifold X n k)
    {φ : M → s.M} (hφ : ContMDiff I s.I n φ) : SingularNManifold X n k where
  E := E
  M := M
  H := H
  modelSpace_homeo_euclideanSpace := hequiv
  I := I
  f := s.f ∘ φ
  hf := s.hf.comp hφ.continuous
  dimension := h.out

@[simp]
lemma comap_f (hequiv : H ≃ₜ EuclideanSpace ℝ (Fin n)) [Fact (finrank ℝ E = n)]
    (s : SingularNManifold X n k) {φ : M → s.M} (hφ : ContMDiff I s.I n φ) :
    (s.comap hequiv hφ).f = s.f ∘ φ :=
  rfl

variable (M) in
/-- The canonical singular `n`-manifold associated to the empty set (seen as an `n`-dimensional
manifold, i.e. modelled on an `n`-dimensional space). -/
def empty (hequiv : H ≃ₜ EuclideanSpace ℝ (Fin n)) [h: Fact (finrank ℝ E = n)]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [IsManifold I k M] [IsEmpty M] :
  SingularNManifold X n k where
  M := M
  E := E
  H := H
  modelSpace_homeo_euclideanSpace := hequiv
  I := I
  dimension := h.out
  f := fun x ↦ (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim

variable (M) in
/-- An `n`-dimensional manifold induces a singular `n`-manifold on the one-point space. -/
def trivial (hequiv : H ≃ₜ EuclideanSpace ℝ (Fin n)) [h: Fact (finrank ℝ E = n)] :
    SingularNManifold PUnit n k where
  E := E
  M := M
  modelSpace_homeo_euclideanSpace := hequiv
  I := I
  dimension := h.out
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

def EuclideanSpace.prodEquivSum (α β 𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    (EuclideanSpace 𝕜 α) × (EuclideanSpace 𝕜 β) ≃ₜ EuclideanSpace 𝕜 (α ⊕ β) where
  toEquiv := (Equiv.sumArrowEquivProdArrow α β 𝕜).symm
  continuous_toFun := sorry
  continuous_invFun := sorry

-- XXX: better name!
def EuclideanSpace.congr {α β 𝕜 : Type*} [Fintype α] [NontriviallyNormedField 𝕜] (h : α ≃ β) :
    EuclideanSpace 𝕜 α ≃ₜ EuclideanSpace 𝕜 β :=
  haveI := Fintype.ofEquiv α h
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 h).toHomeomorph

def EuclideanSpace.prod_dimension {𝕜 : Type*} [NontriviallyNormedField 𝕜] (n m : ℕ) :
    (EuclideanSpace 𝕜 (Fin n)) × (EuclideanSpace 𝕜 (Fin m)) ≃ₜ
      (EuclideanSpace 𝕜 (Fin (n + m))) :=
  (EuclideanSpace.prodEquivSum (Fin n) (Fin m) 𝕜).trans (EuclideanSpace.congr finSumFinEquiv)

/-- The product of a singular `n`- and a singular `m`-manifold into a one-point space
is a singular `n+m`-manifold. -/
-- FUTURE: prove that this observation induces a commutative ring structure
-- on the unoriented bordism group `Ω_n^O = Ω_n^O(pt)`.
def prod {m n : ℕ} (s : SingularNManifold PUnit n k) (t : SingularNManifold PUnit m k) :
    SingularNManifold PUnit (n + m) k where
  M := s.M × t.M
  H := ModelProd s.H t.H
  modelSpace_homeo_euclideanSpace :=
    letI this : s.H × t.H ≃ₜ (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin m)) :=
      s.modelSpace_homeo_euclideanSpace.prodCongr t.modelSpace_homeo_euclideanSpace
    this.trans (EuclideanSpace.prod_dimension n m)
  I := s.I.prod t.I
  f := fun _ ↦ PUnit.unit
  hf := continuous_const
  dimension := by rw [finrank_prod, s.dimension, t.dimension]

def chartedSpaceEuclidean {n : ℕ} (s : SingularNManifold X n k) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) s.H :=
  s.modelSpace_homeo_euclideanSpace.toPartialHomeomorph.singletonChartedSpace
  s.modelSpace_homeo_euclideanSpace.toPartialHomeomorph_source

attribute [local instance] chartedSpaceEuclidean in
instance {n : ℕ} (s t : SingularNManifold X n k) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (s.M ⊕ t.M) := by
  haveI := ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) s.H s.M
  haveI := ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) t.H t.M
  infer_instance

instance {n : ℕ} (s t : SingularNManifold X n k) : IsManifold (𝓡 n) k (s.M ⊕ t.M) := sorry

/-- The disjoint union of two singular `n`-manifolds on `X` is a singular `n`-manifold on `X`. -/
-- We need to choose a model space for the disjoint union (as a priori `s` and `t` could be
-- modelled on very different spaces: for simplicity, we choose `ℝ^n`; all real work is contained
-- in the two instances above.
def sum {n : ℕ} (s t : SingularNManifold X n k) : SingularNManifold X n k where
  E := EuclideanSpace ℝ (Fin n)
  H := EuclideanSpace ℝ (Fin n)
  M := s.M ⊕ t.M
  modelSpace_homeo_euclideanSpace := Homeomorph.refl _
  I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  dimension := finrank_euclideanSpace_fin
  f := Sum.elim s.f t.f
  hf := s.hf.sum_elim t.hf

end SingularNManifold
