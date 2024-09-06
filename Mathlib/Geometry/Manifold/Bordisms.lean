/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
## (Unoriented) bordism theory

This file defines the beginnings of (unoriented) bordism theory. For the full definition,
a number of prerequisites are missing from mathlib, but a surprising amount of progress
can already be made today.

Currently, this file only contains the definition of *singular *n*-manifolds*:
bordism classes are the equivalence classes of singular n-manifolds w.r.t. the (co)bordism relation.

## Main definitions

- **SingularNManifold**: a singular `n`-manifold on a topological space `X`, for `n ∈ ℕ`,
is a pair `(M,f)` of a closed `n`-dimensional manifold `M` together with a continuous map `M → X`.
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

## TODO
- define cobordisms and the cobordism relation
- prove that the cobordisms relation is an equivalence relation
- define unoriented bordisms groups (as a set of equivalence classes),
prove they are a group
- prove that unoriented bordism groups define an extraordinary homology theory

## Tags
singular n-manifold, cobordism

-/

open scoped Manifold
open FiniteDimensional Set

noncomputable section

structure SingularNManifold (X : Type*) [TopologicalSpace X] (n : ℕ) where
  E : Type*
  [normedAddCommGroup : NormedAddCommGroup E]
  [normedSpace: NormedSpace ℝ E]
  M : Type*
  [topSpaceM : TopologicalSpace M]
  H : Type*
  [topSpaceH : TopologicalSpace H]
  [chartedSpace : ChartedSpace H M]
  model : ModelWithCorners ℝ E H
  [smoothMfd : SmoothManifoldWithCorners model M]
  [compactSpace : CompactSpace M]
  [boundaryless: BoundarylessManifold model M]
  [findim: FiniteDimensional ℝ E]
  [dimension : finrank ℝ E = n]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M,f)` on `X` -/
  f : M → X
  hf : Continuous f

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

instance {n : ℕ} {s : SingularNManifold X n} : NormedAddCommGroup s.E := s.normedAddCommGroup

instance {n : ℕ} {s : SingularNManifold X n} : NormedSpace ℝ s.E := s.normedSpace

instance {n : ℕ} {s : SingularNManifold X n} : TopologicalSpace s.M := s.topSpaceM

instance {n : ℕ} {s : SingularNManifold X n} : TopologicalSpace s.H := s.topSpaceH

instance {n : ℕ} {s : SingularNManifold X n} : ChartedSpace s.H s.M := s.chartedSpace

instance {n : ℕ} {s : SingularNManifold X n} : SmoothManifoldWithCorners s.model s.M := s.smoothMfd

instance {n : ℕ} {s : SingularNManifold X n} : CompactSpace s.M := s.compactSpace

instance {n : ℕ} {s : SingularNManifold X n} : BoundarylessManifold s.model s.M := s.boundaryless

instance {n : ℕ} {s : SingularNManifold X n} : FiniteDimensional ℝ s.E := s.findim

instance {n : ℕ} {s : SingularNManifold X n} : finrank ℝ s.E = n := s.dimension

namespace SingularNManifold

variable {n : ℕ}

/-- A map of topological spaces induces a corresponding map of singular n-manifolds. -/
-- This is part of proving functoriality of the bordism groups.
noncomputable def map (s : SingularNManifold X n)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y n where
  model := s.model
  f := φ ∘ s.f
  hf := hφ.comp s.hf
  dimension := s.dimension

@[simp]
lemma map_f (s : SingularNManifold X n) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f :=
  rfl

lemma map_comp (s : SingularNManifold X n)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ((s.map hφ).map hψ).f = (ψ ∘ φ) ∘ s.f := by
  simp [Function.comp_def]
  rfl

-- Let M, M' and W be smooth manifolds.
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {n : ℕ}
  [BoundarylessManifold I M] [CompactSpace M] [FiniteDimensional ℝ E]
  [BoundarylessManifold I' M'] [CompactSpace M'] [FiniteDimensional ℝ E']

variable (M) in
/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
noncomputable def refl (hdim : finrank ℝ E = n) : SingularNManifold M n where
  H := H
  model := I
  dimension := hdim
  f := id
  hf := continuous_id

/-- If `(N, f)` is a singular `n`-manifold on `X` and `M` another `n`-dimensional smooth manifold,
a smooth map `φ : M → N` induces a singular `n`-manifold structure `(M, f ∘ φ)` on `X`. -/
noncomputable def comap [h: Fact (finrank ℝ E = n)]
    (s : SingularNManifold X n)
    {φ : M → s.M} (hφ : Smooth I s.model φ) : SingularNManifold X n where
  E := E
  M := M
  H := H
  model := I
  f := s.f ∘ φ
  hf := s.hf.comp hφ.continuous
  dimension := h.out

@[simp]
lemma comap_f [Fact (finrank ℝ E = n)]
    (s : SingularNManifold X n) {φ : M → s.M} (hφ : Smooth I s.model φ) :
    (s.comap hφ).f = s.f ∘ φ :=
  rfl

variable (M) in
/-- The canonical singular `n`-manifold associated to the empty set (seen as an `n`-dimensional
manifold, i.e. modelled on an `n`-dimensional space). -/
def empty [h: Fact (finrank ℝ E = n)] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M] [IsEmpty M] :
  SingularNManifold X n where
  M := M
  E := E
  H := H
  model := I
  dimension := h.out
  f := fun x ↦ (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim

variable (M) in
/-- An `n`-dimensional manifold induces a singular `n`-manifold on the one-point space. -/
def trivial [h: Fact (finrank ℝ E = n)] : SingularNManifold PUnit n where
  E := E
  M := M
  model := I
  dimension := h.out
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

/-- The product of a singular `n`- and a `m`-manifold into a one-point space
is a singular `n+m`-manifold. -/
-- FUTURE: prove that this observation inducess a commutative ring structure
-- on the unoriented bordism group `Ω_n^O = Ω_n^O(pt)`.
def prod {m n : ℕ} (s : SingularNManifold PUnit n) (t : SingularNManifold PUnit m) :
    SingularNManifold PUnit (n + m) where
  M := s.M × t.M
  model := s.model.prod t.model
  f := fun _ ↦ PUnit.unit
  hf := continuous_const
  dimension := by rw [finrank_prod, s.dimension, t.dimension]

end SingularNManifold
