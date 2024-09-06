/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
TODO docstring

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

-- TODO: fix these two!
-- /-- If `(M', f)` is a singular `n`-manifold on `X` and `M'` another `n`-dimensional smooth manifold,
-- a smooth map `φ : M → M'` induces a singular `n`-manifold structure `(M, f ∘ φ)` on `X`. -/
-- noncomputable def comap [Fact (finrank ℝ E = n)]
--     (s : SingularNManifoldDummy X n)
--     {φ : s.M → M'} (hφ : Smooth s.I I' φ) : SingularNManifoldDummy X n where
--   E := s.E
--   M := s.M
--   H := s.H
--   I := s.I
--   f := s.f ∘ φ
--   hf := s.hf.comp hφ.continuous

-- @[simp]
-- lemma comap_f [Fact (finrank ℝ E = n)]
--     (s : SingularNManifold X n M' I') {φ : M → M'} (hφ : Smooth I I' φ) :
--     (s.comap hφ).f = s.f ∘ φ :=
--   rfl

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

#exit
-- Let M, M' and W be smooth manifolds.
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


/-- A **singular `n`-manifold** on a topological space `X` consists of a
closed smooth `n`-manifold `M` and a continuous map `f : M → X`. -/
structure SingularNManifoldOld (X : Type*) [TopologicalSpace X] (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
    [CompactSpace M] [BoundarylessManifold I M] [FiniteDimensional ℝ E] where
  [hdim : Fact (finrank ℝ E = n)]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M,f)` on `X` -/
  f : M → X
  hf : Continuous f

namespace SingularNManifoldOld

-- We declare these variables *after* the definition above, so `SingularNManifold` can have
-- its current order of arguments.
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {n : ℕ}
  [BoundarylessManifold I M] [CompactSpace M] [FiniteDimensional ℝ E]
  [BoundarylessManifold I' M'] [CompactSpace M'] [FiniteDimensional ℝ E']


/-- If `(M', f)` is a singular `n`-manifold on `X` and `M'` another `n`-dimensional smooth manifold,
a smooth map `φ : M → M'` induces a singular `n`-manifold structure on `M`. -/
noncomputable def comap [Fact (finrank ℝ E = n)]
    (s : SingularNManifoldOld X n M' I')
    {φ : M → M'} (hφ : Smooth I I' φ) : SingularNManifoldOld X n M I where
  f := s.f ∘ φ
  hf := s.hf.comp hφ.continuous

@[simp]
lemma comap_f [Fact (finrank ℝ E = n)]
    (s : SingularNManifoldOld X n M' I') {φ : M → M'} (hφ : Smooth I I' φ) :
    (s.comap hφ).f = s.f ∘ φ :=
  rfl

end SingularNManifoldOld
