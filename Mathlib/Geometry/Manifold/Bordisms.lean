/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.InteriorBoundary

/-!
# Unoriented bordism theory

In this file, we sketch the beginnings of unoriented bordism theory.
Some pieces can already go in mathlib already.
This is not ready for mathlib yet (as we still need the instance that the boundary
of a manifold is a manifold again, might might need some hypotheses to be true).
-/

/-
Missing API for this to work nicely:
- boundary of manifolds: add a typeclass "HasNiceBoundary" (or so) which says
  the boundary is a manifold, and the inclusion is smooth (perhaps with demanding "dimension one less")
  The current definition of boundary and corners will not satisfy this, but many nice manifolds
  will. Prove that boundaryless manifolds are of this form, or so.
- add disjoint union of top. spaces and induced maps: mathlib has this
- define the disjoint union of smooth manifolds, and the associated maps: show they are smooth
(perhaps prove as abstract nonsense? will see!)

- then: complete definition of unoriented cobordisms; complete constructions I had
- fight DTT hell: why is the product with an interval not recognised?

- define the bordism relation/how to define the set of equivalence classes?
equivalences work nicely in the standard design... that's a "how to do X in Lean" question
- postponed: transitivity of the bordism relation (uses the collar neighbourhood theorem)

define induced maps between bordism groups (on singular n-manifolds is easy and done)
functoriality: what exactly do I have to show? also DTT question

prove some of the easy axioms of homology... perhaps all of it?
does mathlib have a class "extraordinary homology theory"? this could be an interesting instance...
-/

open scoped Manifold
open Metric (sphere)
open FiniteDimensional

noncomputable section

-- Closed and n-dimensional manifolds: these should also move to a separate file.
-- TODO: generalise to `BoundarylessManifold I M`
section ClosedManifold

variable (n : ℕ) {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M]

/-- A topological manifold is called **closed** iff it is compact without boundary. -/
structure ClosedManifold [CompactSpace M] [I.Boundaryless]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (N : Type*) [TopologicalSpace N] [ChartedSpace H' N]
  (J : ModelWithCorners 𝕜 E' H') [SmoothManifoldWithCorners J N]

instance ClosedManifold.prod [CompactSpace M] [I.Boundaryless] [CompactSpace N] [J.Boundaryless] :
  ClosedManifold (M × N) (I.prod J) where

/-- An **n-manifold** is a smooth `n`-dimensional manifold. -/
structure NManifold [NormedAddCommGroup E]  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M] where
  hdim : finrank 𝕜 E = n

/-- The product of an `n`- and and an `m`-manifold is an `n+m`-manifold. -/
instance NManifold.prod {m n : ℕ} [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (s : NManifold m M I) (t : NManifold n N J) : NManifold (m + n) (M × N) (I.prod J) where
  hdim := by rw [s.hdim.symm, t.hdim.symm]; apply finrank_prod

structure ClosedNManifold [CompactSpace M] [I.Boundaryless] [FiniteDimensional 𝕜 E]
    extends NManifold n M I

instance ClosedNManifold.ClosedManifold [CompactSpace M] [I.Boundaryless] [FiniteDimensional 𝕜 E] :
  ClosedManifold M I where

variable {n}

/-- The product of a closed `n`- and a closed closed `m`-manifold is a closed `n+m`-manifold. -/
instance ClosedNManifold.prod {m n : ℕ} [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    [CompactSpace M] [I.Boundaryless] [CompactSpace N] [J.Boundaryless]
    (s : ClosedNManifold m M I) (t : ClosedNManifold n N J) :
    ClosedNManifold (m + n) (M × N) (I.prod J) where
  -- TODO: can I inherit this from `NManifold.prod`?
  hdim := by rw [s.hdim.symm, t.hdim.symm]; apply finrank_prod

section examples

-- Let `E` be a finite-dimensional real normed space.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard `n`-sphere is a closed manifold. -/
example {n : ℕ} [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1)] :
  ClosedManifold (sphere (0 : E) 1) (𝓡 n) where

/-- The standard `2`-torus is a closed manifold. -/
example [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 1 + 1)] :
    ClosedManifold ((sphere (0 : E) 1) × (sphere (0 : E) 1)) ((𝓡 2).prod (𝓡 2)) where

-- The standard Euclidean space is an `n`-manifold. -/
example {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] : NManifold n M (𝓡 n) where
  hdim := finrank_euclideanSpace_fin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The standard `n`-sphere is a closed `n`-manifold. -/
example {n : ℕ} [Fact (finrank ℝ F = n + 1)] : ClosedNManifold n (sphere (0 : F) 1) (𝓡 n) where
  hdim := finrank_euclideanSpace_fin

/-- The standard 2-torus is a closed two-manifold. -/
example [Fact (finrank ℝ F = 1 + 1)] :
    ClosedNManifold 2 ((sphere (0 : F) 1) × (sphere (0 : F) 1)) ((𝓡 1).prod (𝓡 1)) where
  hdim := by rw [finrank_prod, finrank_euclideanSpace_fin]

end examples

end ClosedManifold

-- Pre-requisite: the interval `Icc x y has boundary {x, y}`, and related results.
-- TODO: move to `Instances/Real` (and make that import `InteriorBoundary`)
section BoundaryIntervals

variable {x y : ℝ} (hxy : x < y)

open Set

lemma boundary_IccManifold [h : Fact (x < y)] : (𝓡∂ 1).boundary (Set.Icc x y) =
    { ⟨x, ⟨le_refl x, by linarith⟩⟩, ⟨y, ⟨by linarith, le_refl y⟩⟩} := by
  sorry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [SmoothManifoldWithCorners I M] [I.Boundaryless] [CompactSpace M] [FiniteDimensional ℝ E]

/-- The boundary of the interval [x,y], as a subset of `Icc x y`. -/
def A : Set (Icc x y) := { ⟨x, ⟨le_refl x, by linarith⟩⟩, ⟨y, ⟨by linarith, le_refl y⟩⟩}

/-- A product `M × [x,y]` has boundary `M × {x,y}`. -/
lemma boundary_product [h : Fact (x < y)] :
    (I.prod (𝓡∂ 1)).boundary (M × Icc x y) = ((univ : Set M) × (A hxy)) := by
  have : (𝓡∂ 1).boundary (Set.Icc x y) = A hxy := by
    rw [boundary_IccManifold hxy]; simp only [A]
  rw [boundary_of_boundaryless_left]
  rw [this]
  set X := (modelWithCornersEuclideanHalfSpace 1).boundary ↑(Icc x y)
  -- one coercion doesn't align; this should be obvious now!
  sorry

end BoundaryIntervals

-- Let M, M' and W be smooth manifolds.
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace SingularNManifold

/-- A **singular `n`-manifold** on a topological space `X` consists of a
closed smooth `n`-manifold `M` and a continuous map `f : M → X`. -/
structure _root_.SingularNManifold (X : Type*) [TopologicalSpace X] (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
    [CompactSpace M] [I.Boundaryless] [FiniteDimensional ℝ E] extends ClosedNManifold n M I where
  f : M → X
  hf : Continuous f

-- We declare these variables *after* the definition above, so `SingularNManifold` can have
-- its current order of arguments.
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {n : ℕ}
  [I.Boundaryless] [CompactSpace M] [FiniteDimensional ℝ E]

/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
noncomputable def refl (hdim : finrank ℝ E = n) : SingularNManifold M n M I where
  hdim := hdim
  f := id
  hf := continuous_id

-- functoriality: pre-step towards functoriality of the bordism groups
-- xxx: good name?
noncomputable def map (s : SingularNManifold X n M I)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y n M I where
  hdim := s.hdim
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp]
lemma map_f (s : SingularNManifold X n M I) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f := rfl

-- useful, or special case of the above?
lemma map_comp (s : SingularNManifold X n M I)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ):
    ((s.map hφ).map hψ).f = (s.map (hψ.comp hφ)).f := rfl

end SingularNManifold

section HasNiceBoundary

/-- We say a smooth manifold `M` *has nice boundary* if its boundary (as a subspace)
is a smooth manifold such that the inclusion is smooth.
`NiceBoundaryData` gathers all data included in such a choice: a charted space structure
on the boundary, a model with corners and a manifold atlas. -/
structure NiceBoundaryData (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M] where
  E' : Type*
  [normedGroup : NormedAddCommGroup E']
  [normedSpace : NormedSpace ℝ E']
  H' : Type*
  [topH : TopologicalSpace H']
  charts : ChartedSpace H' (I.boundary M)
  J : ModelWithCorners ℝ E' H'
  [mfd : SmoothManifoldWithCorners J (I.boundary M)]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]

/-- `HasNiceBoundary M I J` means the boundary of the manifold `M` modelled on `I`
has a charted space structure and model (included in `s`) which makes it a smooth manifold,
such that the inclusion `∂M → M` is smooth. -/
class HasNiceBoundary (s : NiceBoundaryData M I) where
-- TODO: this errors! do I need to include additional compatibility conditions?
-- can I encode the above better?
-- synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
--   this
-- inferred
--   s.normedGroup
  -- smoothInclusion :
  --   haveI := s.normedGroup;
  --   haveI c := s.charts;
  --   ContMDiff s.J I ∞ ((fun ⟨x, _⟩ ↦ x) : (I.boundary M) → M)

end HasNiceBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {I'' : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners I'' M''] {n : ℕ}
  [CompactSpace M] [I.Boundaryless] [FiniteDimensional ℝ E]
  [CompactSpace M'] [I'.Boundaryless] [FiniteDimensional ℝ E']
  [CompactSpace M''] [I''.Boundaryless] [FiniteDimensional ℝ E'']

namespace UnorientedCobordism

-- TODO: for now, assume all manifolds are modelled on the same chart and model space...

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {I' : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I' M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {I'' : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I'' M''] {n : ℕ}
  [CompactSpace M] [I.Boundaryless]
  [CompactSpace M'] [I'.Boundaryless] [CompactSpace M''] [I''.Boundaryless]

-- All this is full sci-fi, but let's pretend this for now to limp along!!
namespace ScifiBoundary

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  (hE : finrank ℝ E = n + 1) (hE₀ : finrank ℝ E₀ = n)
  {H₀ : Type*} [TopologicalSpace H₀]

instance charts : ChartedSpace H₀ (I.boundary M) := sorry

-- TODO: this depends on I and M
def model : ModelWithCorners ℝ E₀ H₀ := sorry

instance manifold : SmoothManifoldWithCorners (H := H₀) (E := E₀) model/-(model I M)-/ (I.boundary M) := sorry

end ScifiBoundary

/-- An **unoriented cobordism** between two singular `n`-manifolds (M,f) and (N,g) on `X`
is a compact smooth `n`-manifold `W` with a continuous map `F: W→ X` whose boundary is diffeomorphic
to the disjoint union M ⊔ N such that F restricts to f resp. g in the obvious way. -/
structure _root_.UnorientedCobordism (s : SingularNManifold X n M I) (t : SingularNManifold X n M' I')
    (W : Type*) [TopologicalSpace W] [ChartedSpace H'' W]
    (J : ModelWithCorners ℝ E'' H'') [SmoothManifoldWithCorners J W] where
  hW : CompactSpace W
  hW' : finrank ℝ E'' = n + 1
  F : W → X
  hF : Continuous F
  -- φ : Diffeomorph model I (J.boundary W) M ∞--(I.disjUnion I') (M ⊔ M')
  -- φ : Diffeomorph (∂ W) (induced J) (M ⊔ M') I.disjUnion I'
  -- hFf : F.restrict φ^{-1}(M) = s.f
  -- hFg : F.restrict φ^{-1}(N) = t.f

open Set

/-- Each singular `n`-manifold `(M,f)` is cobordant to itself. -/
def refl (s : SingularNManifold X n M I) :
    UnorientedCobordism s s (M × (Icc (0 : ℝ) 1)) (I.prod (𝓡∂ 1)) where
  hW := by infer_instance
  hW' := by rw [finrank_prod, s.hdim, finrank_euclideanSpace_fin]
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst

variable (s : SingularNManifold X n M I) (t : SingularNManifold X n M' I')
  {W : Type*} [TopologicalSpace W] [ChartedSpace H'' W]
  {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]

/-- Being cobordant is symmetric. -/
def symm (φ : UnorientedCobordism s t W J) : UnorientedCobordism t s W J where
  hW := φ.hW
  hW' := φ.hW'
  F := φ.F
  hF := φ.hF
  -- TODO: boundary stuff...

-- Fleshing out the details for transitivity will take us too far: we merely sketch the necessary
-- pieces.
section transSketch

variable {u : SingularNManifold X n M'' I''}
  {W' : Type*} [TopologicalSpace W'] [ChartedSpace H''' W']
  {J' : ModelWithCorners ℝ E''' H'''} [SmoothManifoldWithCorners J' W']
variable {s t}

-- Idea: glue the cobordisms W and W' along their common boundary M',
-- as identified by the diffeomorphism W → M' ← W'.
-- This could be formalised as an adjunction/attaching maps: these are a special case of pushouts
-- (in the category of topological spaces).
-- mathlib has abstract pushouts (and proved that TopCat has them);
-- `Topology/Category/TopCat/Limits/Pullbacks.lean` provides a concrete description of pullbacks
-- in TopCat. A good next step would be to adapt this argument to pushouts, and use this here.
def glue (φ : UnorientedCobordism s t W J) (ψ : UnorientedCobordism t u W' J') : Type* := sorry

instance (φ : UnorientedCobordism s t W J) (ψ : UnorientedCobordism t u W' J') :
    TopologicalSpace (glue φ ψ) := sorry

-- TODO: Using E and H in this declaration and the next one is wrong...
-- Do I need to demand that all manifolds are modeled on the same spaces H and E,
-- or choose an explicit isomorphism? What's the best way here?
-- (In practice, post-composing with a suitable equivalence allows assuming H and E are the same...
-- the question is where this complexity should go.)

-- This and the next item require the collar neighbourhood theorem-
instance (φ : UnorientedCobordism s t W J) (ψ : UnorientedCobordism t u W' J') :
    ChartedSpace H (glue φ ψ) := sorry

def glueModel (φ : UnorientedCobordism s t W J) (ψ : UnorientedCobordism t u W' J') :
    ModelWithCorners ℝ E H := sorry

instance (φ : UnorientedCobordism s t W J) (ψ : UnorientedCobordism t u W' J') :
    SmoothManifoldWithCorners (glueModel φ ψ) (glue φ ψ) := sorry

noncomputable def trans (φ : UnorientedCobordism s t W J) (ψ : UnorientedCobordism t u W' J') :
    UnorientedCobordism s u (glue φ ψ) (glueModel φ ψ) where
  hW := sorry
  hW' := sorry
  F := sorry
  hF := sorry

end transSketch

end UnorientedCobordism

-- how to encode this in Lean?
-- Two singular `n`-manifolds are cobordant iff there exists a smooth cobordism between them.
-- The unoriented `n`-bordism group `Ω_n^O(X)` of `X` is the set of all equivalence classes
-- of singular n-manifolds up to bordism.
-- then: functor between these...

-- prove: every element in Ω_n^O(X) has order two
