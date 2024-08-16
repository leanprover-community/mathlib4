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
Not all of this might end up in mathlib already (depending on how many pre-requisites are missing),
but a fair number of pieces already can be upstreamed!

-/

/-
Missing API for this to work nicely:
- add disjoint union of top. spaces and induced maps: mathlib has this
- define the disjoint union of smooth manifolds, and the associated maps: show they are smooth
(perhaps prove as abstract nonsense? will see!)

- then: complete definition of unoriented cobordisms; complete constructions I had
- fight DTT hell: why is the product with an interval not recognised?

- define the bordism relation/how to define the set of equivalence classes?
equivalences work nicely in the standard design... that's a "how to do X in Lean" question
- postponed: transitivity of the bordism relation (uses the collar neighbourhood theorem)

- define induced maps between bordism groups (on singular n-manifolds is easy and done)
- functoriality: what exactly do I have to show? also DTT question

- prove some of the easy axioms of homology... perhaps all of it?
- does mathlib have a class "extraordinary homology theory"? this could be an interesting instance...
-/

open scoped Manifold
open Metric (sphere)
open FiniteDimensional Set

noncomputable section

-- Closed and `n`-dimensional manifolds: these should also move to a separate file.
section ClosedManifold

variable (n : ℕ) {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M]

/-- A topological manifold is called **closed** iff it is compact without boundary. -/
structure ClosedManifold [CompactSpace M] [BoundarylessManifold I M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (N : Type*) [TopologicalSpace N] [ChartedSpace H' N]
  (J : ModelWithCorners 𝕜 E' H') [SmoothManifoldWithCorners J N]

instance ClosedManifold.prod [CompactSpace M] [BoundarylessManifold I M]
    [CompactSpace N] [BoundarylessManifold J N] :
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

structure ClosedNManifold [CompactSpace M] [BoundarylessManifold I M] [FiniteDimensional 𝕜 E]
    extends NManifold n M I

instance ClosedNManifold.ClosedManifold [CompactSpace M] [BoundarylessManifold I M]
  [FiniteDimensional 𝕜 E] : ClosedManifold M I where

variable {n}

/-- The product of a closed `n`- and a closed closed `m`-manifold is a closed `n+m`-manifold. -/
instance ClosedNManifold.prod {m n : ℕ} [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    [CompactSpace M] [BoundarylessManifold I M] [CompactSpace N] [BoundarylessManifold J N]
    (s : ClosedNManifold m M I) (t : ClosedNManifold n N J) :
    ClosedNManifold (m + n) (M × N) (I.prod J) where
  -- TODO: can I inherit this from `NManifold.prod`?
  hdim := by rw [s.hdim.symm, t.hdim.symm]; apply finrank_prod

section examples

-- Let `E` be a finite-dimensional real normed space.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- TODO: move the empty manifold here, once its definition is in a separate file

/- TODO: these two examples worked when ClosedManifold only demanded `I.Boundaryless`;
-- diagnose and fix this!
/-- The standard `n`-sphere is a closed manifold. -/
example {n : ℕ} [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1)] :
  ClosedManifold (sphere (0 : E) 1) (𝓡 n) where

/-- The standard `2`-torus is a closed manifold. -/
example [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 1 + 1)] :
    ClosedManifold ((sphere (0 : E) 1) × (sphere (0 : E) 1)) ((𝓡 2).prod (𝓡 2)) where
-/

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

variable {x y : ℝ} [hxy : Fact (x < y)]

lemma frontier_range_modelWithCornersEuclideanHalfSpace (n : ℕ) [Zero (Fin n)] :
    frontier (range (𝓡∂ n)) = { y | 0 = y 0 } := by
  calc frontier (range (𝓡∂ n))
    _ = frontier ({ y | 0 ≤ y 0 }) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 = y 0 } := frontier_halfspace n

lemma IccLeftChart_boundary : (IccLeftChart x y).extend (𝓡∂ 1) X ∈ frontier (range (𝓡∂ 1)) := by
  rw [IccLeftChart_extend_left_eq]
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  exact rfl

lemma Icc_isBoundaryPoint_left : (𝓡∂ 1).IsBoundaryPoint (X : Icc x y) := by
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt]
  have : chartAt (EuclideanHalfSpace 1) X = IccLeftChart x y := by
    sorry -- follows by construction of the charted space structure; XXX: how can I use this?
  suffices ((IccLeftChart x y).extend (𝓡∂ 1)) X ∈ frontier (range (𝓡∂ 1)) by convert this
  exact IccLeftChart_boundary

lemma IccRightChart_boundary : (IccRightChart x y).extend (𝓡∂ 1) Y ∈ frontier (range (𝓡∂ 1)) := by
  rw [IccRightChart_extend_right_eq]
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  exact rfl

lemma Icc_isBoundaryPoint_right : (𝓡∂ 1).IsBoundaryPoint (Y : Icc x y) := by
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt]
  have : chartAt (EuclideanHalfSpace 1) Y = IccRightChart x y := by
    sorry -- follows by construction of the charted space structure; XXX: how can I use this?
  suffices ((IccRightChart x y).extend (𝓡∂ 1)) Y ∈ frontier (range (𝓡∂ 1)) by convert this
  exact IccRightChart_boundary

lemma Icc_isInteriorPoint_interior {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y) :
    (𝓡∂ 1).IsInteriorPoint p := by
  have : chartAt (EuclideanHalfSpace 1) p = IccLeftChart x y := by
    sorry -- follows by construction of the charted space structure; XXX: how can I use this?
  suffices ((IccLeftChart x y).extend (𝓡∂ 1)) p ∈ interior (range (𝓡∂ 1)) by
    rw [ModelWithCorners.IsInteriorPoint, extChartAt]
    convert this
  -- TODO compute: chart maps this to something positive
  -- then argue that this lies in the interior
  sorry

-- TODO: does this exist already? it ought to... same for the version below
lemma Set.Icc.eq_left_or_interior_or_eq_right {p : ℝ} (hp : p ∈ Set.Icc x y) :
  p = x ∨ (x < p ∧ p < y) ∨ p = y := sorry

lemma Set.Icc.eq_left_or_interior_or_eq_right' (p : Set.Icc x y) :
  p.val = x ∨ (x < p.val ∧ p.val < y) ∨ p.val = y := sorry

-- TODO: does this lemma require proving a lemma such as "interior and boundary are independent of
-- the charted space structure" (which is out of reach with current mathlib)?
lemma boundary_IccManifold : (𝓡∂ 1).boundary (Icc x y) = { X, Y } := by
  ext p
  rcases Set.Icc.eq_left_or_interior_or_eq_right' p with (hp | hp | hp)
  · have : p = X := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_left (mem_insert X {Y})
  · apply iff_of_false
    · -- FIXME; want a lemma p ∈ interior ↔ p ∉ boundary, and vice versa
      rw [ModelWithCorners.boundary_eq_complement_interior, not_mem_compl_iff]
      exact Icc_isInteriorPoint_interior hp
    · rw [mem_insert_iff, mem_singleton_iff]
      -- can this be golfed?
      push_neg
      constructor
      · by_contra h; linarith [congrArg Subtype.val h]
      · by_contra h; linarith [congrArg Subtype.val h]
  · have : p = Y := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_right (mem_insert_of_mem X rfl)

#exit
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [SmoothManifoldWithCorners I M] [BoundarylessManifold I M] [CompactSpace M] [FiniteDimensional ℝ E]

/-- The boundary of the interval [x,y], as a subset of `Icc x y`. -/
def A : Set (Icc x y) := { ⟨x, ⟨le_refl x, by linarith⟩⟩, ⟨y, ⟨by linarith, le_refl y⟩⟩}

/-- A product `M × [x,y]` has boundary `M × {x,y}`. -/
lemma boundary_product [h : Fact (x < y)] :
    (I.prod (𝓡∂ 1)).boundary (M × Icc x y) = Set.prod univ (A hxy) := by
  have : (𝓡∂ 1).boundary (Icc x y) = A hxy := by
    rw [boundary_IccManifold hxy]; simp only [A]
  rw [I.boundary_of_boundaryless_left]
  rw [this]

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
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
    [BoundarylessManifold I M] [FiniteDimensional ℝ E] extends ClosedNManifold n M I where
  f : M → X
  hf : Continuous f

-- We declare these variables *after* the definition above, so `SingularNManifold` can have
-- its current order of arguments.
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {n : ℕ}
  [BoundarylessManifold I M] [CompactSpace M] [FiniteDimensional ℝ E]

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

/-- All data defining a smooth manifold structure on the boundary of a smooth manifold:
a charted space structure on the boundary, a model with corners and a smooth manifold structure.
This need not exist (say, if `M` has corners); if `M` has no boundary or boundary and no corners,
such a structure is in fact canonically induced.
(Proving this requires more advanced results than we currently have.)
-/
structure BoundaryManifoldData (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M] where
  E' : Type*
  [normedAddCommGroup : NormedAddCommGroup E']
  [normedSpace : NormedSpace ℝ E']
  H' : Type*
  [topologicalSpace : TopologicalSpace H']
  charts : ChartedSpace H' (I.boundary M)
  model : ModelWithCorners ℝ E' H'
  smoothManifold : SmoothManifoldWithCorners model (I.boundary M)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners J N]

instance (d : BoundaryManifoldData M I) : TopologicalSpace d.H' := d.topologicalSpace

instance (d : BoundaryManifoldData M I) : NormedAddCommGroup d.E' := d.normedAddCommGroup

instance (d : BoundaryManifoldData M I) : NormedSpace ℝ d.E' := d.normedSpace

instance (d : BoundaryManifoldData M I) : ChartedSpace d.H' (I.boundary M) := d.charts

instance (d : BoundaryManifoldData M I) : SmoothManifoldWithCorners d.model (I.boundary M) :=
  d.smoothManifold

-- In general, constructing `BoundaryManifoldData` requires deep results: some cases and results
-- we can state already. Boundaryless manifolds have nice boundary, as do products.

-- move to `ChartedSpace.lean`
/-- An empty type is a charted space over any topological space. -/
def ChartedSpace.empty (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [IsEmpty M] : ChartedSpace H M where
  atlas := ∅
  chartAt x := False.elim (IsEmpty.false x)
  mem_chart_source x := False.elim (IsEmpty.false x)
  chart_mem_atlas x := False.elim (IsEmpty.false x)

-- move to `InteriorBoundary.lean`
instance [BoundarylessManifold I M] : IsEmpty (I.boundary M) :=
  isEmpty_coe_sort.mpr (ModelWithCorners.Boundaryless.boundary_eq_empty I)

/-- The empty set is a smooth manifold w.r.t. any charted space and model. -/
instance SmoothManifoldWithCorners.empty [IsEmpty M] : SmoothManifoldWithCorners I M := by
  apply smoothManifoldWithCorners_of_contDiffOn
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
  rw [this] at hx
  apply False.elim hx

/-- The empty manifold is boundaryless. -/
instance ModelWithCorners.BoundarylessManifold.of_empty [IsEmpty M] :
    BoundarylessManifold I M where
  isInteriorPoint' x := False.elim (IsEmpty.false x)

/-- The empty manifold is closed. -/
example [IsEmpty M] : ClosedManifold M I where

/- n-dimensionality, however, requires a finite-dimensional model...
-- FIXME: is this the right design decision?
example {n : ℕ} [FiniteDimensional ℝ E] [IsEmpty M] : ClosedNManifold n M I where
  hdim := sorry -/

variable (M) in
/-- If `M` is boundaryless, its boundary manifold data is easy to construct. -/
def BoundaryManifoldData.of_boundaryless [BoundarylessManifold I M] : BoundaryManifoldData M I where
  E' := E
  H' := E
  charts := ChartedSpace.empty E (I.boundary M : Set M)
  model := modelWithCornersSelf ℝ E
  smoothManifold := by
    -- as-is, this errors with "failed to synthesize ChartedSpace E ↑(I.boundary M)" (which is fair)
    -- adding this line errors with "tactic 'apply' failed, failed to assign synthesized instance"
    --haveI := ChartedSpace.empty E (I.boundary M : Set M)
    sorry -- apply SmoothManifoldWithCorners.empty

-- another trivial case: modelWithCornersSelf on euclidean half space!

variable (M I) in
/-- If `M` is boundaryless and `N` has nice boundary, so does `M × N`. -/
def BoundaryManifoldData.prod_of_boundaryless_left [BoundarylessManifold I M]
    (bd : BoundaryManifoldData N J) : BoundaryManifoldData (M × N) (I.prod J) where
  E' := E × bd.E'
  H' := ModelProd H bd.H'
  charts := by
    haveI := bd.charts
    convert prodChartedSpace H M bd.H' (J.boundary N)
    -- TODO: convert between these... mathematically equivalent...
    -- ChartedSpace (ModelProd H bd.H') ↑((I.prod J).boundary (M × N)) =
    --   ChartedSpace (ModelProd H bd.H') (M × ↑(J.boundary N))
    sorry
  model := I.prod bd.model
  smoothManifold := by
    convert SmoothManifoldWithCorners.prod (I := I) (I' := bd.model) M (J.boundary N)
    -- same issue as above
    sorry

-- TODO: fix the details once I found a solution for the above
variable (N J) in
/-- If `M` has nice boundary and `N` is boundaryless, `M × N` has nice boundary. -/
def BoundaryManifoldData.prod_of_boundaryless_right (bd : BoundaryManifoldData M I)
    [BoundarylessManifold J N] : BoundaryManifoldData (M × N) (I.prod J) where
  E' := bd.E' × E'
  H' := ModelProd bd.H' H'
  charts := by
    haveI := bd.charts
    convert prodChartedSpace bd.H' (I.boundary M) H' N
    sorry -- same issue as above
  model := bd.model.prod J
  smoothManifold := sorry -- similar

/-- If `M` is modelled on finite-dimensional Euclidean half-space, it has nice boundary.
Proving this requires knowing homology groups of spheres (or similar). -/
def BoundaryManifoldData.of_Euclidean_halfSpace (n : ℕ) [Zero (Fin n)]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [SmoothManifoldWithCorners (𝓡∂ n) M] : BoundaryManifoldData M (𝓡∂ n) :=
  sorry

-- Another example: if E is a half-space in a Banach space, defined by a linear functional,
-- the boundary of B is also nice: this is proven in Roig-Dominguez' textbook

-- TODO: can/should this be HasNiceBoundary M I J instead?
/--  We say a smooth manifold `M` *has nice boundary* if its boundary (as a subspace)
is a smooth manifold such that the inclusion is smooth. (This condition is *not* automatic, for
instance manifolds with corners violate it, but it is satisfied in most cases of interest.

`HasNiceBoundary d` formalises this: the boundary of the manifold `M` modelled on `I`
has a charted space structure and model (included in `d`) which makes it a smooth manifold,
such that the inclusion `∂M → M` is smooth. -/
class HasNiceBoundary (bd : BoundaryManifoldData M I) where
  /-- The inclusion of `∂M` into `M` is smooth w.r.t. `d`. -/
  smooth_inclusion : ContMDiff bd.model I 1 ((fun ⟨x, _⟩ ↦ x) : (I.boundary M) → M)

/-- A manifold without boundary (trivially) has nice boundary. -/
instance [BoundarylessManifold I M] :
    HasNiceBoundary (BoundaryManifoldData.of_boundaryless (I := I) (M := M)) where
  smooth_inclusion :=
    have : I.boundary M = ∅ := ModelWithCorners.Boundaryless.boundary_eq_empty I
    fun p ↦ False.elim (IsEmpty.false p)

/-- If `M` has nice boundary and `N` is boundaryless, `M × N` also has nice boundary. -/
instance (bd : BoundaryManifoldData M I) [h : HasNiceBoundary bd] [BoundarylessManifold J N] :
    HasNiceBoundary (BoundaryManifoldData.prod_of_boundaryless_right N J bd) where
  smooth_inclusion := by
    let bd'' := BoundaryManifoldData.prod_of_boundaryless_right N J bd
    let I'' := bd''.model
    have h : ContMDiff bd.model I 1 ((fun ⟨x, _⟩ ↦ x) : (I.boundary M) → M) := h.smooth_inclusion
    have h' : ContMDiff J J 1 (fun x ↦ x : N → N) := contMDiff_id
    have : ContMDiff ((bd.model).prod J) (I.prod J) 1
        (fun (⟨x, _⟩, y) ↦ (x, y) : (I.boundary M) × N → M × N) := by
      -- TODO: how to apply prod with just two factors? let aux := ContMDiff.prod h h'
      sorry
    convert this
    -- xxx: add as API lemma, that bd''.model is what we think it is... simp only [bd''.model]
    -- TODO need to rewrite: boundary is the product of boundaries, f factors accordingly...
    sorry

/-- If `M` is boundaryless and `N` has nice boundary, `M × N` also has nice boundary. -/
instance (bd : BoundaryManifoldData N J) [HasNiceBoundary bd] [BoundarylessManifold I M] :
    HasNiceBoundary (BoundaryManifoldData.prod_of_boundaryless_left M I bd) where
  smooth_inclusion := sorry

end HasNiceBoundary

section DisjUnion

-- Let M, M' and M'' be smooth manifolds *over the same space* `H`.
-- TODO: need we also assume their models are literally the same? or on the same space E?
-- or can something weaker suffice?
variable {M : Type*} [TopologicalSpace M] [cm : ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [cm': ChartedSpace H M']
  /-{I' : ModelWithCorners ℝ E H}-/ [SmoothManifoldWithCorners I M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {I'' : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I'' M'']

/-- A partial homeomorphism `M → H` defines a partial homeomorphism `M ⊕ M' → H`. -/
def foo (φ : PartialHomeomorph M H) : PartialHomeomorph (M ⊕ M') H := sorry

def bar (φ : PartialHomeomorph M' H) : PartialHomeomorph (M ⊕ M') H := sorry

def foo' (A : Set (PartialHomeomorph M H)) : Set (PartialHomeomorph (M ⊕ M') H) := { foo φ | φ : A }

def bar' (A : Set (PartialHomeomorph M' H)) : Set (PartialHomeomorph (M ⊕ M') H) := { bar φ | φ : A }

/-- The disjoint union of two charted spaces on `H` is a charted space over `H`. -/
instance ChartedSpace.sum : ChartedSpace H (M ⊕ M') where
  atlas := (foo' cm.atlas) ∪ (bar' cm'.atlas)
  -- others should be easy
  chartAt x := by sorry
    --by_cases h : x ∈ M
    --if x ∈ M then foo (cm.chartAt x) else
  mem_chart_source p := sorry
  chart_mem_atlas := sorry

/-- The disjoint union of two smooth manifolds modelled on `(E,H)`
is a smooth manifold modeled on `(E, H)`. -/
-- XXX. do I really need the same model twice??
instance SmoothManifoldWithCorners.sum : SmoothManifoldWithCorners I (M ⊕ M') := sorry

/-- The inclusion `M → M ⊕ M'` is smooth. -/
lemma ContMDiff.inl : ContMDiff I I ∞ (M' := M ⊕ M') (fun x ↦ Sum.inl x) := sorry

/-- The inclusion `M' → M ⊕ M'` is smooth. -/
lemma ContMDiff.inr : ContMDiff I I ∞ (M' := M ⊕ M') (fun x ↦ Sum.inr x) := sorry

-- TODO: name this nicely; add associativity version as well
-- this seems to be missing for sums of topological spaces (but surely exists abstractly):
variable (I M M') in -- TODO: argument order is weird!
def equivDisjUnionSum : Diffeomorph I I (M ⊕ M') (M' ⊕ M) ∞ := sorry

lemma sdfdsf : (equivDisjUnionSum M I M') ∘ (fun x ↦ Sum.inl x) = (fun x ↦ Sum.inr x) := sorry

lemma hogehoge : (equivDisjUnionSum M I M') ∘ (fun x ↦ Sum.inr x) = (fun x ↦ Sum.inl x) := sorry

end DisjUnion

namespace UnorientedCobordism

-- TODO: for now, assume all manifolds are modelled on the same chart and model space...
-- Is this necessary (`H` presumably is necessary for disjoint unions to work out...)?
-- How would that work in practice? Post-compose with a suitable equivalence of H resp. E?

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  /-{I' : ModelWithCorners ℝ E H}-/ [SmoothManifoldWithCorners I M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  /-{I'' : ModelWithCorners ℝ E H}-/ [SmoothManifoldWithCorners I M''] {n : ℕ}
  [CompactSpace M] [BoundarylessManifold I M]
  [CompactSpace M'] [BoundarylessManifold I M'] [CompactSpace M''] [BoundarylessManifold I M'']
  [CompactSpace M] [FiniteDimensional ℝ E]
  [CompactSpace M'] [FiniteDimensional ℝ E'] [CompactSpace M''] [FiniteDimensional ℝ E'']


/-- An **unoriented cobordism** between two singular `n`-manifolds `(M,f)` and `(N,g)` on `X`
is a compact smooth `n`-manifold `W` with a continuous map `F: W → X`
whose boundary is diffeomorphic to the disjoint union `M ⊔ N` such that `F` restricts to `f`
resp. `g` in the obvious way. -/
structure UnorientedCobordism (s : SingularNManifold X n M I)
    (t : SingularNManifold X n M' I) {W : Type*} [TopologicalSpace W]
    [ChartedSpace H'' W] {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]
    (bd : BoundaryManifoldData W J) [HasNiceBoundary bd] where
  hW : CompactSpace W
  hW' : finrank ℝ E'' = n + 1
  F : W → X
  hF : Continuous F
  /-- The boundary of `W` is diffeomorphic to the disjoint union `M ⊔ M'`. -/
  φ : Diffeomorph bd.model I (J.boundary W) (M ⊕ M') ∞
  /-- `F` restricted to `M ↪ ∂W` equals `f`: this is formalised more nicely as
  `f = F ∘ ι ∘ φ⁻¹ : M → X`, where `ι : ∂W → W` is the inclusion. -/
  hFf : F ∘ ((fun ⟨x, _⟩ ↦ x : J.boundary W → W)) ∘ φ.symm ∘ (fun x ↦ Sum.inl x) = s.f
  /-- `F` restricted to `N ↪ ∂W` equals `g` -/
  hFg : F ∘ ((fun ⟨x, _⟩ ↦ x : J.boundary W → W)) ∘ φ.symm ∘ (fun x ↦ Sum.inr x) = t.f

variable {s : SingularNManifold X n M I}
  {t : SingularNManifold X n M' I} {W : Type*} [TopologicalSpace W] [ChartedSpace H'' W]
  {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]
  {bd : BoundaryManifoldData W J} [HasNiceBoundary bd]

-- TODO: can I remove the `Fact`, concluding the empty set otherwise? or is this not useful?
variable {x y : ℝ} [Fact (x < y)] in
def _root_.boundaryData_IccManifold : BoundaryManifoldData ((Icc x y)) (𝓡∂ 1) := sorry

variable (x y : ℝ) [Fact (x < y)] (M I) in
abbrev foo  : BoundaryManifoldData (M × (Icc x y)) (I.prod (𝓡∂ 1)) :=
  BoundaryManifoldData.prod_of_boundaryless_left (M := M) (I := I)
    (boundaryData_IccManifold (x := x) (y := y))

variable {x y : ℝ} [Fact (x < y)] in
instance : HasNiceBoundary (foo M I x y) := sorry

/-- If `M` is boundaryless, `∂(M × [0,1])` is diffeomorph to the disjoint union `M ⊔ M`. -/
def Diffeomorph.productInterval_sum : Diffeomorph ((foo M I 0 1).model) I
    ((I.prod (𝓡∂ 1)).boundary (M × (Icc (0 : ℝ) 1))) (M ⊕ M') ∞ :=
  sorry

/-- Each singular `n`-manifold `(M,f)` is cobordant to itself. -/
def refl (s : SingularNManifold X n M I) : UnorientedCobordism s s (foo M I 0 1) where
  hW := by infer_instance
  hW' := by rw [finrank_prod, s.hdim, finrank_euclideanSpace_fin]
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst
  φ := Diffeomorph.productInterval_sum
  -- TODO: most of these proofs should become API lemmas about `Diffeomorph.productInterval_sum`
  hFf := sorry
  hFg := sorry

variable (s : SingularNManifold X n M I) (t : SingularNManifold X n M' I)
  {W : Type*} [TopologicalSpace W] [ChartedSpace H'' W]
  {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]
  {bd : BoundaryManifoldData W J} [HasNiceBoundary bd]

/-- Being cobordant is symmetric. -/
def symm (φ : UnorientedCobordism s t bd) : UnorientedCobordism t s bd where
  hW := φ.hW
  hW' := φ.hW'
  F := φ.F
  hF := φ.hF
  φ := Diffeomorph.trans φ.φ (equivDisjUnionSum M I M')
  -- apply sdfdsf resp. hogehoge, and combine with φ.hFf and φ.hFg
  hFf := sorry
  hFg := sorry

-- Fleshing out the details for transitivity will take us too far: we merely sketch the necessary
-- pieces.
section transSketch

variable {u : SingularNManifold X n M'' I}
  {W' : Type*} [TopologicalSpace W'] [ChartedSpace H''' W']
  {J' : ModelWithCorners ℝ E''' H'''} [SmoothManifoldWithCorners J' W']
  {bd' : BoundaryManifoldData W' J'} [HasNiceBoundary bd']

-- Idea: glue the cobordisms W and W' along their common boundary M',
-- as identified by the diffeomorphism W → M' ← W'.
-- This could be formalised as an adjunction/attaching maps: these are a special case of pushouts
-- (in the category of topological spaces).
-- mathlib has abstract pushouts (and proved that TopCat has them);
-- `Topology/Category/TopCat/Limits/Pullbacks.lean` provides a concrete description of pullbacks
-- in TopCat. A good next step would be to adapt this argument to pushouts, and use this here.
-- TODO: can I remove the s and t variables from this definition?
def glue (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') : Type* := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    TopologicalSpace (glue s t φ ψ) := sorry

-- This and the next item require the collar neighbourhood theorem.
instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    ChartedSpace H (glue s t φ ψ) := sorry

-- TODO: can I remove the s and t variables from this one?
def glueModel (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    ModelWithCorners ℝ E H := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    SmoothManifoldWithCorners (glueModel s t φ ψ) (glue s t φ ψ) := sorry

-- TODO: can I remove the s and t variables from this one?
def glueBoundaryData (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    BoundaryManifoldData (glue s t φ ψ) (glueModel s t φ ψ) := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    HasNiceBoundary (glueBoundaryData s t φ ψ) := sorry

noncomputable def trans (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    UnorientedCobordism s u (glueBoundaryData s t φ ψ) where
  hW := sorry
  hW' := sorry
  F := sorry
  hF := sorry
  φ := sorry
  hFf := sorry
  hFg := sorry

end transSketch

end UnorientedCobordism

-- how to encode this in Lean?
-- Two singular `n`-manifolds are cobordant iff there exists a smooth cobordism between them.
-- The unoriented `n`-bordism group `Ω_n^O(X)` of `X` is the set of all equivalence classes
-- of singular n-manifolds up to bordism.
-- then: functor between these...

-- prove: every element in Ω_n^O(X) has order two
