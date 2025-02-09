/-
Copyright (c) 2024 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/

import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Logic.Equiv.PartialEquiv

/-!
# CW complexes

This file defines (relative) CW complexes and proves basic properties about them.

A CW complex is a topological space that is made by gluing closed disks of different dimensions
together.

## Main definitions
* `RelCWComplex C D`: the class of CW structures on a subspace `C` relative to a base set
  `D` of a topological space `X`.
* `CWComplex C`: an abbreviation for `RelCWComplex C ∅`. The class of CW structures on a
  subspace `C` of the topological space `X`.
* `openCell n`: indexed family of all open cells of dimension `n`.
* `closedCell n`: indexed family of all closed cells of dimension `n`.
* `cellFrontier n`: indexed family of the boundaries of cells of dimension `n`.
* `skeleton C n`: the `n`-skeleton of the (relative) CW complex `C`.

## Main statements
* `iUnion_openCell_eq_skeleton`: the skeletons can also be seen as a union of open cells.
* `cellFrontier_subset_finite_openCell`: the edge of a cell is contained in a finite union of
  open cells of a lower dimension.

## Implementation notes
* We use the historical definition of CW complexes, due to Whitehead: a CW complex is a collection
  of cells with attaching maps - all cells are subspaces of one ambient topological space.
  This way, we avoid having to work with a lot of different topological spaces.
  On the other hand, it requires the union of all cells to be closed.
  If that is not the case, you need to consider that union as a subspace of itself.
* The definition `RelCWComplex` does not require `X` to be a Hausdorff space.
  A lot of the lemmas will however require this property.
* This definition is a class to ease working with different constructions and their properties.
  Overall this means the being a CW complex is treated more like a property than data.
* For statements, the auxiliary construction `skeletonLT` is preferred over `skeleton` as it makes
  the base case of inductions easier. The statement about `skeleton` should then be derived from the
  one about `skeletonLT`.

## References
* [A. Hatcher, *Algebraic Topology*][hatcher02]
-/

noncomputable section

open Metric Set

namespace Topology

/-- A CW complex of a topological space `X` relative to another subspace `D` is the data of its
*`n`-cells* `cell n i` for each `n : ℕ` along with *attaching maps* that satisfy a number of
properties with the most important being closure-finiteness (`mapsto`) and weak topology
(`closed'`). Note that this definition requires `C` and `D` to be closed subspaces.
If `C` is not closed choose `X` to be `C`. -/
class RelCWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) (D : outParam (Set X)) where
  /-- The indexing type of the cells of dimension `n`. -/
  cell (n : ℕ) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
  This map is a bijection when restricting to `ball 0 1`, where we consider `(Fin n → ℝ)`
  endowed with the maximum metric. -/
  map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  /-- The source of every charactersitic map of dimension `n` is
  `(ball 0 1 : Set (Fin n → ℝ))`. -/
  source_eq (n : ℕ) (i : cell n) : (map n i).source = ball 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`. -/
  continuousOn (n : ℕ) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `ball 0 1` is continuous on the image. -/
  continuousOn_symm (n : ℕ) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `RelCWComplex.pairwiseDisjoint` or
  `RelCWComplex.disjoint_openCell_of_ne` instead. -/
  pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  /-- All open cells are disjoint with the base. Use `RelCWComplex.disjointBase` instead. -/
  disjointBase' (n : ℕ) (i : cell n) : Disjoint (map n i '' ball 0 1) D
  /-- The boundary of a cell is contained in a finite union of closed cells of a lower dimension.
  Use `RelCWComplex.cellFrontier_subset_finite_closedCell` instead. -/
  mapsto (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
  every closed cell and `D` is closed. Use `RelCWComplex.closed` instead. -/
  closed' (A : Set X) (asubc : A ⊆ C) :
    ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A
  /-- The base `D` is closed. -/
  isClosedBase : IsClosed D
  /-- The union of all closed cells equals `C`. Use `RelCWComplex.union` instead. -/
  union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

/-- Characterizing when a subspace `C` of a topological space `X` is a CW complex. Note that this
requires `C` to be closed. If `C` is not closed choose `X` to be `C`. -/
abbrev CWComplex {X : Type*} [TopologicalSpace X] (C : Set X) := RelCWComplex C ∅

/-- A constructor for `CWComplex`. -/
def CWComplex.mk.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : ℕ → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsto: ∀ n i, ∃ I : Π m, Finset (cell m),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X), (asubc : A ⊆ C) →
      (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A)
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) : CWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := by simp only [disjoint_empty, implies_true]
  mapsto := by simpa only [empty_union]
  closed' := by simpa only [inter_empty, isClosed_empty, and_true]
  isClosedBase := isClosed_empty
  union' := by simpa only [empty_union]

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

/-- The open `n`-cell given by the index `i`. Use this instead of `map n i '' ball 0 1` whenever
possible. -/
def RelCWComplex.openCell [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X := map n i '' ball 0 1

/-- The closed `n`-cell given by the index `i`. Use this instead of `map n i '' closedBall 0 1`
whenever possible. -/
def RelCWComplex.closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X :=
  map n i '' closedBall 0 1

/-- The boundary of the `n`-cell given by the index `i`. Use this instead of `map n i '' sphere 0 1`
whenever possible. -/
def RelCWComplex.cellFrontier [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X :=
  map n i '' sphere 0 1

namespace CWComplex

export RelCWComplex (cell map source_eq continuousOn continuousOn_symm mapsto isClosedBase openCell
  closedCell cellFrontier)

end CWComplex

lemma CWComplex.mapsto [CWComplex C] (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1) := by
  have := RelCWComplex.mapsto n i
  simp_rw [empty_union] at this
  exact this

lemma RelCWComplex.pairwiseDisjoint [RelCWComplex C D] :
    (univ : Set (Σ n, cell C n)).PairwiseDisjoint (fun ni ↦ openCell ni.1 ni.2) :=
  RelCWComplex.pairwiseDisjoint'

lemma RelCWComplex.disjointBase [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    Disjoint (openCell n i) D :=
  RelCWComplex.disjointBase' n i

lemma RelCWComplex.disjoint_openCell_of_ne [RelCWComplex C D] {n m : ℕ} {i : cell C n}
    {j : cell C m} (ne : (⟨n, i⟩ : Σ n, cell C n) ≠ ⟨m, j⟩) : openCell n i ∩ openCell m j = ∅ := by
  have := pairwiseDisjoint (C := C) (D := D)
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_iff_inter_eq_empty] at this
  exact this (mem_univ _) (mem_univ _) ne

lemma RelCWComplex.cellFrontier_subset_base_union_finite_closedCell [RelCWComplex C D]
    (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m), cellFrontier n i ⊆
    D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j := by
  rcases mapsto n i with ⟨I, hI⟩
  use I
  rw [mapsTo'] at hI
  exact hI

lemma CWComplex.cellFrontier_subset_finite_closedCell [CWComplex C] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m), cellFrontier n i ⊆ ⋃ (m < n) (j ∈ I m), closedCell m j := by
  rcases RelCWComplex.mapsto n i with ⟨I, hI⟩
  use I
  rw [mapsTo', empty_union] at hI
  exact hI

lemma RelCWComplex.union [RelCWComplex C D] : D ∪ ⋃ (n : ℕ) (j : cell C n), closedCell n j = C :=
  RelCWComplex.union'

lemma CWComplex.union [CWComplex C] : ⋃ (n : ℕ) (j : cell C n), closedCell n j = C := by
  have := RelCWComplex.union' (C := C) (D := ∅)
  rw [empty_union] at this
  exact this

lemma RelCWComplex.openCell_subset_closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    openCell n i ⊆ closedCell n i := image_mono Metric.ball_subset_closedBall

lemma RelCWComplex.cellFrontier_subset_closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    cellFrontier n i ⊆ closedCell n i := image_mono Metric.sphere_subset_closedBall

lemma RelCWComplex.cellFrontier_union_openCell_eq_closedCell [RelCWComplex C D] (n : ℕ)
    (i : cell C n) : cellFrontier n i ∪ openCell n i = closedCell n i := by
  rw [cellFrontier, openCell, closedCell, ← image_union]
  congrm map n i '' ?_
  exact sphere_union_ball

lemma RelCWComplex.map_zero_mem_openCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    map n i 0 ∈ openCell n i := by
  apply mem_image_of_mem
  simp only [mem_ball, dist_self, zero_lt_one]

lemma RelCWComplex.map_zero_mem_closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    map n i 0 ∈ closedCell n i :=
  openCell_subset_closedCell _ _ (map_zero_mem_openCell _ _)

/-- A non-standard definition of the `n`-skeleton of a CW complex for `n ∈ ℕ ∪ {∞}`.
This allows the base case of induction to be about the base instead of being about the union of
the base and some points.
The standard `skeleton` is defined in terms of `skeletonLT`. `skeletonLT` is preferred
in statements. You should then derive the statement about `skeleton`. -/
def RelCWComplex.skeletonLT (C : Set X) {D : Set X} [RelCWComplex C D] (n : ℕ∞) : Set X :=
  D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C m), closedCell m j

/-- The `n`-skeleton of a CW complex, for `n ∈ ℕ ∪ {∞}`. For statements use `skeletonLT` instead
and then derive the statement about `skeleton`. -/
def RelCWComplex.skeleton (C : Set X) {D : Set X} [RelCWComplex C D] (n : ℕ∞) : Set X :=
  skeletonLT C (n + 1)

namespace CWComplex

export RelCWComplex (skeletonLT skeleton)

end CWComplex

lemma RelCWComplex.skeletonLT_zero_eq_base [RelCWComplex C D] : skeletonLT C 0 = D := by
  simp only [skeletonLT, ENat.not_lt_zero, iUnion_of_empty, iUnion_empty, union_empty]

lemma CWComplex.skeletonLT_zero_eq_empty [CWComplex C] : skeletonLT C 0 = ∅ :=
    RelCWComplex.skeletonLT_zero_eq_base

lemma RelCWComplex.isCompact_closedCell [RelCWComplex C D] {n : ℕ} {i : cell C n} :
    IsCompact (closedCell n i) :=
  (isCompact_closedBall _ _).image_of_continuousOn (continuousOn n i)

lemma RelCWComplex.isClosed_closedCell [RelCWComplex C D] [T2Space X] {n : ℕ} {i : cell C n} :
  IsClosed (closedCell n i) := isCompact_closedCell.isClosed

lemma RelCWComplex.isCompact_cellFrontier [RelCWComplex C D] {n : ℕ} {i : cell C n} :
    IsCompact (cellFrontier n i) :=
  (isCompact_sphere _ _).image_of_continuousOn ((continuousOn n i).mono sphere_subset_closedBall)

lemma RelCWComplex.isClosed_cellFrontier [RelCWComplex C D] [T2Space X] {n : ℕ} {i : cell C n} :
    IsClosed (cellFrontier n i) :=
  isCompact_cellFrontier.isClosed

lemma RelCWComplex.closure_openCell_eq_closedCell [RelCWComplex C D] [T2Space X] {n : ℕ}
    {j : cell C n} : closure (openCell n j) = closedCell n j := by
  apply subset_antisymm (isClosed_closedCell.closure_subset_iff.2 (openCell_subset_closedCell n j))
  rw [closedCell, ← closure_ball 0 (by exact one_ne_zero)]
  apply ContinuousOn.image_closure
  rw [closure_ball 0 (by exact one_ne_zero)]
  exact continuousOn n j

lemma RelCWComplex.closed (C : Set X) {D : Set X} [RelCWComplex C D] [T2Space X] (A : Set X)
    (asubc : A ⊆ C) :
    IsClosed A ↔ (∀ n (j : cell C n), IsClosed (A ∩ closedCell n j)) ∧ IsClosed (A ∩ D) := by
  refine ⟨?_, closed' A asubc⟩
  exact fun closedA ↦ ⟨fun _ _ ↦ closedA.inter isClosed_closedCell, closedA.inter (isClosedBase C)⟩

lemma CWComplex.closed (C : Set X) [CWComplex C] [T2Space X] (A : Set X) (asubc : A ⊆ C) :
    IsClosed A ↔ ∀ n (j : cell C n), IsClosed (A ∩ closedCell n j) := by
  have := RelCWComplex.closed C A asubc
  simp_all

@[simp] lemma RelCWComplex.skeletonLT_top [RelCWComplex C D] : skeletonLT C ⊤ = C := by
  simp [skeletonLT, union]

@[simp] lemma RelCWComplex.skeleton_top [RelCWComplex C D] : skeleton C ⊤ = C := skeletonLT_top

lemma RelCWComplex.skeletonLT_mono [RelCWComplex C D] {n m : ℕ∞} (h : m ≤ n) :
    skeletonLT C m ⊆ skeletonLT C n := by
  apply union_subset_union_right
  intro x xmem
  simp_rw [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨l , lltm, xmeml⟩ := xmem
  exact ⟨l, lt_of_lt_of_le lltm h, xmeml⟩

lemma RelCWComplex.skeleton_mono [RelCWComplex C D] {n m : ℕ∞} (h : m ≤ n) :
    skeleton C m ⊆ skeleton C n :=
  skeletonLT_mono (add_le_add_right h 1)

lemma RelCWComplex.skeletonLT_subset_complex [RelCWComplex C D] {n : ℕ∞} : skeletonLT C n ⊆ C := by
  simp_rw [← skeletonLT_top (C := C) (D := D)]
  exact skeletonLT_mono (OrderTop.le_top n)

lemma RelCWComplex.skeleton_subset_complex [RelCWComplex C D] {n : ℕ∞} :
    skeleton C n ⊆ C :=
  skeletonLT_subset_complex

lemma RelCWComplex.closedCell_subset_skeletonLT [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ skeletonLT C (n + 1) := by
  intro x xmem
  right
  simp_rw [mem_iUnion, exists_prop]
  refine ⟨n, (by norm_cast; exact lt_add_one n), ⟨j,xmem⟩⟩

lemma RelCWComplex.closedCell_subset_skeleton [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ skeleton C n :=
  closedCell_subset_skeletonLT n j

lemma RelCWComplex.closedCell_subset_complex [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ C :=
  (closedCell_subset_skeleton n j).trans
    (by simp_rw [← skeleton_top (C := C) (D := D)]; exact skeleton_mono le_top)

lemma RelCWComplex.openCell_subset_skeletonLT [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ skeletonLT C (n + 1) :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_skeletonLT _ _ )

lemma RelCWComplex.openCell_subset_skeleton [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ skeleton C n :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_skeleton _ _)

lemma RelCWComplex.openCell_subset_complex [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ C := by
  apply subset_trans (openCell_subset_skeleton _ _)
    (by simp_rw [← skeleton_top (C := C) (D := D)]; exact skeleton_mono le_top)

lemma RelCWComplex.cellFrontier_subset_skeletonLT [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    cellFrontier n j ⊆ skeletonLT C n := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n j
  apply subset_trans hI
  apply union_subset_union_right
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨i, iltn, j, _, xmem⟩ := xmem
  exact ⟨i, by norm_cast, j, xmem⟩

lemma RelCWComplex.cellFrontier_subset_skeleton [RelCWComplex C D] (n : ℕ) (j : cell C (n + 1)) :
    cellFrontier (n + 1) j ⊆ skeleton C n :=
  cellFrontier_subset_skeletonLT _ _

lemma RelCWComplex.iUnion_cellFrontier_subset_skeletonLT [RelCWComplex C D] (l : ℕ) :
    ⋃ (j : cell C l), cellFrontier l j ⊆ skeletonLT C l :=
  iUnion_subset (fun _ ↦ cellFrontier_subset_skeletonLT _ _)

lemma RelCWComplex.iUnion_cellFrontier_subset_skeleton [RelCWComplex C D] (l : ℕ) :
    ⋃ (j : cell C l), cellFrontier l j ⊆ skeleton C l :=
  (iUnion_cellFrontier_subset_skeletonLT l).trans (skeletonLT_mono le_self_add)

lemma RelCWComplex.closedCell_zero_eq_singleton [RelCWComplex C D] {j : cell C 0} :
    closedCell 0 j = {map 0 j ![]} := by
  simp [closedCell, Matrix.empty_eq]

lemma RelCWComplex.openCell_zero_eq_singleton [RelCWComplex C D] {j : cell C 0} :
    openCell 0 j = {map 0 j ![]} := by
  simp [openCell, Matrix.empty_eq]

lemma RelCWComplex.cellFrontier_zero_eq_empty [RelCWComplex C D] {j : cell C 0} :
    cellFrontier 0 j = ∅ := by
  simp [cellFrontier, sphere_eq_empty_of_subsingleton]

lemma RelCWComplex.base_subset_skeletonLT [RelCWComplex C D] (n : ℕ∞) : D ⊆ skeletonLT C n :=
  subset_union_left

lemma RelCWComplex.base_subset_skeleton [RelCWComplex C D] (n : ℕ∞) : D ⊆ skeleton C n :=
  base_subset_skeletonLT (n + 1)

lemma RelCWComplex.base_subset_complex [RelCWComplex C D] : D ⊆ C := by
  simp_rw [← skeleton_top (C := C) (D := D)]
  exact base_subset_skeleton ⊤

namespace CWComplex

export RelCWComplex (pairwiseDisjoint disjoint_openCell_of_ne openCell_subset_closedCell
  cellFrontier_subset_closedCell cellFrontier_union_openCell_eq_closedCell map_zero_mem_openCell
  map_zero_mem_closedCell isCompact_closedCell isClosed_closedCell isCompact_cellFrontier
  isClosed_cellFrontier closure_openCell_eq_closedCell skeletonLT_top skeleton_top skeletonLT_mono
  skeleton_mono skeletonLT_subset_complex skeleton_subset_complex closedCell_subset_skeletonLT
  closedCell_subset_skeleton closedCell_subset_complex openCell_subset_skeletonLT
  openCell_subset_skeleton
  openCell_subset_complex cellFrontier_subset_skeletonLT cellFrontier_subset_skeleton
  iUnion_cellFrontier_subset_skeletonLT iUnion_cellFrontier_subset_skeleton
  closedCell_zero_eq_singleton
  openCell_zero_eq_singleton cellFrontier_zero_eq_empty)

end CWComplex

end Topology
