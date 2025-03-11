/-
Copyright (c) 2024 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/

import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.MetricSpace.ProperSpace.Real

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
  Overall this means that being a CW complex is treated more like a property than data.
* The natural number is explicit in `openCell`, `closedCell` and `cellFrontier` because `cell n` and
  `cell m` might be the same type in an explicit CW complex even when `n` and `m` are different.
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
properties with the most important being closure-finiteness (`mapsTo`) and weak topology
(`closed'`). Note that this definition requires `C` and `D` to be closed subspaces.
If `C` is not closed choose `X` to be `C`. -/
class RelCWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) (D : outParam (Set X)) where
  /-- The indexing type of the cells of dimension `n`. -/
  cell (n : ℕ) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
  This map is a bijection when restricting to `ball 0 1`, where we consider `(Fin n → ℝ)`
  endowed with the maximum metric. -/
  map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  /-- The source of every characteristic map of dimension `n` is
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
  mapsTo (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
  every closed cell and `D` is closed. Use `RelCWComplex.closed` instead. -/
  closed' (A : Set X) (asubc : A ⊆ C) :
    ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A
  /-- The base `D` is closed. -/
  isClosedBase : IsClosed D
  /-- The union of all closed cells equals `C`. Use `RelCWComplex.union` instead. -/
  union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

@[deprecated (since := "2025-02-20")] alias
RelCWComplex.mapsto := Topology.RelCWComplex.mapsTo

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
    (mapsTo: ∀ n i, ∃ I : Π m, Finset (cell m),
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
  mapsTo := by simpa only [empty_union]
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

export RelCWComplex (cell map source_eq continuousOn continuousOn_symm mapsTo isClosedBase openCell
  closedCell cellFrontier)

end CWComplex

lemma CWComplex.mapsTo [CWComplex C] (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1) := by
  have := RelCWComplex.mapsTo n i
  simp_rw [empty_union] at this
  exact this

@[deprecated (since := "2025-02-20")] alias
CWComplex.mapsto := Topology.CWComplex.mapsTo

lemma RelCWComplex.pairwiseDisjoint [RelCWComplex C D] :
    (univ : Set (Σ n, cell C n)).PairwiseDisjoint (fun ni ↦ openCell ni.1 ni.2) :=
  RelCWComplex.pairwiseDisjoint'

lemma RelCWComplex.disjointBase [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    Disjoint (openCell n i) D :=
  RelCWComplex.disjointBase' n i

lemma RelCWComplex.disjoint_openCell_of_ne [RelCWComplex C D] {n m : ℕ} {i : cell C n}
    {j : cell C m} (ne : (⟨n, i⟩ : Σ n, cell C n) ≠ ⟨m, j⟩) :
    Disjoint (openCell n i) (openCell m j) :=
  pairwiseDisjoint (mem_univ _) (mem_univ _) ne

lemma RelCWComplex.cellFrontier_subset_base_union_finite_closedCell [RelCWComplex C D]
    (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m), cellFrontier n i ⊆
    D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j := by
  rcases mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo'] at hI
  exact hI

lemma CWComplex.cellFrontier_subset_finite_closedCell [CWComplex C] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m), cellFrontier n i ⊆ ⋃ (m < n) (j ∈ I m), closedCell m j := by
  rcases RelCWComplex.mapsTo n i with ⟨I, hI⟩
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

lemma RelCWComplex.skeletonLT_monotone [RelCWComplex C D] : Monotone (skeletonLT C) :=
  fun _ _ h ↦ skeletonLT_mono h

lemma RelCWComplex.skeleton_mono [RelCWComplex C D] {n m : ℕ∞} (h : m ≤ n) :
    skeleton C m ⊆ skeleton C n :=
  skeletonLT_mono (add_le_add_right h 1)

lemma RelCWComplex.skeleton_monotone [RelCWComplex C D] : Monotone (skeleton C) :=
  fun _ _ h ↦ skeleton_mono h

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

lemma RelCWComplex.cellFrontier_subset_complex [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    cellFrontier n j ⊆ C :=
  (cellFrontier_subset_closedCell n j).trans (closedCell_subset_complex n j)

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

lemma RelCWComplex.isClosed [T2Space X] [RelCWComplex C D] : IsClosed C := by
  rw [closed C C (by rfl)]
  constructor
  · intros
    rw [inter_eq_right.2 (closedCell_subset_complex _ _)]
    exact isClosed_closedCell
  · rw [inter_eq_right.2 base_subset_complex]
    exact isClosedBase C

lemma RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ [RelCWComplex C D]
    (n : ℕ) : skeletonLT C n ∪ ⋃ (j : cell C n), closedCell n j = skeletonLT C (n + 1)  := by
  rw [skeletonLT, skeletonLT, union_assoc]
  congr
  norm_cast
  exact (biUnion_lt_succ _ _).symm

lemma RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ [RelCWComplex C D] (n : ℕ) :
    skeleton C n ∪ ⋃ (j : cell C (n + 1)), closedCell (n + 1) j = skeleton C (n + 1) :=
  skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ _

/-- A version of the definition of `skeletonLT` with open cells. -/
lemma RelCWComplex.iUnion_openCell_eq_skeletonLT [RelCWComplex C D] (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C m), openCell m j = skeletonLT C n := by
  apply subset_antisymm
  · apply union_subset
    · exact base_subset_skeletonLT n
    · apply iUnion₂_subset fun m hm ↦ iUnion_subset fun j ↦ ?_
      exact (openCell_subset_skeletonLT m j).trans (skeletonLT_mono (Order.add_one_le_of_lt hm))
  · rw [skeletonLT]
    apply union_subset subset_union_left
    refine iUnion₂_subset fun m hm ↦ iUnion_subset fun j ↦ ?_
    rw [← cellFrontier_union_openCell_eq_closedCell]
    apply union_subset
    · induction' m using Nat.case_strong_induction_on with m hm'
      · simp [cellFrontier_zero_eq_empty]
      · obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (m + 1) j
        apply hI.trans
        apply union_subset subset_union_left
        apply iUnion₂_subset fun l hl ↦ iUnion₂_subset fun i _ ↦ ?_
        rw [← cellFrontier_union_openCell_eq_closedCell]
        apply union_subset
        · exact (hm' l (Nat.le_of_lt_succ hl) ((ENat.coe_lt_coe.2 hl).trans hm) i)
        · apply subset_union_of_subset_right
          exact subset_iUnion₂_of_subset l ((ENat.coe_lt_coe.2 hl).trans hm) <| subset_iUnion _ i
    · exact subset_union_of_subset_right (subset_iUnion₂_of_subset m hm (subset_iUnion _ j)) _

lemma CWComplex.iUnion_openCell_eq_skeletonLT [CWComplex C] (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n) (j : cell C m), openCell m j = skeletonLT C n := by
  rw [← RelCWComplex.iUnion_openCell_eq_skeletonLT, empty_union]

lemma RelCWComplex.iUnion_openCell_eq_skeleton [RelCWComplex C D] (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n + 1) (j : cell C m), openCell m j = skeleton C n :=
  iUnion_openCell_eq_skeletonLT _

lemma CWComplex.iUnion_openCell_eq_skeleton [CWComplex C] (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n + 1) (j : cell C m), openCell m j = skeleton C n :=
  iUnion_openCell_eq_skeletonLT _

lemma RelCWComplex.union_iUnion_openCell_eq_complex [RelCWComplex C D] :
    D ∪ ⋃ (n : ℕ) (j : cell C n), openCell n j = C := by
  simp only [← skeletonLT_top, ← iUnion_openCell_eq_skeletonLT, ENat.coe_lt_top, iUnion_true]

lemma CWComplex.iUnion_openCell_eq_complex [CWComplex C] :
    ⋃ (n : ℕ) (j : cell C n), openCell n j = C := by
  simpa using RelCWComplex.union_iUnion_openCell_eq_complex (C := C) (D := ∅)

/-- The contrapositive of `disjoint_openCell_of_ne`. -/
lemma RelCWComplex.eq_of_not_disjoint_openCell [RelCWComplex C D] {n : ℕ} {j : cell C n} {m : ℕ}
    {i : cell C m} (h : ¬ Disjoint (openCell n j) (openCell m i)) :
    (⟨n, j⟩ : (Σ n, cell C n)) = ⟨m, i⟩ := by
  contrapose! h
  exact disjoint_openCell_of_ne h

lemma RelCWComplex.mem_skeletonLT_iff [RelCWComplex C D] {n : ℕ∞} {x : X} :
    x ∈ skeletonLT C n ↔ x ∈ D ∨ ∃ (m : ℕ) (_ : m < n) (j : cell C m), x ∈ openCell m j := by
  simp [← iUnion_openCell_eq_skeletonLT]

lemma CWComplex.mem_skeletonLT_iff [CWComplex C] {n : ℕ∞} {x : X} :
    x ∈ skeletonLT C n ↔ ∃ (m : ℕ) (_ : m < n) (j : cell C m), x ∈ openCell m j := by
  simp [← iUnion_openCell_eq_skeletonLT]

lemma RelCWComplex.mem_skeleton_iff [RelCWComplex C D] {n : ℕ∞} {x : X} :
    x ∈ skeleton C n ↔ x ∈ D ∨ ∃ (m : ℕ) (_ : m ≤ n) (j : cell C m), x ∈ openCell m j := by
  rw [skeleton, mem_skeletonLT_iff]
  suffices ∀ (m : ℕ), m < n + 1 ↔ m ≤ n by simp_rw [this]
  intro m
  cases n
  · simp
  · rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt, Nat.cast_le, Order.lt_add_one_iff]

lemma CWComplex.exists_mem_openCell_of_mem_skeleton [CWComplex C] {n : ℕ∞} {x : X} :
    x ∈ skeleton C n ↔ ∃ (m : ℕ) (_ : m ≤ n) (j : cell C m), x ∈ openCell m j := by
  rw [RelCWComplex.mem_skeleton_iff, mem_empty_iff_false, false_or]

/-- A skeleton and an open cell of a higher dimension are disjoint. -/
lemma RelCWComplex.disjoint_skeletonLT_openCell [RelCWComplex C D] {n : ℕ∞} {m : ℕ}
    {j : cell C m} (hnm : n ≤ m) : Disjoint (skeletonLT C n) (openCell m j) := by
  -- This is a consequence of `iUnion_openCell_eq_skeletonLT` and `disjoint_openCell_of_ne`
  simp_rw [← iUnion_openCell_eq_skeletonLT, disjoint_union_left, disjoint_iUnion_left]
  refine ⟨(disjointBase m j).symm, ?_⟩
  intro l hln i
  apply disjoint_openCell_of_ne
  intro
  simp_all only [Sigma.mk.inj_iff]
  exact (lt_self_iff_false m).mp (ENat.coe_lt_coe.1 (hln.trans_le hnm))

/-- A skeleton and an open cell of a higher dimension are disjoint. -/
lemma RelCWComplex.disjoint_skeleton_openCell [RelCWComplex C D] {n : ℕ∞} {m : ℕ}
    {j : cell C m} (nlem : n < m) : Disjoint (skeleton C n) (openCell m j) :=
  disjoint_skeletonLT_openCell (Order.add_one_le_of_lt nlem)

lemma RelCWComplex.disjoint_base_iUnion_openCell [RelCWComplex C D] :
    Disjoint D (⋃ (n : ℕ) (j : cell C n), openCell n j) := by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, iUnion_eq_empty]
  intro n i
  rw [inter_comm, (disjointBase n i).inter_eq]

lemma RelCWComplex.disjoint_interior_base_closedCell [T2Space X] [RelCWComplex C D] {n : ℕ}
    {j : cell C n} : Disjoint (interior D) (closedCell n j) := by
  rw [disjoint_iff_inter_eq_empty]
  by_contra h
  push_neg at h
  rw [← closure_openCell_eq_closedCell, inter_comm,
    closure_inter_open_nonempty_iff isOpen_interior] at h
  rcases h with ⟨x, xmemcell, xmemD⟩
  suffices x ∈ skeletonLT C 0 ∩ openCell n j by
    rwa [(disjoint_skeletonLT_openCell n.cast_nonneg').inter_eq] at this
  exact ⟨base_subset_skeletonLT 0 (interior_subset xmemD), xmemcell⟩

lemma RelCWComplex.disjoint_interior_base_iUnion_closedCell [T2Space X] [RelCWComplex C D] :
    Disjoint (interior D) (⋃ (n : ℕ) (j : cell C n), closedCell n j) := by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, disjoint_interior_base_closedCell.inter_eq,
    iUnion_empty]

/-- A skeleton intersected with a closed cell of a higher dimension is the skeleton intersected with
the boundary of the cell. -/
lemma RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier [RelCWComplex C D]
    {n : ℕ∞} {m : ℕ} {j : cell C m} (hnm : n ≤ m) :
    skeletonLT C n ∩ closedCell m j = skeletonLT C n ∩ cellFrontier m j := by
  refine subset_antisymm ?_ (inter_subset_inter_right _ (cellFrontier_subset_closedCell _ _))
  rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
  apply union_subset (by rfl)
  rw [(disjoint_skeletonLT_openCell hnm).inter_eq]
  exact empty_subset _

/-- Version of `skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier` using `skeleton`. -/
lemma RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier [RelCWComplex C D]
    {n : ℕ∞} {m : ℕ} {j : cell C m} (hnm : n < m) :
    skeleton C n ∩ closedCell m j = skeleton C n ∩ cellFrontier m j :=
  skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier (Order.add_one_le_of_lt hnm)

/-- If for all `m ≤ n` and every `i : cell C m` the intersection `A ∩ closedCell m j` is closed
and `A ∩ D` is closed then `A ∩ cellFrontier (n + 1) j` is closed for every
`j : cell C (n + 1)`. -/
lemma RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} {n : ℕ} (hn : ∀ m ≤ n, ∀ (j : cell C m),
    IsClosed (A ∩ closedCell m j)) (j : cell C (n + 1)) (hD : IsClosed (A ∩ D)) :
    IsClosed (A ∩ cellFrontier (n + 1) j) := by
  -- this is a consequence of `cellFrontier_subset_base_union_finite_closedCell`
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (n + 1) j
  rw [← inter_eq_right.2 hI, ← inter_assoc]
  refine IsClosed.inter ?_ isClosed_cellFrontier
  simp_rw [inter_union_distrib_left, inter_iUnion,
    ← iUnion_subtype (fun m ↦ m < n + 1) (fun m ↦ ⋃ i ∈ I m, A ∩ closedCell m i)]
  apply hD.union
  apply isClosed_iUnion_of_finite
  intro ⟨m, mlt⟩
  rw [← iUnion_subtype (fun i ↦ i ∈ I m) (fun i ↦ A ∩ closedCell m i.1)]
  exact isClosed_iUnion_of_finite (fun ⟨j, _⟩ ↦ hn m (Nat.le_of_lt_succ mlt) j)

lemma CWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
    [CWComplex C] [T2Space X] {A : Set X} {n : ℕ} (hn : ∀ m ≤ n, ∀ (j : cell C m),
    IsClosed (A ∩ closedCell m j)) (j : cell C (n + 1)) :
    IsClosed (A ∩ cellFrontier (n + 1) j) :=
  RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j
    (by simp only [inter_empty, isClosed_empty])

/-- If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed then
`A` is closed. -/
lemma RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} (hAC : A ⊆ C) (hDA : IsClosed (A ∩ D))
    (h : ∀ n (_ : 0 < n), ∀ (j : cell C n),
    IsClosed (A ∩ openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A := by
  rw [closed C A hAC]
  refine ⟨?_, hDA⟩
  intro n j
  induction' n using Nat.case_strong_induction_on with n hn
  · rw [closedCell_zero_eq_singleton]
    exact isClosed_inter_singleton
  specialize h n.succ n.zero_lt_succ j
  rcases h with h1 | h2
  · rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
    exact (isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j hDA).union h1
  · exact h2

/-- If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed then
`A` is closed. -/
lemma CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
    [CWComplex C] [T2Space X] {A : Set X} (hAC : A ⊆ C) (h : ∀ n (_ : 0 < n), ∀ (j : cell C n),
    IsClosed (A ∩ openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A :=
  RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC (by simp) h

/-- A version of `cellFrontier_subset_base_union_finite_closedCell` using open cells:
The boundary of a cell is contained in a finite union of open cells of a lower dimension. -/
lemma RelCWComplex.cellFrontier_subset_finite_openCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m),
    cellFrontier n i ⊆ D ∪ (⋃ (m < n) (j ∈ I m), openCell m j) := by
  induction' n using Nat.case_strong_induction_on with n hn
  · simp [cellFrontier_zero_eq_empty]
  · -- We apply `cellFrontier_subset_base_union_finite_closedCell` once and then apply
    -- the induction hypothesis to the finitely many cells that
    -- `cellFrontier_subset_base_union_finite_closedCell` gives us.
    classical
    obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell n.succ i
    choose p hp using hn
    let I m := J m ∪ ((Finset.range n.succ).biUnion
      (fun l ↦ (J l).biUnion (fun y ↦ if h : l ≤ n then p l h y m else ∅)))
    use I
    intro x hx
    specialize hJ hx
    simp only [mem_union, mem_iUnion, exists_prop] at hJ ⊢
    rcases hJ with hJ | hJ
    · exact .inl hJ
    obtain ⟨l, hln , j, hj, hxj⟩ := hJ
    rw [← cellFrontier_union_openCell_eq_closedCell] at hxj
    rcases hxj with hxj | hxj
    · specialize hp l (Nat.le_of_lt_succ hln) j hxj
      simp_rw [mem_union, mem_iUnion, exists_prop] at hp
      refine .imp_right (fun ⟨k, hkl, i, hi, hxi⟩ ↦ ⟨k, lt_trans hkl hln, i, ?_, hxi⟩) hp
      simp only [Nat.succ_eq_add_one, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, I]
      exact .inr ⟨l, hln, j, hj, by simp [Nat.le_of_lt_succ hln, hi]⟩
    · right
      use l, hln, j
      simp only [Nat.succ_eq_add_one, Finset.mem_union, I]
      exact ⟨Or.intro_left _ hj, hxj⟩

/-- A version of `cellFrontier_subset_finite_closedCell` using open cells: The boundary of a cell is
contained in a finite union of open cells of a lower dimension. -/
lemma CWComplex.cellFrontier_subset_finite_openCell [CWComplex C] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m),
    cellFrontier n i ⊆ ⋃ (m < n) (j ∈ I m), openCell m j := by
  simpa using RelCWComplex.cellFrontier_subset_finite_openCell n i

namespace CWComplex

export RelCWComplex (pairwiseDisjoint disjoint_openCell_of_ne openCell_subset_closedCell
  cellFrontier_subset_closedCell cellFrontier_union_openCell_eq_closedCell map_zero_mem_openCell
  map_zero_mem_closedCell isCompact_closedCell isClosed_closedCell isCompact_cellFrontier
  isClosed_cellFrontier closure_openCell_eq_closedCell skeletonLT_top skeleton_top skeletonLT_mono
  skeleton_mono skeletonLT_monotone skeleton_monotone skeletonLT_subset_complex
  skeleton_subset_complex closedCell_subset_skeletonLT closedCell_subset_skeleton
  closedCell_subset_complex openCell_subset_skeletonLT openCell_subset_skeleton
  openCell_subset_complex cellFrontier_subset_skeletonLT cellFrontier_subset_skeleton
  cellFrontier_subset_complex iUnion_cellFrontier_subset_skeletonLT
  iUnion_cellFrontier_subset_skeleton closedCell_zero_eq_singleton openCell_zero_eq_singleton
  cellFrontier_zero_eq_empty isClosed skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ
  skeleton_union_iUnion_closedCell_eq_skeleton_succ
  eq_of_not_disjoint_openCell disjoint_skeletonLT_openCell
  disjoint_skeleton_openCell skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier
  skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier)

end CWComplex

end Topology
