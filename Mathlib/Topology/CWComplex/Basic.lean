/-
Copyright (c) 2024 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder

/-!
# CW complexes

This file defines (relative) CW complexes and proofs basic properties about them.

A CW complex is a topological space that is made by gluing closed disks of different dimensions
together.

## Main definitions
* `RelCWComplex C D` : The class of CW structures on a subspace `C` realtive to `D` of a topological
  space `X`.
* `ClasCWComplex C` : An abbreviation for `RelCWComplex C ∅`. The class of CW structures on a
  subspace `C` of the topological space `X`.
* `openCell n i` : An open cell of dimension `n`.
* `closedCell n i` : A closed cell of dimension `n`.
* `cellFrontier n i` : The edge of a cell of dimension `n`.
* `level C n` : The `n`-th level of the (relative) CW complex `C`.

## Main statements
* `iUnion_openCell_eq_level` : The levels can also be seen as a union of open cells.
* `cellFrontier_subset_finite_openCell` : The edge of a cell is contained in a finite union of
  open cells of a lower dimension.

## Implementation notes
* This definition uses is the historical definition rather than the modern one to avoid working
  with a lot of different topological spaces.
* We define what it means for a subspace to be a CW complex instead of a topological space itself.
  This has the advantage that it makes a lot of constructions easier as you do not need to deal with
  different topologies. However, this approach requires the subspace to be closed. Should that
  not be the case you need to consider that subspace as a subspace of itself.
* The definition `RelCWcomplex` does not require `X` to be a Hausdorff space.
  A lot of the lemmas will however require this property.
* For statements the auxiliary construction `levelaux` is preferred over `level` as it makes
  the base case of inductions easier. The statement about `level` should then be derived from the
  one about `levelaux`.

## References
* [A. Hatcher, *Algebraic Topology*][hatcher02]
-/

noncomputable section

open Metric Set

/-- Characterizing when a subspace `C` of a topological space `X` is a CW complex relative to
  another subspace `D`. Note that this requires `C` and `D` to be closed subspaces.
  If `C` is not closed choose `X` to be `C`. A lot of lemmas will require `[T2Space X]`.-/
class RelCWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) (D : outParam (Set X)) where
  /-- The indexing type of the cells of dimension `n`.-/
  cell (n : ℕ) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
    This map is a bijection when restricting to `closedBall 0 1` as specified by the property
    `source_eq`. Note that `(Fin n → ℝ)` carries the maximum metric.-/
  map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  /-- The source of every charactersitic map of dimension `n` is
    `(closedBall 0 1 : Set (Fin n → ℝ))`.-/
  source_eq (n : ℕ) (i : cell n) : (map n i).source = closedBall 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`.-/
  cont (n : ℕ) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `closedBall 0 1` is continuous on the image.-/
  cont_symm (n : ℕ) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `pairwiseDisjoint` or `disjoint_openCell_of_ne` in
    the namespace `RelCWComplex` instead. -/
  pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  /-- All open cells are disjoint with the base. Use `disjointBase` in the namespace `RelCWComplex`
    instead. -/
  disjointBase' (n : ℕ) (i : cell n) : Disjoint (map n i '' ball 0 1) D
  /-- The edge of a cell is contained in a finite union of closed cells of a lower dimension.
    Use `cellFrontier_subset_finite_closedCell` in the namespace `RelCWComplex` instead.-/
  mapsto (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
    every closed cell and `D` is closed. Use `closed` in the namespace `RelCWComplex` instead.-/
  closed' (A : Set X) (asubc : A ⊆ C) :
    ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A
  /-- The base `D` is closed.-/
  isClosedBase : IsClosed D
  /-- The union of all closed cells equals `C`. Use `union` in the namespace `RelCWComplex`
    instead.-/
  union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

abbrev ClasCWComplex {X : Type*} [TopologicalSpace X] (C : Set X) := RelCWComplex C ∅

def ClasCWComplex.mk.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ)  → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = closedBall 0 1)
    (cont : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (cont_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsto: ∀ n i, ∃ I : Π m, Finset (cell m),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X), (asubc : A ⊆ C) →
      (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A)
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) : ClasCWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  cont := cont
  cont_symm := cont_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := by simp only [disjoint_empty, implies_true]
  mapsto := by simpa only [empty_union]
  closed' := by simpa only [inter_empty, isClosed_empty, and_true]
  isClosedBase := isClosed_empty
  union' := by simpa only [empty_union]

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

/-- The open `n`-cell given by the index `i`. Use this instead of `map n i '' ball 0 1` whenever
  possible.-/
def RelCWComplex.openCell [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X := map n i '' ball 0 1

/-- The closed `n`-cell given by the index `i`. Use this instead of `map n i '' closedBall 0 1
  whenever possible.`-/
def RelCWComplex.closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X :=
  map n i '' closedBall 0 1

/-- The edge of the `n`-cell given by the index `i`. Use this instead of `map n i '' sphere 0 1`
  whenever possible. -/
def RelCWComplex.cellFrontier [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X :=
  map n i '' sphere 0 1

namespace ClasCWComplex

export RelCWComplex (cell map source_eq cont cont_symm mapsto isClosedBase openCell closedCell
  cellFrontier)

end ClasCWComplex

lemma ClasCWComplex.mapsto [ClasCWComplex C] (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m),
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

lemma ClasCWComplex.cellFrontier_subset_finite_closedCell [ClasCWComplex C] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m), cellFrontier n i ⊆ ⋃ (m < n) (j ∈ I m), closedCell m j := by
  rcases RelCWComplex.mapsto n i with ⟨I, hI⟩
  use I
  rw [mapsTo', empty_union] at hI
  exact hI

lemma RelCWComplex.union [RelCWComplex C D] : D ∪ ⋃ (n : ℕ) (j : cell C n), closedCell n j = C :=
  RelCWComplex.union'

lemma ClasCWComplex.union [ClasCWComplex C] : ⋃ (n : ℕ) (j : cell C n), closedCell n j = C := by
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

/-- A non-standard definition of the `n`-th level of a CW complex for `n ∈ ℕ ∪ ∞` useful for
  induction. The standard `level` is defined in terms of levelaux. `levelaux` is preferred in
  statements. You should then derive the statement about `level`. -/
def RelCWComplex.levelaux (C : Set X) {D : Set X} [RelCWComplex C D] (n : ℕ∞) : Set X :=
  D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C m), closedCell m j

/-- The `n`-th level of a CW complex, for `n ∈ ℕ ∪ ∞`. For statements use `levelaux` instead
  and then derive the statement about `level`.-/
def RelCWComplex.level (C : Set X) {D : Set X} [RelCWComplex C D] (n : ℕ∞) : Set X :=
  levelaux C (n + 1)

namespace ClasCWComplex

export RelCWComplex (levelaux level)

end ClasCWComplex

lemma RelCWComplex.levelaux_zero_eq_base [RelCWComplex C D] : levelaux C 0 = D := by
  simp only [levelaux, ENat.not_lt_zero, iUnion_of_empty, iUnion_empty, union_empty]

lemma ClasCWComplex.levelaux_zero_eq_empty [ClasCWComplex C] : levelaux C 0 = ∅ :=
    RelCWComplex.levelaux_zero_eq_base

lemma RelCWComplex.isCompact_closedCell [RelCWComplex C D] {n : ℕ} {i : cell C n} :
    IsCompact (closedCell n i) := (isCompact_closedBall _ _).image_of_continuousOn (cont n i)

lemma RelCWComplex.isClosed_closedCell [RelCWComplex C D] [T2Space X] {n : ℕ} {i : cell C n} :
  IsClosed (closedCell n i) := isCompact_closedCell.isClosed

lemma RelCWComplex.isCompact_cellFrontier [RelCWComplex C D] {n : ℕ} {i : cell C n} :
    IsCompact (cellFrontier n i) :=
  (isCompact_sphere _ _).image_of_continuousOn ((cont n i).mono sphere_subset_closedBall)

lemma RelCWComplex.isClosed_cellFrontier [RelCWComplex C D] [T2Space X] {n : ℕ} {i : cell C n} :
    IsClosed (cellFrontier n i) :=
  isCompact_cellFrontier.isClosed

lemma RelCWComplex.closure_openCell_eq_closedCell [RelCWComplex C D] [T2Space X] {n : ℕ}
    {j : cell C n} : closure (openCell n j) = closedCell n j := by
  apply subset_antisymm (isClosed_closedCell.closure_subset_iff.2 (openCell_subset_closedCell n j))
  rw [closedCell, ← closure_ball 0 (by exact one_ne_zero)]
  apply ContinuousOn.image_closure
  rw [closure_ball 0 (by exact one_ne_zero)]
  exact cont n j

lemma RelCWComplex.closed (C : Set X) {D : Set X} [RelCWComplex C D] [T2Space X] (A : Set X)
    (asubc : A ⊆ C) :
    IsClosed A ↔ (∀ n (j : cell C n), IsClosed (A ∩ closedCell n j)) ∧ IsClosed (A ∩ D) := by
  constructor
  · intro closedA
    constructor
    · intro n j
      exact closedA.inter isClosed_closedCell
    · exact closedA.inter (isClosedBase C)
  · exact RelCWComplex.closed' A asubc

lemma ClasCWComplex.closed (C : Set X) [ClasCWComplex C] [T2Space X] (A : Set X) (asubc : A ⊆ C) :
    IsClosed A ↔ ∀ n (j : cell C n), IsClosed (A ∩ closedCell n j) := by
  have := RelCWComplex.closed C A asubc
  simp_all

@[simp] lemma RelCWComplex.levelaux_top [RelCWComplex C D] : levelaux C ⊤ = C := by
  simp [levelaux, union]

@[simp] lemma RelCWComplex.level_top [RelCWComplex C D] : level C ⊤ = C := levelaux_top

lemma RelCWComplex.levelaux_mono [RelCWComplex C D] {n m : ℕ∞} (h : m ≤ n) :
    levelaux C m ⊆ levelaux C n := by
  apply union_subset_union_right
  intro x xmem
  simp_rw [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨l , lltm, xmeml⟩ := xmem
  exact ⟨l, lt_of_lt_of_le lltm h, xmeml⟩

lemma RelCWComplex.level_mono [RelCWComplex C D] {n m : ℕ∞} (h : m ≤ n) : level C m ⊆ level C n :=
  levelaux_mono (add_le_add_right h 1)

lemma RelCWComplex.levelaux_subset_complex [RelCWComplex C D] {n : ℕ∞} : levelaux C n ⊆ C := by
  simp_rw [← levelaux_top (C := C) (D := D)]
  exact levelaux_mono (OrderTop.le_top n)

lemma RelCWComplex.level_subset_complex [RelCWComplex C D] {n : ℕ∞} :
    level C n ⊆ C :=
  levelaux_subset_complex

lemma RelCWComplex.closedCell_subset_levelaux [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ levelaux C (n + 1) := by
  intro x xmem
  right
  simp_rw [mem_iUnion, exists_prop]
  refine ⟨n, (by norm_cast; exact lt_add_one n), ⟨j,xmem⟩⟩

lemma RelCWComplex.closedCell_subset_level [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ level C n :=
  closedCell_subset_levelaux n j

lemma RelCWComplex.closedCell_subset_complex [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ C :=
  (closedCell_subset_level n j).trans
    (by simp_rw [← level_top (C := C) (D := D)]; exact level_mono le_top)

lemma RelCWComplex.openCell_subset_levelaux [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ levelaux C (n + 1) :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_levelaux _ _ )

lemma RelCWComplex.openCell_subset_level [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ level C n :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_level _ _)

lemma RelCWComplex.openCell_subset_complex [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ C := by
  apply subset_trans (openCell_subset_level _ _)
    (by simp_rw [← level_top (C := C) (D := D)]; exact level_mono le_top)

lemma RelCWComplex.cellFrontier_subset_levelaux [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    cellFrontier n j ⊆ levelaux C n := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n j
  apply subset_trans hI
  apply union_subset_union_right
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨i, iltn, j, _, xmem⟩ := xmem
  exact ⟨i, by norm_cast, j, xmem⟩

lemma RelCWComplex.cellFrontier_subset_level [RelCWComplex C D] (n : ℕ) (j : cell C (n + 1)) :
    cellFrontier (n + 1) j ⊆ level C n :=
  cellFrontier_subset_levelaux _ _

lemma RelCWComplex.iUnion_cellFrontier_subset_levelaux [RelCWComplex C D] (l : ℕ) :
    ⋃ (j : cell C l), cellFrontier l j ⊆ levelaux C l :=
  iUnion_subset  (fun _ ↦ cellFrontier_subset_levelaux _ _)

lemma RelCWComplex.iUnion_cellFrontier_subset_level [RelCWComplex C D] (l : ℕ) :
    ⋃ (j : cell C l), cellFrontier l j ⊆ level C l :=
  (iUnion_cellFrontier_subset_levelaux l).trans (levelaux_mono le_self_add)

lemma RelCWComplex.closedCell_zero_eq_singleton [RelCWComplex C D] {j : cell C 0} :
    closedCell 0 j = {map 0 j ![]} := by
  simp [closedCell, Matrix.empty_eq]

lemma RelCWComplex.openCell_zero_eq_singleton [RelCWComplex C D] {j : cell C 0} :
    openCell 0 j = {map 0 j ![]} := by
  simp [openCell, Matrix.empty_eq]

lemma RelCWComplex.cellFrontier_zero_eq_empty [RelCWComplex C D] {j : cell C 0} :
    cellFrontier 0 j = ∅ := by
  simp [cellFrontier, sphere_eq_empty_of_subsingleton]

lemma RelCWComplex.base_subset_levelaux [RelCWComplex C D] (n : ℕ∞) : D ⊆ levelaux C n :=
  subset_union_left

lemma RelCWComplex.base_subset_level [RelCWComplex C D] (n : ℕ∞) : D ⊆ level C n :=
  base_subset_levelaux (n + 1)

lemma RelCWComplex.base_subset_complex [RelCWComplex C D] : D ⊆ C := by
  simp_rw [← level_top (C := C) (D := D)]
  exact base_subset_level ⊤

lemma RelCWComplex.isClosed [T2Space X] [RelCWComplex C D] : IsClosed C := by
  rw [closed (C := C) (D := D) C (by rfl)]
  constructor
  · intros
    rw [inter_eq_right.2 (closedCell_subset_complex _ _)]
    exact isClosed_closedCell
  · rw [inter_eq_right.2 base_subset_complex]
    exact isClosedBase C

lemma RelCWComplex.iUnion_levelaux_eq_levelaux [RelCWComplex C D] (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n + 1), levelaux C m = levelaux C n := by
  apply subset_antisymm
  · simp_rw [iUnion_subset_iff]
    exact fun _ h ↦  levelaux_mono (Order.le_of_lt_add_one h)
  · cases' n with n
    · simp only [levelaux_top, top_add, ENat.coe_lt_top, iUnion_true, ← union]
      apply union_subset
      · exact subset_iUnion_of_subset 0 (base_subset_levelaux 0)
      · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
        exact subset_iUnion_of_subset (n + 1) (closedCell_subset_levelaux n i)
    · apply subset_iUnion_of_subset n
      norm_cast
      simp

lemma RelCWComplex.iUnion_level_eq_level [RelCWComplex C D] (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n + 1), level C m = level C n := by
  simp_rw [level, ← iUnion_levelaux_eq_levelaux (n + 1)]
  ext
  simp only [mem_iUnion, exists_prop]
  constructor
  · intro ⟨i, hin, hiC⟩
    refine ⟨i + 1, ?_, hiC⟩
    exact (ENat.add_lt_add_iff_right ENat.one_ne_top).mpr hin
  · intro ⟨i, hin, hiC⟩
    cases' i with i
    · refine ⟨0, ?_, levelaux_mono (by norm_num) hiC⟩
      exact ENat.add_one_pos
    · refine ⟨i, ?_, hiC⟩
      exact (ENat.add_lt_add_iff_right ENat.one_ne_top).mp hin

lemma RelCWComplex.levelaux_succ_eq_levelaux_union_iUnion_closedCell [RelCWComplex C D] (n : ℕ) :
    levelaux C (n + 1) = levelaux C n ∪ ⋃ (j : cell C n), closedCell n j := by
  rw [levelaux, levelaux, union_assoc]
  congr
  norm_cast
  exact biUnion_lt_succ _ _

lemma RelCWComplex.level_succ_eq_level_union_iUnion [RelCWComplex C D] (n : ℕ) :
    level C (n + 1) = level C n ∪ ⋃ (j : cell C (↑n + 1)), closedCell (n + 1) j :=
  levelaux_succ_eq_levelaux_union_iUnion_closedCell _

/-- A version of the definition of `levelaux` with open cells. -/
lemma RelCWComplex.iUnion_openCell_eq_levelaux [RelCWComplex C D] (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C m), openCell m j = levelaux C n := by
  apply subset_antisymm
  · apply union_subset
    · exact base_subset_levelaux n
    · apply iUnion_subset fun m ↦ iUnion_subset fun hm ↦ iUnion_subset fun j ↦ ?_
      exact subset_trans (openCell_subset_levelaux m j) (levelaux_mono (Order.add_one_le_of_lt hm))
  · rw [levelaux]
    apply union_subset subset_union_left
    apply iUnion_subset fun m ↦ iUnion_subset fun hm ↦ iUnion_subset fun j ↦ ?_
    rw [← cellFrontier_union_openCell_eq_closedCell]
    apply union_subset
    · induction' m using Nat.case_strong_induction_on with m hm'
      · simp [cellFrontier_zero_eq_empty]
      · obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (m + 1) j
        apply hI.trans
        apply union_subset subset_union_left
        apply iUnion_subset fun l ↦ iUnion_subset fun hl ↦ iUnion_subset fun i ↦
          iUnion_subset fun _ ↦ ?_
        rw [← cellFrontier_union_openCell_eq_closedCell]
        apply union_subset
        · exact (hm' l (Nat.le_of_lt_succ hl) ((ENat.coe_lt_coe.2 hl).trans hm) i)
        · apply subset_union_of_subset_right
          apply subset_iUnion_of_subset l
          apply subset_iUnion_of_subset ((ENat.coe_lt_coe.2 hl).trans hm)
          exact subset_iUnion _ i
    · apply subset_union_of_subset_right
        (subset_iUnion_of_subset m (subset_iUnion_of_subset hm (subset_iUnion _ j)))

lemma ClasCWComplex.iUnion_openCell_eq_levelaux [ClasCWComplex C] (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n) (j : cell C m), openCell m j = levelaux C n := by
  rw [← RelCWComplex.iUnion_openCell_eq_levelaux, empty_union]

lemma RelCWComplex.iUnion_openCell_eq_level [RelCWComplex C D] (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n + 1) (j : cell C m), openCell m j = level C n :=
  iUnion_openCell_eq_levelaux _

lemma ClasCWComplex.iUnion_openCell_eq_levelAB [ClasCWComplex C] (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n + 1) (j : cell C m), openCell m j = level C n :=
  ClasCWComplex.iUnion_openCell_eq_levelaux _

lemma RelCWComplex.iUnion_openCell [RelCWComplex C D] :
    D ∪ ⋃ (n : ℕ) (j : cell C n), openCell n j = C := by
  simp only [← levelaux_top (C := C) (D := D), ← iUnion_openCell_eq_levelaux,
    ENat.coe_lt_top, iUnion_true]

lemma ClasCWComplex.iUnion_openCell [ClasCWComplex C] :
    ⋃ (n : ℕ) (j : cell C n), openCell n j = C := by
  have := RelCWComplex.iUnion_openCell (C := C) (D := ∅)
  simp_all

/-- The contraposition of `disjoint_openCell_of_ne`.-/
lemma RelCWComplex.eq_cell_of_not_disjoint [RelCWComplex C D] {n : ℕ} {j : cell C n} {m : ℕ}
    {i : cell C m} (notdisjoint: ¬ Disjoint (openCell n j) (openCell m i)) :
    (⟨n, j⟩ : (Σ n, cell C n)) = ⟨m, i⟩ := by
  by_contra h'
  push_neg at h'
  apply notdisjoint
  have := pairwiseDisjoint (C := C) (D := D)
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun] at this
  exact this (x := ⟨n, j⟩) (mem_univ _) (y := ⟨m, i⟩) (mem_univ _) h'

lemma RelCWComplex.exists_mem_openCell_of_mem_levelaux [RelCWComplex C D] {n : ℕ∞} {x : X}
    (hx : x ∈ levelaux C n) :
    x ∈ D ∨ ∃ (m : ℕ) (_ : m < n) (j : cell C m), x ∈ openCell m j := by
  simp_all [← iUnion_openCell_eq_levelaux]

lemma ClasCWComplex.exists_mem_openCell_of_mem_levelaux [ClasCWComplex C] {n : ℕ∞} {x : X}
    (xmemlvl : x ∈ levelaux C n) :
    ∃ (m : ℕ) (_ : m < n) (j : cell C m), x ∈ openCell m j := by
  simp_all [← ClasCWComplex.iUnion_openCell_eq_levelaux]

lemma RelCWComplex.exists_mem_openCell_of_mem_level [RelCWComplex C D] {n : ℕ∞} {x : X}
    (xmemlvl : x ∈ level C n) :
    x ∈ D ∨ ∃ (m : ℕ) (_ : m ≤ n) (j : cell C m), x ∈ openCell m j := by
  rw [level] at xmemlvl
  rcases exists_mem_openCell_of_mem_levelaux xmemlvl with xmem | xmem
  · left
    exact xmem
  · right
    obtain ⟨m, mlen, _⟩ := xmem
    use m, Order.le_of_lt_add_one mlen

lemma ClasCWComplex.exists_mem_openCell_of_mem_level [ClasCWComplex C] {n : ℕ∞} {x : X}
    (xmemlvl : x ∈ level C n) :
    ∃ (m : ℕ) (_ : m ≤ n) (j : cell C m), x ∈ openCell m j := by
  rcases RelCWComplex.exists_mem_openCell_of_mem_level (C := C) (D := ∅) (n := n) xmemlvl with h | h
  · contradiction
  · exact h

/-- A level and an open cell of a higher dimension are disjoint -/
lemma RelCWComplex.levelaux_inter_openCell_eq_empty [RelCWComplex C D] {n : ℕ∞} {m : ℕ}
    {j : cell C m} (nlem : n ≤ m) : levelaux C n ∩ openCell m j = ∅ := by
  -- This is a consequence of `iUnion_openCell_eq_levelaux` and `disjoint_openCell_of_ne`
  simp_rw [← iUnion_openCell_eq_levelaux, union_inter_distrib_right, iUnion_inter, union_empty_iff,
    iUnion_eq_empty]
  constructor
  · rw [← Disjoint.inter_eq]
    exact Disjoint.symm (disjointBase m j)
  intro l llt i
  apply disjoint_openCell_of_ne
  intro eq
  simp_all only [Sigma.mk.inj_iff]
  linarith [ENat.coe_lt_coe.1 (gt_of_ge_of_gt nlem llt)]

/-- A level and an open cell of a higher dimension are disjoint -/
lemma RelCWComplex.level_inter_openCell_eq_empty [RelCWComplex C D] {n : ℕ∞} {m : ℕ} {j : cell C m}
    (nlem : n < m) : level C n ∩ openCell m j = ∅ :=
  levelaux_inter_openCell_eq_empty (Order.add_one_le_of_lt nlem)

lemma RelCWComplex.base_inter_iUnion_openCell_eq_empty [T2Space X] [RelCWComplex C D] :
    D ∩ ⋃ (n : ℕ) (j : cell C n), openCell n j = ∅ := by
  simp_rw [inter_iUnion, iUnion_eq_empty]
  intro n i
  rw [inter_comm, (disjointBase n i).inter_eq]

lemma RelCWComplex.interior_base_inter_closedCell_eq_empty [T2Space X] [RelCWComplex C D] {n : ℕ}
    {j : cell C n} : interior D ∩ closedCell n j = ∅ := by
  by_contra h
  push_neg at h
  rw [← closure_openCell_eq_closedCell, inter_comm,
    closure_inter_open_nonempty_iff isOpen_interior] at h
  rcases h with ⟨x, xmemcell, xmemD⟩
  suffices x ∈ levelaux C 0 ∩ openCell n j by
    rw [levelaux_inter_openCell_eq_empty n.cast_nonneg'] at this
    exact this
  exact ⟨base_subset_levelaux 0 (interior_subset xmemD), xmemcell⟩

lemma RelCWComplex.interior_base_inter_iUnion_closedCell_eq_empty [T2Space X] [RelCWComplex C D] :
    interior D ∩ ⋃ (n : ℕ) (j : cell C n), closedCell n j = ∅ := by
  simp_rw [inter_iUnion, interior_base_inter_closedCell_eq_empty, iUnion_empty]

/-- A level intersected with a closed cell of a higher dimension is the level intersected with
  the edge of the cell.-/
lemma RelCWComplex.levelaux_inter_closedCell_eq_levelaux_inter_cellFrontier [RelCWComplex C D]
    {n : ℕ∞} {m : ℕ} {j : cell C m} (nlem : n ≤ m) :
    levelaux C n ∩ closedCell m j = levelaux C n ∩ cellFrontier m j := by
  refine subset_antisymm ?_ (inter_subset_inter_right _ (cellFrontier_subset_closedCell _ _))
  rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
  apply union_subset (by rfl)
  rw [levelaux_inter_openCell_eq_empty nlem]
  exact empty_subset (levelaux C n ∩ cellFrontier m j)

/-- Version of `levelaux_inter_openCell_eq_empty` using `level`.-/
lemma RelCWComplex.level_inter_closedCell_eq_level_inter_cellFrontier [RelCWComplex C D] {n : ℕ∞}
    {m : ℕ} {j : cell C m} (nltm : n < m) :
    level C n ∩ closedCell m j = level C n ∩ cellFrontier m j :=
  levelaux_inter_closedCell_eq_levelaux_inter_cellFrontier (Order.add_one_le_of_lt nltm)

/-- If for all `m ≤ n` and every `i : cell C m` the intersection `A ∩ closedCell m j` is closed
  and `A ∩ D` is closed then `A ∩ cellFrontier (n + 1) j` is closed for every
  `j : cell C (n + 1)`.-/
lemma RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} {n : ℕ} (hn : ∀ m ≤ n, ∀ (j : cell C m),
    IsClosed (A ∩ closedCell m j)) (j : cell C (n + 1)) (hD : IsClosed (A ∩ D)) :
    IsClosed (A ∩ cellFrontier (n + 1) j) := by
  -- this is a consequence of `cellFrontier_subset_finite_closedCell`
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (n + 1) j
  rw [← inter_eq_right.2 hI, ← inter_assoc]
  refine IsClosed.inter ?_ isClosed_cellFrontier
  simp_rw [inter_union_distrib_left, inter_iUnion,
    ← iUnion_subtype (fun m ↦ m < n + 1) (fun m ↦ ⋃ i ∈ I m, A ∩ closedCell m i)]
  apply hD.union
  apply isClosed_iUnion_of_finite
  intro ⟨m, mlt⟩
  rw [← iUnion_subtype (fun i ↦ i ∈ I m) (fun i ↦ A ∩ closedCell (↑m) i.1)]
  exact isClosed_iUnion_of_finite (fun ⟨j, _⟩ ↦ hn m (Nat.le_of_lt_succ mlt) j)

lemma ClasCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
    [ClasCWComplex C] [T2Space X] {A : Set X} {n : ℕ} (hn : ∀ m ≤ n, ∀ (j : cell C m),
    IsClosed (A ∩ closedCell m j)) (j : cell C (n + 1)) :
    IsClosed (A ∩ cellFrontier (n + 1) j) :=
  RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j
    (by simp only [inter_empty, isClosed_empty])

/-- If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed then
  `A` is closed. -/
lemma RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} (asub : A ⊆ C) (hDA : IsClosed (A ∩ D))
    (h : ∀ n (_ : 0 < n), ∀ (j : cell C n),
    IsClosed (A ∩ openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A := by
  rw [closed C A asub]
  refine ⟨?_, hDA⟩
  intro n j
  induction' n using Nat.case_strong_induction_on with n hn
  · rw [closedCell_zero_eq_singleton]
    exact isClosed_inter_singleton
  specialize h n.succ (Nat.zero_lt_succ n) j
  rcases h with h1 | h2
  · rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
    exact (isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j hDA).union h1
  · exact h2

/-- If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed then
  `A` is closed. -/
lemma ClasCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
    [ClasCWComplex C] [T2Space X] {A : Set X} (asub : A ⊆ C) (h : ∀ n (_ : 0 < n), ∀ (j : cell C n),
    IsClosed (A ∩ openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A :=
  RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell asub
    (by simp only [inter_empty, isClosed_empty]) h

/-- A version of `cellFrontier_subset_finite_closedCell` using open cells: The edge of a cell is
  contained in a finite union of open cells of a lower dimension.-/
lemma RelCWComplex.cellFrontier_subset_finite_openCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m),
    cellFrontier n i ⊆ D ∪ (⋃ (m < n) (j ∈ I m), openCell m j) := by
  induction' n using Nat.case_strong_induction_on with n hn
  · simp [cellFrontier_zero_eq_empty]
  · -- We apply `cellFrontier_subset_finite_closedCell` once and then apply
    -- the induction hypothesis to the finitely many cells that
    -- `cellFrontier_subset_finite_closedCell` gives us.
    classical
    obtain ⟨J, hJ⟩ :=  cellFrontier_subset_base_union_finite_closedCell (Nat.succ n) i
    choose p hp using hn
    let I m := J m ∪ (Finset.biUnion (Finset.range n.succ)
      (fun l ↦ Finset.biUnion (J l) (fun y ↦ if h : l ≤ n then p l h y m else ∅)))
    use I
    intro x xmem
    specialize hJ xmem
    simp only [mem_union, mem_iUnion, exists_prop] at hJ ⊢
    rcases hJ with hJ | hJ
    · exact .inl hJ
    obtain ⟨l, llen , j, jmem, xmemclosedCell⟩ := hJ
    rw [← cellFrontier_union_openCell_eq_closedCell] at xmemclosedCell
    rcases xmemclosedCell with xmemcellFrontier | xmemopenCell
    · let hK := hp l (Nat.le_of_lt_succ llen) j xmemcellFrontier
      simp_rw [mem_union, mem_iUnion, exists_prop] at hK
      rcases hK with hK | hK
      · exact .inl hK
      right
      obtain ⟨k, kltl, i, imem, xmemopenCell⟩ := hK
      use k, (lt_trans kltl llen), i
      refine ⟨?_, xmemopenCell ⟩
      simp only [Nat.succ_eq_add_one, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, I]
      right
      use l, llen, j, jmem
      simp only [Nat.le_of_lt_succ llen, ↓reduceDIte, imem]
    · right
      use l, llen, j
      simp only [Nat.succ_eq_add_one, Finset.mem_union, I]
      exact ⟨Or.intro_left _ jmem, xmemopenCell⟩

/-- A version of `cellFrontier_subset_finite_closedCell` using open cells: The edge of a cell is
  contained in a finite union of open cells of a lower dimension.-/
lemma ClasCWComplex.cellFrontier_subset_finite_openCellAB [ClasCWComplex C] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m),
    cellFrontier n i ⊆ ⋃ (m < n) (j ∈ I m), openCell m j := by
  have := RelCWComplex.cellFrontier_subset_finite_openCell n i
  simp_all only [empty_union]

namespace ClasCWComplex

export RelCWComplex (pairwiseDisjoint disjoint_openCell_of_ne openCell_subset_closedCell
  cellFrontier_subset_closedCell cellFrontier_union_openCell_eq_closedCell map_zero_mem_openCell
  map_zero_mem_closedCell isCompact_closedCell isClosed_closedCell isCompact_cellFrontier
  isClosed_cellFrontier closure_openCell_eq_closedCell levelaux_top level_top levelaux_mono
  level_mono levelaux_subset_complex level_subset_complex closedCell_subset_levelaux
  closedCell_subset_level closedCell_subset_complex openCell_subset_levelaux openCell_subset_level
  openCell_subset_complex cellFrontier_subset_levelaux cellFrontier_subset_level
  iUnion_cellFrontier_subset_levelaux iUnion_cellFrontier_subset_level closedCell_zero_eq_singleton
  openCell_zero_eq_singleton cellFrontier_zero_eq_empty isClosed iUnion_levelaux_eq_levelaux
  iUnion_level_eq_level levelaux_succ_eq_levelaux_union_iUnion_closedCell
  level_succ_eq_level_union_iUnion eq_cell_of_not_disjoint levelaux_inter_openCell_eq_empty
  level_inter_openCell_eq_empty levelaux_inter_closedCell_eq_levelaux_inter_cellFrontier
  level_inter_closedCell_eq_level_inter_cellFrontier)

end ClasCWComplex
