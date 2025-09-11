/-
Copyright (c) 2025 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/

import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Finiteness notions on CW complexes

In this file we define what it means for a CW complex to be finite dimensional, of finite type or
finite. We define constructors with relaxed conditions for CW complexes of finite type and
finite CW complexes.

## Main definitions
* `RelCWComplex.FiniteDimensional`: a CW complex is finite dimensional if it has only finitely many
  nonempty indexing types for the cells.
* `RelCWComplex.FiniteType`: a CW complex is of finite type if it has only finitely many cells in
  each dimension.
* `RelCWComplex.Finite`: a CW complex is finite if it is finite dimensional and of finite type.

## Main statements
* `RelCWComplex.mkFiniteType`: if we want to construct a CW complex of finite type, we can relax the
  condition `mapsTo`.
* `RelCWComplex.mkFinite`: if we want to construct a finite CW complex, we can relax the condition
  `mapsTo` and can leave out the condition `closed'`.
* `RelCWComplex.finite_iff_finite_cells`: a CW complex is finite iff the total number of its cells
  is finite.
-/

open Metric Set

namespace Topology

/-- A CW complex is finite dimensional if `cell C n` is empty for all but finitely many `n`. -/
class RelCWComplex.FiniteDimensional.{u} {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] : Prop where
  /-- For some natural number `n`, the type `cell C m` is empty for all `m ≥ n`. -/
  eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell C n)

/-- A CW complex is of finite type if `cell C n` is finite for every `n`. -/
class RelCWComplex.FiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] : Prop where
  /-- `cell C n` is finite for every `n`. -/
  finite_cell (n : ℕ) : Finite (cell C n)

/-- A CW complex is finite if it is finite dimensional and of finite type. -/
class RelCWComplex.Finite {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] extends FiniteDimensional C, FiniteType C

variable {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X} [RelCWComplex C D]

lemma RelCWComplex.finite_of_finiteDimensional_finiteType [FiniteDimensional C]
    [FiniteType C] : Finite C where
  eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell
  finite_cell n := FiniteType.finite_cell n

namespace CWComplex

export RelCWComplex (FiniteDimensional FiniteType Finite FiniteDimensional.eventually_isEmpty_cell
  FiniteType.finite_cell finite_of_finiteDimensional_finiteType)

end CWComplex

/-- If we want to construct a relative CW complex of finite type, we can add the condition
`finite_cell` and relax the condition `mapsTo`. -/
def RelCWComplex.mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X))
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (_ : A ⊆ C),
      ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A)
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    RelCWComplex C D where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  isClosedBase := isClosedBase
  union' := union'

/-- A CW complex that was constructed using `RelCWComplex.mkFiniteType` is of finite type. -/
lemma RelCWComplex.finiteType_mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X))
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (_ : A ⊆ C),
      ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A)
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
    FiniteType C :=
  letI := mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
  { finite_cell := finite_cell }

/-- If we want to construct a CW complex of finite type, we can add the condition `finite_cell` and
relax the condition `mapsTo`. -/
def CWComplex.mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (_ : A ⊆ C),
    (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A)
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  union' := union'

/-- A CW complex that was constructed using `CWComplex.mkFiniteType` is of finite type. -/
lemma CWComplex.finiteType_mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (_ : A ⊆ C),
      (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A)
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFiniteType C cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' mapsTo closed' union'
    FiniteType C :=
  letI := mkFiniteType C cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' mapsTo closed' union'
  { finite_cell := finite_cell }

/-- If we want to construct a finite relative CW complex we can add the conditions
`eventually_isEmpty_cell` and `finite_cell`, relax the condition `mapsTo` and remove the condition
`closed'`. -/
def RelCWComplex.mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X)) (cell : (n : ℕ) → Type u)
    (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    RelCWComplex C D where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' A asubc := by
    intro h
    -- `A = A ∩ C = A ∩ (D ∪ ⋃ n, ⋃ j, closedCell n j)` is closed by assumption since `C` has only
    -- finitely many cells.
    rw [← inter_eq_left.2 asubc]
    simp_rw [Filter.eventually_atTop, ge_iff_le] at eventually_isEmpty_cell
    obtain ⟨N, hN⟩ := eventually_isEmpty_cell
    suffices IsClosed (A ∩ (D ∪ ⋃ (n : {n : ℕ // n < N}), ⋃ j, ↑(map n j) '' closedBall 0 1)) by
      convert this using 2
      rw [← union', iUnion_subtype]
      congrm D ∪ ⋃ n, ?_
      refine subset_antisymm ?_ (iUnion_subset (fun i ↦ by rfl))
      apply iUnion_subset
      intro i
      have : n < N := Decidable.byContradiction fun h ↦ (hN n (Nat.ge_of_not_lt h)).false i
      exact subset_iUnion₂ (s := fun _ i ↦ (map n i) '' closedBall 0 1) this i
    simp_rw [inter_union_distrib_left, inter_iUnion]
    exact h.2.union (isClosed_iUnion_of_finite (fun n ↦ isClosed_iUnion_of_finite (h.1 n.1)))
  isClosedBase := isClosedBase
  union' := union'

/-- A CW complex that was constructed using `RelCWComplex.mkFinite` is finite. -/
lemma RelCWComplex.finite_mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X)) (cell : (n : ℕ) → Type u)
    (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFinite C D cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' disjointBase' mapsTo isClosedBase union'
    Finite C :=
  letI := mkFinite C D cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' disjointBase' mapsTo isClosedBase union'
  { eventually_isEmpty_cell := eventually_isEmpty_cell
    finite_cell := finite_cell }

/-- If we want to construct a finite CW complex we can add the conditions `eventually_isEmpty_cell`
and `finite_cell`, relax the condition `mapsTo` and remove the condition `closed'`. -/
def CWComplex.mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsTo' : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C := (RelCWComplex.mkFinite C ∅
  (cell := cell)
  (map := map)
  (eventually_isEmpty_cell := eventually_isEmpty_cell)
  (finite_cell := finite_cell)
  (source_eq := source_eq)
  (continuousOn := continuousOn)
  (continuousOn_symm := continuousOn_symm)
  (pairwiseDisjoint' := pairwiseDisjoint')
  (disjointBase' := by simp only [disjoint_empty, implies_true])
  (mapsTo := by simpa only [empty_union])
  (isClosedBase := isClosed_empty)
  (union' := by simpa only [empty_union])).toCWComplex

/-- A CW complex that was constructed using `CWComplex.mkFinite` is finite. -/
lemma CWComplex.finite_mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFinite C cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' mapsTo union'
    Finite C :=
  letI := mkFinite C cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' mapsTo union'
  { eventually_isEmpty_cell := eventually_isEmpty_cell
    finite_cell := finite_cell }

variable {X : Type*} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- If the collection of all cells (of any dimension) of a relative CW complex `C` is finite, then
`C` is finite as a CW complex. -/
lemma RelCWComplex.finite_of_finite_cells (finite : _root_.Finite (Σ n, cell C n)) : Finite C where
  eventually_isEmpty_cell := by
    simp only [Filter.eventually_atTop, ge_iff_le]
    by_cases h : IsEmpty (Σ n, cell C n)
    · exact ⟨0, by simp_all⟩
    -- We take the greatest `n` such that there is a `j : cell C n` and show that this fulfills
    -- the necessary conditions.
    rw [not_isEmpty_iff] at h
    have _ := Fintype.ofFinite (Σ n, cell C n)
    classical
    let A := (Finset.univ : Finset (Σ n, cell C n)).image Sigma.fst
    use A.max' (Finset.image_nonempty.2 Finset.univ_nonempty) + 1
    intro m _
    by_contra h'
    have hmA : m ∈ A := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, A]
      simp only [not_isEmpty_iff, ← exists_true_iff_nonempty] at h'
      obtain ⟨j, _⟩ := h'
      use ⟨m, j⟩
    linarith [A.le_max' m hmA]
  finite_cell _ := Finite.of_injective (Sigma.mk _) sigma_mk_injective

/-- If `C` is finite as a CW complex then the collection of all cells (of any dimension) is
finite. -/
lemma RelCWComplex.finite_cells_of_finite [finite : Finite C] : _root_.Finite (Σ n, cell C n) := by
  -- We show that there is a bijection between `Σ n, cell C n` and
  -- `Σ (m : {m : ℕ // m < n}), cell C m`.
  have h := finite.eventually_isEmpty_cell
  have _ := finite.finite_cell
  simp only [Filter.eventually_atTop, ge_iff_le] at h
  rcases h with ⟨n, hn⟩
  have (m) (j : cell C m) : m < n := by
    by_contra h
    exact (hn m (not_lt.1 h)).false j
  let f : (Σ (m : {m : ℕ // m < n}), cell C m) ≃ Σ m, cell C m := {
    toFun := fun ⟨m, j⟩ ↦ ⟨m, j⟩
    invFun := fun ⟨m, j⟩ ↦ ⟨⟨m, this m j⟩, j⟩
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]}
  rw [← Equiv.finite_iff f]
  exact Finite.instSigma

/-- A CW complex is finite iff the total number of its cells is finite. -/
lemma RelCWComplex.finite_iff_finite_cells : Finite C ↔ _root_.Finite (Σ n, cell C n) :=
  ⟨fun h ↦ finite_cells_of_finite (finite := h), finite_of_finite_cells⟩

namespace CWComplex

export RelCWComplex (finite_of_finite_cells finite_cells_of_finite finite_iff_finite_cells)

end CWComplex

end Topology
