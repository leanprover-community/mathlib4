/-
Copyright (c) 2025 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/

import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Analysis.NormedSpace.Real

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW complexes.
The definintion of subcomplexes is in the file `Topology.CWComplex.Classical.Basic`.

## Main results
* `RelCWComplex.Subcomplex.instRelCWComplex`: a subcomplex of a (relative) CW complex is again a
  (relative) CW complex.

## References
* [K. Jänich, *Topology*][Janich1984]
-/

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

/-- A subcomplex is the union of its closed cells and its base. -/
lemma RelCWComplex.Subcomplex.union_closedCell [T2Space X] [RelCWComplex C D] (E : Subcomplex C) :
    D ∪ ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply union_subset
    · rw [← Subcomplex.union (C := C) (D := D) (E := E)]
      exact subset_union_left
    · apply iUnion_subset fun n ↦ iUnion_subset fun i ↦ ?_
      rw [← closure_openCell_eq_closedCell, E.closed.closure_subset_iff, ← E.union]
      apply subset_union_of_subset_right
      exact subset_iUnion_of_subset n
        (subset_iUnion (fun (i : ↑(E.I n)) ↦ openCell (C := C) (D := D) n ↑i) i)
  · simp_rw [← E.union]
    apply union_subset_union_right
    apply iUnion_mono fun n ↦ iUnion_mono fun (i : ↑(E.I n)) ↦ ?_
    exact openCell_subset_closedCell (C := C) n i

/-- A subcomplex is the union of its closed cells. -/
lemma CWComplex.Subcomplex.union_closedCell [T2Space X] [CWComplex C] (E : Subcomplex C) :
    ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E :=
  (empty_union _ ).symm.trans (RelCWComplex.Subcomplex.union_closedCell E)

lemma RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (h : i ∉ E.I n) : Disjoint (openCell n i) E := by
  simp_rw [← union, disjoint_union_right, disjoint_iUnion_right]
  exact ⟨disjointBase n i , fun _ _ ↦ disjoint_openCell_of_ne (by aesop)⟩

open Classical in
/-- A subcomplex is again a CW complex. -/
@[simps]
instance RelCWComplex.Subcomplex.instRelCWComplex [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) : RelCWComplex E D where
  cell n := E.I n
  map n i := map (C := C) n i
  source_eq n i := source_eq (C := C) n i
  continuousOn n i := continuousOn (C := C) n i
  continuousOn_symm n i := continuousOn_symm (C := C) n i
  pairwiseDisjoint' := by
    simp only [PairwiseDisjoint, Set.Pairwise, mem_univ, ne_eq, Function.onFun,
      disjoint_iff_inter_eq_empty, true_implies, Sigma.forall, Subtype.forall]
    intro n j _ m i _ eq
    refine (disjoint_openCell_of_ne ?_).inter_eq
    simp_all only [Sigma.mk.inj_iff, not_and, ne_eq]
    intro a
    subst a
    simp_all
  disjointBase' n i := disjointBase' (C := C) n i
  mapsTo := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) n i with ⟨J, hJ⟩
    use fun m ↦ Finset.preimage (J m) Subtype.val (by simp [InjOn])
    rw [mapsTo_iff_image_subset]
    intro x hx
    specialize hJ hx
    simp_rw [iUnion_coe_set, mem_union, mem_iUnion, exists_prop, exists_and_right,
      Decidable.or_iff_not_imp_left] at hJ ⊢
    intro h
    specialize hJ h
    obtain ⟨m, hmn, j, hj, hxj⟩ := hJ
    use m, hmn, j
    refine ⟨?_, openCell_subset_closedCell _ _ hxj⟩
    suffices j ∈ E.I m from ⟨this, by simp [hj]⟩
    have : x ∈ (E : Set X) := by
      rw [← union_closedCell]
      right
      refine mem_of_subset_of_mem ?_ hx
      refine subset_iUnion_of_subset n (subset_iUnion_of_subset i ?_)
      exact cellFrontier_subset_closedCell (C := C) n i
    simp only [← E.union, iUnion_coe_set, mem_union, h, mem_iUnion, exists_prop,
      false_or] at this
    obtain ⟨l, o, hxo⟩ := this
    suffices (⟨m, j⟩ : Σ n, cell C n) = ⟨l, ↑o⟩ by aesop
    apply eq_of_not_disjoint_openCell
    rw [not_disjoint_iff]
    use x
    exact ⟨hxj, hxo.2⟩
  closed' A hA h := by
    apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
      (subset_trans hA (subset_complex (C := C) E)) h.2
    intro n _ j
    by_cases hj : j ∈ E.I n
    · exact Or.intro_right _ (h.1 n ⟨j, hj⟩)
    left
    suffices A ∩ openCell n j = ∅ from this ▸ isClosed_empty
    rw [← disjoint_iff_inter_eq_empty]
    exact (disjoint_openCell_subcomplex_of_not_mem E hj).symm.mono_left hA
  isClosedBase := isClosedBase (C := C)
  union' := union_closedCell E

/-- A subcomplex is again a CW complex. -/
instance CWComplex.Subcomplex.instCWComplex [T2Space X] [CWComplex C] (E : Subcomplex C) :
    CWComplex (E : Set X) :=
  RelCWComplex.toCWComplex (E : Set X)

@[simp]
lemma CWComplex.Subcomplex.cell_def [T2Space X] [CWComplex C] (E : Subcomplex C)
    (n : ℕ) : cell (E : Set X) n = E.I (C := C) n :=
  rfl

@[simp]
lemma CWComplex.Subcomplex.map_def [T2Space X] [CWComplex C] (E : Subcomplex C) (n : ℕ)
    (i : E.I n) : map (C := E) n i = map (C := C) n i :=
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.openCell_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C) (n : ℕ)
    (i : E.I n) : openCell (C := E) n i = openCell n (i : cell C n) := by
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.closedCell_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    (n : ℕ) (i : E.I n) : closedCell (C := E) n i = closedCell n (i : cell C n) := by
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.cellFrontier_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    (n : ℕ) (i : E.I n) : cellFrontier (C := E) n i = cellFrontier n (i : cell C n) := by
  rfl

instance RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType [T2Space X]
    [RelCWComplex C D] [FiniteType C] (E : Subcomplex C) : FiniteType (E : Set X) where
  finite_cell n :=
    let _ := FiniteType.finite_cell (C := C) (D := D) n
    toFinite (E.I n)

instance RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] [FiniteDimensional C] (E : Subcomplex C) :
    FiniteDimensional (E : Set X) where
  eventually_isEmpty_cell := by
    have := FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)
    simp only [Filter.eventually_atTop, ge_iff_le] at this ⊢
    obtain ⟨n, hn⟩ := this
    use n
    intro b nleb
    simp [isEmpty_subtype, hn b nleb]

/-- A subcomplex of a finite CW complex is again finite. -/
instance RelCWComplex.Subcomplex.finite_subcomplex_of_finite [T2Space X] [RelCWComplex C D]
    [Finite C] (E : Subcomplex C) : Finite (E : Set X) :=
  finite_of_finiteDimensional_finiteType _

namespace CWComplex.Subcomplex

export RelCWComplex.Subcomplex (subset_complex finiteType_subcomplex_of_finiteType
  finiteDimensional_subcomplex_of_finiteDimensional finite_subcomplex_of_finite)

end CWComplex.Subcomplex

end Topology
