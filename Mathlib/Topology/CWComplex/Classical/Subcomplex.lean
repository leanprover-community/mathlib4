/-
Copyright (c) 2025 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/

import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW complexes.
The definintion of subcomplexes is in the file `Topology.CWComplex.Classical.Basic`.

## Main results
* `RelCWComplex.Subcomplex.instRelCWComplex`: a subcomplex of a (relative) CW complex is again a
  (relative) CW complex.
* `RelCWComplex.Subcomplex.instCompletelyDistribLattice`: for every (relative) CW complex `C`,
  the space of subcomplexes `Subcomplex C` is a completely distributive lattice.

## References
* [K. Jänich, *Topology*][Janich1984]
-/

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

lemma RelCWComplex.Subcomplex.closedCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    closedCell n i ⊆ E := by
  rw [← closure_openCell_eq_closedCell, E.closed.closure_subset_iff, ← E.union]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n
    (subset_iUnion (fun (j : ↑(E.I n)) ↦ openCell (C := C) n j) ⟨i, hi⟩)

lemma RelCWComplex.Subcomplex.openCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    openCell n i ⊆ E :=
  (openCell_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

lemma RelCWComplex.Subcomplex.cellFrontier_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    cellFrontier n i ⊆ E :=
  (cellFrontier_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

/-- A subcomplex is the union of its closed cells and its base. -/
lemma RelCWComplex.Subcomplex.union_closedCell [T2Space X] [RelCWComplex C D] (E : Subcomplex C) :
    D ∪ ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply union_subset E.base_subset
    exact iUnion₂_subset fun n i ↦ closedCell_subset_of_mem E i.2
  · rw [← E.union]
    apply union_subset_union_right
    apply iUnion₂_mono fun n i ↦ ?_
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
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    refine @pairwiseDisjoint' _ _ C D _ ⟨n, i⟩ trivial ⟨m, j⟩ trivial ?_
    exact Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) |>.ne hne
  disjointBase' n i := disjointBase' (C := C) n i
  mapsTo := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) n i with ⟨J, hJ⟩
    use fun m ↦ Finset.preimage (J m) Subtype.val Subtype.val_injective.injOn
    rw [mapsTo_iff_image_subset]
    intro x hx
    specialize hJ hx
    simp_rw [iUnion_coe_set, mem_union, mem_iUnion, Finset.mem_preimage, exists_prop,
      Decidable.or_iff_not_imp_left] at hJ ⊢
    intro h
    specialize hJ h
    obtain ⟨m, hmn, j, hj, hxj⟩ := hJ
    suffices j ∈ E.I m from ⟨m, hmn, j, this, hj, openCell_subset_closedCell _ _ hxj⟩
    have : x ∈ (E : Set X) := E.cellFrontier_subset_of_mem i.2 hx
    by_contra hj'
    exact E.disjoint_openCell_subcomplex_of_not_mem hj' |>.notMem_of_mem_left hxj this
  closed' A hA h := by
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      (subset_trans hA (subset_complex (C := C) E)) h.2
    intro n _ j
    by_cases hj : j ∈ E.I n
    · exact Or.intro_right _ (h.1 n ⟨j, hj⟩)
    · exact Or.intro_left _ ((disjoint_openCell_subcomplex_of_not_mem E hj).symm.mono_left hA)
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
    Subtype.finite

instance RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] [FiniteDimensional C] (E : Subcomplex C) :
    FiniteDimensional (E : Set X) where
  eventually_isEmpty_cell := by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    simp [isEmpty_subtype]

/-- A subcomplex of a finite CW complex is again finite. -/
instance RelCWComplex.Subcomplex.finite_subcomplex_of_finite [T2Space X] [RelCWComplex C D]
    [Finite C] (E : Subcomplex C) : Finite (E : Set X) :=
  finite_of_finiteDimensional_finiteType _

section Lattice

@[simps -isSimp]
protected def RelCWComplex.Subcomplex.sup [RelCWComplex C D] (E F : Subcomplex C) :
    Subcomplex C where
  carrier := E ∪ F
  I n := E.I n ∪ F.I n
  closed' := (closed E).union (closed F)
  union' := by
    simp only [iUnion_coe_set, mem_union, iUnion_or, iUnion_union_distrib, ← union]
    rw [union_assoc, ← union_assoc _ D, union_comm _ D, union_assoc, ← union_assoc _ D,
      union_self]

@[simps -isSimp]
protected def RelCWComplex.Subcomplex.inf [RelCWComplex C D] (E F : Subcomplex C) :
    Subcomplex C where
  carrier := E ∩ F
  I n := E.I n ∩ F.I n
  closed' := (closed E).inter (closed F)
  union' := by
    simp only [iUnion_coe_set, mem_inter_iff, iUnion_and, ← union]
    rw [inter_union_distrib_left, union_inter_cancel_left, union_inter_distrib_left, ← union_assoc,
      union_self, ← union_inter_distrib_left]
    congrm D ∪ ?_
    apply subset_antisymm
    · refine Subset.trans ?_ iUnion_inter_subset
      apply iUnion_mono
      intro n
      refine Subset.trans ?_ iUnion_inter_subset
      apply iUnion_mono
      intro i
      simp only [subset_inter_iff, iUnion_subset_iff, subset_refl, implies_true, and_true]
      exact fun hi hi' ↦ subset_iUnion_of_subset hi Subset.rfl
    · intro x
      simp only [mem_inter_iff, mem_iUnion, exists_prop, and_imp, forall_exists_index]
      intro n i hi hxi m j hj hxj
      use n, i, hi
      refine ⟨?_, hxi⟩
      suffices (⟨n, i⟩ : Σ n, cell C n) = ⟨m, j⟩ by aesop
      apply eq_of_not_disjoint_openCell
      rw [not_disjoint_iff]
      exact ⟨x, hxi, hxj⟩

instance RelCWComplex.Subcomplex.instDistribLattice [RelCWComplex C D] :
    DistribLattice (Subcomplex C) :=
  {(inferInstance : PartialOrder (Subcomplex C)) with
    sup E F := RelCWComplex.Subcomplex.sup E F
    le_sup_left E F := by
      rw [← SetLike.coe_subset_coe, coe_sup]
      exact subset_union_left
    le_sup_right E F := by
      rw [← SetLike.coe_subset_coe, coe_sup]
      exact subset_union_right
    sup_le E F G hEG hFG := by
      rw [← SetLike.coe_subset_coe]
      simp [hEG, hFG, coe_sup]
    inf E F := RelCWComplex.Subcomplex.inf E F
    inf_le_left E F := by
      rw [← SetLike.coe_subset_coe, coe_inf]
      exact inter_subset_left
    inf_le_right E F := by
      rw [← SetLike.coe_subset_coe, coe_inf]
      exact inter_subset_right
    le_inf E F G hEF hEG := by
      rw [← SetLike.coe_subset_coe]
      simp [hEF, hEG, coe_inf]
    le_sup_inf E F G := by
      rw [← SetLike.coe_subset_coe]
      simp only [min, SemilatticeInf.inf, max, coe_inf, coe_sup]
      rw [← union_inter_distrib_left]
    }

/-- Auxiliary definition used to define `top` in `Subcomplex C`. -/
@[simps -isSimp]
protected def RelCWComplex.Subcomplex.top' [T2Space X] [RelCWComplex C D] : Subcomplex C where
  carrier := C
  I n := univ
  closed' := isClosed
  union' := by simp [← union_iUnion_openCell_eq_complex]

/-- Auxiliary definition used to define `bot` in `Subcomplex C`. -/
@[simps -isSimp]
protected def RelCWComplex.Subcomplex.bot' [RelCWComplex C D] : Subcomplex C where
  carrier := D
  I n := ∅
  closed' := isClosedBase C
  union' := by simp

/-- Auxiliary definition used to define `sSup` in `Subcomplex C`. -/
@[simps! -isSimp]
protected def RelCWComplex.Subcomplex.sSup' [T2Space X] [RelCWComplex C D]
    (S : Set (Subcomplex C)) : Subcomplex C :=
  mk' C (D ∪ ⋃ (E ∈ S), E) (fun n ↦ ⋃ (E ∈ S), E.I n)
    (by
      intro n ⟨i, hi⟩
      apply subset_union_of_subset_right
      simp_rw [mem_iUnion] at hi
      obtain ⟨E, hE, hEj⟩ := hi
      apply subset_iUnion_of_subset E
      apply subset_iUnion_of_subset hE
      rw [← E.union_closedCell (C := C)]
      apply subset_union_of_subset_right
      exact subset_iUnion_of_subset n (subset_iUnion
        (fun (j : ↑(E.I n)) ↦ closedCell (C := C) n ↑j) ⟨i, hEj⟩))
    (by
      simp_rw [← Subcomplex.union]
      rw [← iUnion_subtype (p := fun E ↦ E ∈ S)
        (s := fun E ↦ D ∪ ⋃ n, ⋃ (j : E.1.I n), openCell n j.1)]
      by_cases h : Nonempty S
      · rw [← union_iUnion, ← union_assoc, union_self, iUnion_comm]
        congrm D ∪ ?_
        apply iUnion_congr fun n ↦ ?_
        simp_rw [iUnion_subtype, mem_iUnion, iUnion_exists]
        rw [iUnion_comm]
        apply iUnion_congr fun E ↦ ?_
        rw [iUnion_comm]
      · simp_all)

/-- Auxiliary definition used to define `sInf` in `Subcomplex C`. -/
@[simps -isSimp]
protected def RelCWComplex.Subcomplex.sInf' [T2Space X] [RelCWComplex C D]
    (S : Set (Subcomplex C)) : Subcomplex C where
  carrier := C ∩ ⋂ (E ∈ S), E
  I n := ⋂ (E ∈ S), E.I n
  closed' := isClosed.inter (isClosed_biInter (fun E _ ↦ closed E))
  union' := by
    rw [← iInter_subtype (p := fun E ↦ E ∈ S) (s := fun E ↦ (E: Set X))]
    by_cases h : Nonempty S
    · simp_rw [inter_iInter, inter_eq_right.2 (subset_complex _), ← Subcomplex.union,
        ← union_iInter]
      congrm D ∪ ?_
      simp_rw [iUnion_subtype, mem_iInter]
      ext x
      simp only [mem_iUnion, exists_prop, iInter_coe_set, mem_iInter]
      constructor
      · intro ⟨n, i, hi, hx⟩ E hE
        exact ⟨n, i, hi E hE, hx⟩
      · intro h'
        let ⟨E, hE⟩ := Classical.choice h
        obtain ⟨n, i, hi, hx⟩ := h' E hE
        use n, i
        refine ⟨?_, hx⟩
        intro F hF
        obtain ⟨m, j, hj, hx'⟩ := h' F hF
        suffices (⟨n, i⟩ : Σ n, cell C n) = ⟨m, j⟩ by aesop
        apply eq_of_not_disjoint_openCell
        rw [not_disjoint_iff]
        exact ⟨x, hx, hx'⟩
    · simp_all only [nonempty_subtype, not_exists, iUnion_coe_set, iInter_of_empty, iInter_univ,
      mem_univ, iUnion_true, iInter_coe_set, inter_univ]
      exact union_iUnion_openCell_eq_complex

protected def RelCWComplex.Subcomplex.CompletelyDistribLattice.MinimalAxioms [T2Space X]
    [RelCWComplex C D] : CompletelyDistribLattice.MinimalAxioms (Subcomplex C) :=
  { __ := (inferInstance : DistribLattice (Subcomplex C))
    sSup := Topology.RelCWComplex.Subcomplex.sSup'
    le_sSup S E hES := by
      simp only [← SetLike.coe_subset_coe, coe_sSup']
      apply subset_union_of_subset_right
      exact subset_biUnion_of_mem hES
    sSup_le S E hE := by simp_all [← SetLike.coe_subset_coe, base_subset_complex, coe_sSup']
    sInf := Topology.RelCWComplex.Subcomplex.sInf'
    sInf_le S E hES := by
      simp only [← SetLike.coe_subset_coe, coe_sInf']
      apply inter_subset_right.trans
      exact biInter_subset_of_mem hES
    le_sInf SDiff E hE := by simp_all [← SetLike.coe_subset_coe, subset_complex, coe_sInf']
    top := Topology.RelCWComplex.Subcomplex.top'
    bot := Topology.RelCWComplex.Subcomplex.bot'
    le_top E := by simp [← SetLike.coe_subset_coe, subset_complex, coe_top']
    bot_le E := by simp [← SetLike.coe_subset_coe, base_subset_complex]
    iInf_iSup_eq {ι} f E := by
      simp_rw [eq_iff, iSup, coe_sSup', iInf, coe_sInf']
      by_cases h : Nonempty ι
      · simp only [mem_range, iInter_exists, iInter_iInter_eq', coe_sSup', iUnion_exists,
          iUnion_iUnion_eq', inter_iInter, inter_union_distrib_left,
          inter_eq_right.2 (base_subset_complex (C := C)), inter_iUnion, coe_sInf']
        by_cases h' : ∀ a, Nonempty (f a)
        · simp only [union_iUnion, union_iInter]
          ext x
          simp only [mem_iUnion, mem_iInter]
          constructor
          · intro hE
            use (fun i ↦ (hE i).choose)
            intro i
            exact (hE i).choose_spec
          · intro ⟨g, hg⟩ i
            use g i, hg i
        · simp_all only [not_forall, not_nonempty_iff, isEmpty_pi, iUnion_of_empty, union_empty]
          apply subset_antisymm
          · obtain ⟨a, ha⟩ := h'
            apply iInter_subset_of_subset a
            simp
          · apply subset_iInter
            intro i
            exact subset_union_left
      · simp_all only [not_nonempty_iff, mem_range, IsEmpty.exists_iff, iInter_of_empty,
        iInter_univ, inter_univ, iUnion_exists, iUnion_iUnion_eq', coe_sInf']
        ext x
        simp [mem_union, mem_iUnion, exists_const, iff_or_self]
        exact fun h ↦ base_subset_complex h
    }

instance RelCWComplex.Subcomplex.instCompletelyDistribLattice [T2Space X]
    [RelCWComplex C D] : CompletelyDistribLattice (Subcomplex C) :=
  CompletelyDistribLattice.ofMinimalAxioms
    RelCWComplex.Subcomplex.CompletelyDistribLattice.MinimalAxioms

@[simp]
lemma RelCWComplex.Subcomplex.coe_top [T2Space X] [RelCWComplex C D] :
    (⊤ : Subcomplex C) = C := by
  simp [instCompletelyDistribLattice, CompletelyDistribLattice.MinimalAxioms]
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.top_I [T2Space X] [RelCWComplex C D] (n : ℕ) :
    (⊤ : Subcomplex C).I n = univ := by
  simp [instCompletelyDistribLattice, CompletelyDistribLattice.MinimalAxioms]
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.coe_bot [T2Space X] [RelCWComplex C D] :
    (⊥ : Subcomplex C) = D := by
  simp [instCompletelyDistribLattice, CompletelyDistribLattice.MinimalAxioms]
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.bot_I [T2Space X] [RelCWComplex C D] (n : ℕ) :
    (⊥ : Subcomplex C).I n = ∅ := by
  simp [instCompletelyDistribLattice, CompletelyDistribLattice.MinimalAxioms]
  rfl

instance RelCWComplex.Subcomplex.finite_bot [T2Space X] [RelCWComplex C D] :
    Finite ((⊥ : Subcomplex C) : Set X) where
  eventually_isEmpty_cell := by
    simp_rw [cell_def]
    simp
  finite_cell n := by
    simp [cell_def, Finite.of_subsingleton]

lemma RelCWComplex.Subcomplex.iSup_carrier [T2Space X] [RelCWComplex C D]
    {J : Type*} (f : J → Subcomplex C) :
    ((⨆ (j : J), f j) : Subcomplex C) = D ∪ ⋃ j, f j := by
  simp [iSup, CompleteLattice.toConditionallyCompleteLattice,
    CompletelyDistribLattice.toCompleteLattice, instCompletelyDistribLattice,
    CompletelyDistribLattice.MinimalAxioms, coe_sSup']

@[simp]
lemma RelCWComplex.Subcomplex.iSup_coe_eq_of_nonempty [T2Space X] [RelCWComplex C D]
    {J : Type*} [Nonempty J] (f : J → Subcomplex C) :
    (((⨆ (j : J), f j) : Subcomplex C) : Set X) = ⋃ j, f j := by
  simp only [iSup_carrier, union_eq_right]
  apply subset_iUnion_of_subset (Classical.choice (α := J) inferInstance)
  exact base_subset_complex

@[simp]
lemma RelCWComplex.Subcomplex.iSup_coe_eq_of_empty [T2Space X] [RelCWComplex C D]
    {J : Type*} [IsEmpty J] (f : J → Subcomplex C) :
    ⨆ (j : J), f j = ⊥ := by
  ext x
  simp [← SetLike.mem_coe, iSup_carrier]

@[simp]
lemma CWComplex.Subcomplex.coe_iSup [T2Space X] [CWComplex C]
    {J : Type*} (f : J → Subcomplex C) :
    (((⨆ (j : J), f j) : Subcomplex C) : Set X) = ⋃ j, f j := by
  simp [RelCWComplex.Subcomplex.iSup_carrier]

@[simp]
lemma RelCWComplex.Subcomplex.iSup_I [T2Space X] [RelCWComplex C D]
    {J : Type*} (f : J → Subcomplex C) (n : ℕ) :
    (⨆ (j : J), f j).I n = ⋃ (j : J), (f j).I n := by
  simp [iSup, CompleteLattice.toConditionallyCompleteLattice,
    CompletelyDistribLattice.toCompleteLattice, instCompletelyDistribLattice,
    CompletelyDistribLattice.MinimalAxioms, sSup'_I]

lemma RelCWComplex.Subcomplex.coe_iInf [T2Space X] [RelCWComplex C D]
    {J : Type*} (f : J → Subcomplex C) :
    (((⨅ (j : J), f j) : Subcomplex C) : Set X) = C ∩ ⋂ j, f j := by
  simp [iInf, CompleteLattice.toConditionallyCompleteLattice,
    CompletelyDistribLattice.toCompleteLattice,
    instCompletelyDistribLattice, CompletelyDistribLattice.MinimalAxioms, coe_sInf']

@[simp]
lemma RelCWComplex.Subcomplex.iInf_coe_eq_of_nonempty [T2Space X] [RelCWComplex C D]
    {J : Type*} [Nonempty J] (f : J → Subcomplex C) :
    (((⨅ (j : J), f j) : Subcomplex C) : Set X) = ⋂ j, f j := by
  simp only [coe_iInf, inter_eq_right]
  apply iInter_subset_of_subset (Classical.choice (α := J) inferInstance)
  exact subset_complex _

@[simp]
lemma RelCWComplex.Subcomplex.iInf_coe_eq_of_empty [T2Space X] [RelCWComplex C D]
    {J : Type*} [IsEmpty J] (f : J → Subcomplex C) :
    ⨅ (j : J), f j = ⊤ := by
  ext
  simp only [← SetLike.mem_coe, coe_iInf, coe_top, iInter_of_empty, inter_univ]

@[simp]
lemma RelCWComplex.Subcomplex.iInf_I [T2Space X] [RelCWComplex C D]
    {J : Type*} (f : J → Subcomplex C) (n : ℕ) :
    (⨅ (j : J), f j).I n = ⋂ (j : J), (f j).I n := by
  simp [iInf, CompleteLattice.toConditionallyCompleteLattice,
    CompletelyDistribLattice.toCompleteLattice,
    instCompletelyDistribLattice, CompletelyDistribLattice.MinimalAxioms, sInf'_I]

/-- A finite union of finite-dimensional subcomplexes is again a finite-dimensional subcomplex. -/
instance RelCWComplex.Subcomplex.finiteDimensional_finite_iSup_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] {J : Type*} [_root_.Finite J]
    {f : J → Subcomplex C} [hf : ∀ (j : J), FiniteDimensional (f j : Set X)] :
    FiniteDimensional (((⨆ j : J, f j) : Subcomplex C) : Set X) where
  eventually_isEmpty_cell := by
    have h j := (hf j).eventually_isEmpty_cell
    simp only [cell_def, isEmpty_coe_sort, Filter.eventually_iff,
      Filter.mem_atTop_sets, ge_iff_le, mem_setOf_eq, iSup_I, iUnion_eq_empty, setOf_forall,
      Filter.iInter_mem] at h ⊢
    exact h

/-- A finite union of subcomplexes of finite type is again a subcomplex of finite type. -/
instance RelCWComplex.Subcomplex.finiteType_finite_iSup_of_finiteType [T2Space X]
    [RelCWComplex C D] {J : Type*} [_root_.Finite J] {f : J → Subcomplex C}
    [hf : ∀ (j : J), FiniteType (f j : Set X)] :
    FiniteType (X := X) ↑(⨆ j, f j) where
 finite_cell := by
    have h j := (hf j).finite_cell
    intro n
    simp only [cell_def, iSup_I] at h ⊢
    exact Finite.Set.finite_iUnion _

/-- A nonempty intersection of subcomplexes where one is finite dimensional is again a
finite-dimensional subcomplex. -/
lemma RelCWComplex.Subcomplex.finiteDimensional_iInf_of_exists_finiteDimensional
    [T2Space X] [RelCWComplex C D] {J : Type*} [Nonempty J] {f : J → Subcomplex C} (j : J)
    [hf : FiniteDimensional (f j : Set X)] :
    FiniteDimensional (((⨅ j : J, f j) : Subcomplex C) : Set X) where
  eventually_isEmpty_cell := by
    have h := hf.eventually_isEmpty_cell
    simp_all only [cell_def, isEmpty_coe_sort, Filter.eventually_atTop, ge_iff_le,
      iInf_I]
    obtain ⟨n, hn⟩ := h
    use n
    intro m hm
    rw [← subset_empty_iff]
    exact iInter_subset_of_subset j (subset_empty_iff.2 (hn m hm))

/-- A nonempty intersection of finite-dimensional subcomplexes is again a finite-dimensional
subcomplex. -/
instance RelCWComplex.Subcomplex.finiteDimensional_iInf_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] {J : Type*} [Nonempty J] {f : J → Subcomplex C}
    [hf : ∀ j, FiniteDimensional (f j : Set X)] :
    FiniteDimensional (((⨅ j : J, f j) : Subcomplex C) : Set X) :=
  let j := Classical.choice (α := J) inferInstance
  finiteDimensional_iInf_of_exists_finiteDimensional j

/-- A nonempty intersection of subcomplexes where one is of finite type is again of finite type. -/
lemma RelCWComplex.Subcomplex.finiteType_iInf_of_exists_finiteType
    [T2Space X] [RelCWComplex C D] {J : Type*} [Nonempty J] {f : J → Subcomplex C} (j : J)
    [hf : FiniteType (f j : Set X)] :
    FiniteType (((⨅ j : J, f j) : Subcomplex C) : Set X) where
  finite_cell := by
    intro n
    have := FiniteType.finite_cell (C := (f j : Set X)) (D := D) n
    simp_all only [cell_def, finite_coe_iff, iInf_I]
    exact Finite.subset this (iInter_subset _ j)

/-- A nonempty intersection of subcomplexes of finite type is again of finite type. -/
instance RelCWComplex.Subcomplex.finiteType_iInf_of_finiteType
    [T2Space X] [RelCWComplex C D] {J : Type*} [Nonempty J] {f : J → Subcomplex C}
    [hf : ∀ j, FiniteType (f j : Set X)] :
    FiniteType (((⨅ j : J, f j) : Subcomplex C) : Set X) :=
  let j := Classical.choice (α := J) inferInstance
  finiteType_iInf_of_exists_finiteType j

/-- A nonempty intersection of subcomplexes where one is finite is again a finite subcomplex. -/
lemma RelCWComplex.Subcomplex.finite_iInf_of_exists_finite
    [T2Space X] [RelCWComplex C D] {J : Type*} [Nonempty J] {f : J → Subcomplex C} (j : J)
    [hf : Finite (f j : Set X)] :
    Finite (((⨅ j : J, f j) : Subcomplex C) : Set X) :=
  let _ := finiteDimensional_iInf_of_exists_finiteDimensional (f := f) j
  let _ := finiteType_iInf_of_exists_finiteType (f := f) j
  finite_of_finiteDimensional_finiteType _

end Lattice

instance RelCWComplex.Subcomplex.instInhabited [T2Space X] [RelCWComplex C D] :
    Inhabited (Subcomplex C) :=
  ⟨⊥⟩

namespace CWComplex.Subcomplex

export RelCWComplex.Subcomplex (closedCell_subset_of_mem openCell_subset_of_mem
  cellFrontier_subset_of_mem disjoint_openCell_subcomplex_of_not_mem subset_complex
  finiteType_subcomplex_of_finiteType finiteDimensional_subcomplex_of_finiteDimensional
  finite_subcomplex_of_finite instDistribLattice instCompletelyDistribLattice coe_top top_I coe_bot
  bot_I finite_bot iSup_I finiteDimensional_finite_iSup_of_finiteDimensional
  finiteType_finite_iSup_of_finiteType coe_iInf iInf_coe_eq_of_nonempty iInf_coe_eq_of_empty iInf_I
  finiteDimensional_iInf_of_exists_finiteDimensional finiteDimensional_iInf_of_finiteDimensional
  finiteType_iInf_of_exists_finiteType finiteType_iInf_of_finiteType finite_iInf_of_exists_finite
  instInhabited)

end CWComplex.Subcomplex

end Topology
