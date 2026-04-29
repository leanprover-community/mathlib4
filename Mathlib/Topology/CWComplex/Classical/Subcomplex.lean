/-
Copyright (c) 2025 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW complexes.
The definition of subcomplexes is in the file `Mathlib/Topology/CWComplex/Classical/Basic.lean`.

## Main results
* `RelCWComplex.Subcomplex.instRelCWComplex`: a subcomplex of a (relative) CW complex is again a
  (relative) CW complex.
* `RelCWComplex.Subcomplex.instCompletelyDistribLattice`: for every (relative) CW complex `C`,
  the space of subcomplexes `Subcomplex C` is a completely distributive lattice.

## References
* [K. Jänich, *Topology*][Janich1984]
-/

@[expose] public section

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
  (empty_union _).symm.trans (RelCWComplex.Subcomplex.union_closedCell E)

lemma RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (h : i ∉ E.I n) : Disjoint (openCell n i) E := by
  simp_rw [← union, disjoint_union_right, disjoint_iUnion_right]
  exact ⟨disjointBase n i , fun _ _ ↦ disjoint_openCell_of_ne (by lia)⟩

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

instance RelCWComplex.Subcomplex.instMax [RelCWComplex C D] : Max (Subcomplex C) where
  max E F := {
    carrier := E ∪ F
    I n := E.I n ∪ F.I n
    closed' := (closed E).union (closed F)
    union' :=  by
      simp [mem_union, iUnion_or, iUnion_union_distrib, ← union, ← union_assoc _ D, union_comm,
        union_assoc]}

lemma RelCWComplex.Subcomplex.coe_sup [RelCWComplex C D] (E F : Subcomplex C) :
    (((E ⊔ F) : Subcomplex C) : Set X) = ↑E ∪ ↑F :=
  rfl

lemma RelCWComplex.Subcomplex.sup_I [RelCWComplex C D] (E F : Subcomplex C) (n : ℕ) :
    (E ⊔ F).I n = E.I n ∪ F.I n :=
  rfl

instance RelCWComplex.Subcomplex.instMin [RelCWComplex C D] : Min (Subcomplex C) where
  min E F := {
    carrier := E ∩ F
    I n := E.I n ∩ F.I n
    closed' := (closed E).inter (closed F)
    union' := by
      simp_rw [← Subcomplex.union, ← union_inter_distrib_left, iUnion_coe_set]
      congrm D ∪ ?_
      calc
        ⋃ n, ⋃ i ∈ (E.I n ∩ F.I n), openCell n i
        _ = ⋃ (x ∈ {x : Σ n, cell C n | x.2 ∈ E.I x.1} ∩ {x : Σ n, cell C n | x.2 ∈ F.I x.1}),
            openCell x.1 x.2 := by
          simp [iUnion_sigma]
        _ = (⋃ n, ⋃ i ∈ E.I n, openCell n i) ∩ ⋃ n, ⋃ i ∈ F.I n, openCell n i := by
          rw [biUnion_inter_of_pairwise_disjoint
            (fun ⟨n, j⟩ ⟨m, i⟩ h ↦ disjoint_openCell_of_ne h)]
          simp [iUnion_sigma]}

lemma RelCWComplex.Subcomplex.coe_inf [RelCWComplex C D] (E F : Subcomplex C) :
    (((E ⊓ F) : Subcomplex C) : Set X) = ↑E ∩ ↑F :=
  rfl

lemma RelCWComplex.Subcomplex.inf_I [RelCWComplex C D] (E F : Subcomplex C) (n : ℕ) :
    (E ⊓ F).I n = E.I n ∩ F.I n :=
  rfl

instance RelCWComplex.Subcomplex.instLattice [RelCWComplex C D] : Lattice (Subcomplex C) where
  sup E F := E ⊔ F
  inf E F := E ⊓ F
  le_sup_left E F := by simp [← SetLike.coe_subset_coe, coe_sup]
  le_sup_right E F := by simp [← SetLike.coe_subset_coe, coe_sup]
  sup_le E F G hE hF := by simp_all [← SetLike.coe_subset_coe, coe_sup]
  inf_le_left E F := by simp [← SetLike.coe_subset_coe, coe_inf]
  inf_le_right E F := by simp [← SetLike.coe_subset_coe, coe_inf]
  le_inf E F G hE hF := by simp_all [← SetLike.coe_subset_coe, coe_inf]

instance RelCWComplex.Subcomplex.instDistribLattice [RelCWComplex C D] :
    DistribLattice (Subcomplex C) where
  le_sup_inf E F G := by
    simp [← SetLike.coe_subset_coe, coe_sup, coe_inf, union_inter_distrib_left]

@[simps -isSimp]
instance RelCWComplex.Subcomplex.instTop [T2Space X] [RelCWComplex C D] : Top (Subcomplex C) where
  top := {
    carrier := C
    I n := univ
    closed' := isClosed
    union' := by simp [← union_iUnion_openCell_eq_complex]
  }

@[simps -isSimp]
instance RelCWComplex.Subcomplex.instBot [RelCWComplex C D] : Bot (Subcomplex C) where
  bot := {
    carrier := D
    I n := ∅
    closed' := isClosedBase C
    union' := by simp
  }

instance RelCWComplex.Subcomplex.finite_bot [T2Space X] [RelCWComplex C D] :
    Finite ((⊥ : Subcomplex C) : Set X) where
  eventually_isEmpty_cell := by simp [cell_def, bot_I]
  finite_cell n := by simp [cell_def, bot_I n, Finite.of_subsingleton]

@[simps! -isSimp]
instance RelCWComplex.Subcomplex.instSupSet [T2Space X] [RelCWComplex C D] :
    SupSet (Subcomplex C) where
  sSup S := mk' C (D ∪ ⋃ (E ∈ S), E) (fun n ↦ ⋃ (E ∈ S), E.I n)
    (by
      intro n ⟨i, hi⟩
      apply subset_union_of_subset_right
      simp_rw [mem_iUnion] at hi
      obtain ⟨E, hE, hEj⟩ := hi
      exact subset_iUnion₂_of_subset E hE <| E.closedCell_subset_of_mem hEj)
    (by
      by_cases h : Nonempty S
      · simp_rw [← Subcomplex.union, biUnion_eq_iUnion, union_iUnion, ← union_assoc,
          union_self, ← union_iUnion, iUnion_subtype, biUnion_iUnion, iUnion_comm (ι := ℕ)]
      · simp_all)

lemma RelCWComplex.Subcomplex.coe_iSup [T2Space X] [RelCWComplex C D]
    {J : Type*} (f : J → Subcomplex C) :
    ((⨆ (j : J), f j) : Subcomplex C) = D ∪ ⋃ j, f j := by
  simp [iSup, coe_sSup]

@[simp]
lemma RelCWComplex.Subcomplex.coe_iSup_eq_of_nonempty [T2Space X] [RelCWComplex C D]
    {J : Type*} [Nonempty J] (f : J → Subcomplex C) :
    (((⨆ (j : J), f j) : Subcomplex C) : Set X) = ⋃ j, f j := by
  simp only [coe_iSup, union_eq_right]
  apply subset_iUnion_of_subset (Classical.choice (α := J) inferInstance)
  exact base_subset_complex

@[simp]
lemma CWComplex.Subcomplex.coe_iSup [T2Space X] [CWComplex C]
    {J : Type*} (f : J → Subcomplex C) :
    (((⨆ (j : J), f j) : Subcomplex C) : Set X) = ⋃ j, f j := by
  simp [RelCWComplex.Subcomplex.coe_iSup]

@[simp]
lemma RelCWComplex.Subcomplex.iSup_I [T2Space X] [RelCWComplex C D]
    {J : Type*} (f : J → Subcomplex C) (n : ℕ) :
    (⨆ (j : J), f j).I n = ⋃ (j : J), (f j).I n := by
  simp [iSup, sSup_I]

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

@[simps! -isSimp]
instance RelCWComplex.Subcomplex.instInfSet [T2Space X] [RelCWComplex C D] :
    InfSet (Subcomplex C) where
  sInf S := {
    carrier := C ∩ ⋂ (E ∈ S), E
    I n := ⋂ (E ∈ S), E.I n
    closed' := isClosed.inter (isClosed_biInter (fun E _ ↦ closed E))
    union' := by
      rw [← iInter_subtype (p := fun E ↦ E ∈ S) (s := fun E ↦ (E: Set X))]
      by_cases h : Nonempty S
      · simp_rw [inter_iInter, inter_eq_right.2 (subset_complex _), ← Subcomplex.union,
          ← union_iInter]
        congrm D ∪ ?_
        simp_rw [iUnion_subtype]
        calc
          ⋃ n, ⋃ x ∈ ⋂ E ∈ S, E.I n, openCell n x
          _ = ⋃ x ∈ ⋂ (E : { x // x ∈ S }), {x : Σ n, cell C n | x.2 ∈ E.1.I x.1},
              openCell x.1 x.2 := by
            simp [iUnion_sigma]
          _ = ⋂ (E : { x // x ∈ S }), ⋃ n, ⋃ x ∈ E.1.I n, openCell n x := by
            rw [biUnion_iInter_of_pairwise_disjoint
              (fun ⟨n, j⟩ ⟨m, i⟩ h ↦ disjoint_openCell_of_ne h)]
            simp [iUnion_sigma]
      · simp_all only [nonempty_subtype, not_exists, iUnion_coe_set, iInter_of_empty, iInter_univ,
          mem_univ, iUnion_true, iInter_coe_set, inter_univ]
        exact union_iUnion_openCell_eq_complex
  }

lemma RelCWComplex.Subcomplex.coe_iInf [T2Space X] [RelCWComplex C D]
    {J : Type*} (f : J → Subcomplex C) :
    (((⨅ (j : J), f j) : Subcomplex C) : Set X) = C ∩ ⋂ j, f j := by
  simp [iInf, coe_sInf]

@[simp]
lemma RelCWComplex.Subcomplex.coe_iInf_eq_of_nonempty [T2Space X] [RelCWComplex C D]
    {J : Type*} [Nonempty J] (f : J → Subcomplex C) :
    (((⨅ (j : J), f j) : Subcomplex C) : Set X) = ⋂ j, f j := by
  simp only [coe_iInf, inter_eq_right]
  apply iInter_subset_of_subset (Classical.choice (α := J) inferInstance)
  exact subset_complex _

@[simp]
lemma RelCWComplex.Subcomplex.iInf_I [T2Space X] [RelCWComplex C D]
    {J : Type*} (f : J → Subcomplex C) (n : ℕ) :
    (⨅ (j : J), f j).I n = ⋂ (j : J), (f j).I n := by
  simp [iInf, sInf_I]

/-- An intersection of subcomplexes where one is finite dimensional is again a finite-dimensional
subcomplex. -/
lemma RelCWComplex.Subcomplex.finiteDimensional_iInf_of_exists_finiteDimensional
    [T2Space X] [RelCWComplex C D] {J : Type*} {f : J → Subcomplex C} (j : J)
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

/-- An intersection of subcomplexes where one is of finite type is again of finite type. -/
lemma RelCWComplex.Subcomplex.finiteType_iInf_of_exists_finiteType
    [T2Space X] [RelCWComplex C D] {J : Type*} {f : J → Subcomplex C} (j : J)
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

/-- An intersection of subcomplexes where one is finite is again a finite subcomplex. -/
lemma RelCWComplex.Subcomplex.finite_iInf_of_exists_finite
    [T2Space X] [RelCWComplex C D] {J : Type*} {f : J → Subcomplex C} (j : J)
    [hf : Finite (f j : Set X)] :
    Finite (((⨅ j : J, f j) : Subcomplex C) : Set X) :=
  let _ := finiteDimensional_iInf_of_exists_finiteDimensional (f := f) j
  let _ := finiteType_iInf_of_exists_finiteType (f := f) j
  finite_of_finiteDimensional_finiteType _

instance RelCWComplex.Subcomplex.instCompleteLattice [T2Space X] [RelCWComplex C D] :
    CompleteLattice (Subcomplex C) where
  isLUB_sSup S := by
    rw [isLUB_iff_le_iff]
    intro E
    constructor
    · intro hES F hF
      exact (subset_union_of_subset_right (subset_biUnion_of_mem hF) _).trans hES
    · intro h
      simpa [← SetLike.coe_subset_coe, coe_sSup, base_subset_complex]
  isGLB_sInf S := by
    rw [isGLB_iff_le_iff]
    intro E
    constructor
    · intro hES F hF
      exact hES.trans (inter_subset_right.trans (biInter_subset_of_mem hF))
    · intro h
      simpa [← SetLike.coe_subset_coe, subset_complex, coe_sInf]
  le_top E := by simp [← SetLike.coe_subset_coe, subset_complex, coe_top]
  bot_le E := by simp [← SetLike.coe_subset_coe, base_subset_complex]

/-- An auxiliary definition to provide a `CompletelyDistribLattice` instance on subcomplexes. -/
protected def RelCWComplex.Subcomplex.CompletelyDistribLattice.MinimalAxioms [T2Space X]
    [RelCWComplex C D] : CompletelyDistribLattice.MinimalAxioms (Subcomplex C) where
  iInf_iSup_eq {ι} f E := by
    by_cases h : Nonempty ι
    · by_cases h' : ∀ a, Nonempty (f a)
      · have h'' := Classical.nonempty_pi.mpr h'
        simp [eq_iff, ← iInf_eq_iInter, ← iSup_eq_iUnion, iInf_iSup_eq]
      · push Not at h'
        have h'' := isEmpty_pi.mpr h'
        rcases h' with ⟨i, hi⟩
        rw [iSup_of_empty, eq_bot_iff]
        exact iInf_le_of_le i <| by rw [iSup_of_empty]
    · rw [not_nonempty_iff] at h
      simp [iInf_of_empty]

instance RelCWComplex.Subcomplex.instCompletelyDistribLattice [T2Space X]
    [RelCWComplex C D] : CompletelyDistribLattice (Subcomplex C) := fast_instance%
  { RelCWComplex.Subcomplex.instCompleteLattice with
    __ := CompletelyDistribLattice.ofMinimalAxioms
      RelCWComplex.Subcomplex.CompletelyDistribLattice.MinimalAxioms }

end Lattice

instance RelCWComplex.Subcomplex.instInhabited [RelCWComplex C D] :
    Inhabited (Subcomplex C) :=
  ⟨⊥⟩

namespace CWComplex.Subcomplex

export RelCWComplex.Subcomplex (closedCell_subset_of_mem openCell_subset_of_mem
  cellFrontier_subset_of_mem disjoint_openCell_subcomplex_of_not_mem subset_complex
  finiteType_subcomplex_of_finiteType finiteDimensional_subcomplex_of_finiteDimensional
  finite_subcomplex_of_finite instDistribLattice instCompletelyDistribLattice coe_top top_I coe_bot
  bot_I finite_bot iSup_I finiteDimensional_finite_iSup_of_finiteDimensional
  finiteType_finite_iSup_of_finiteType coe_iInf coe_iInf_eq_of_nonempty iInf_I
  finiteDimensional_iInf_of_exists_finiteDimensional finiteDimensional_iInf_of_finiteDimensional
  finiteType_iInf_of_exists_finiteType finiteType_iInf_of_finiteType finite_iInf_of_exists_finite
  instInhabited)

end CWComplex.Subcomplex

end Topology
