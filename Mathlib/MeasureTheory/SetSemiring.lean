/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.SupClosed

/-! # Semirings and rings of sets

A semi-ring of sets `C` (in the sense of measure theory) is a family of sets containing `∅`,
stable by intersection and such that for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of
finitely many sets in `C`. Note that a semi-ring of sets may not contain unions.

An important example of a semi-ring of sets is intervals in `ℝ`. The intersection of two intervals
is an interval (possibly empty). The union of two intervals may not be an interval.
The set difference of two intervals may not be an interval, but it will be a disjoint union of
two intervals.

A ring of sets is a set of sets containing `∅`, stable by union, set difference and intersection.

## Main definitions

* `MeasureTheory.IsSetSemiring C`: property of being a semi-ring of sets.
* `MeasureTheory.IsSetSemiring.disjointOfDiff hs ht`: for `s, t` in a semi-ring `C`
  (with `hC : IsSetSemiring C`) with `hs : s ∈ C`, `ht : t ∈ C`, this is a `Finset` of
  pairwise disjoint sets such that `s \ t = ⋃₀ hC.disjointOfDiff hs ht`.
* `MeasureTheory.IsSetSemiring.disjointOfDiffUnion hs hI`: for `hs : s ∈ C` and a finset
  `I` of sets in `C` (with `hI : ↑I ⊆ C`), this is a `Finset` of pairwise disjoint sets such that
  `s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion hs hI`.
* `MeasureTheory.IsSetSemiring.disjointOfUnion hJ`: for `hJ ⊆ C`, this is a
  `Finset` of pairwise disjoint sets such that `⋃₀ J = ⋃₀ hC.disjointOfUnion hJ`.

* `MeasureTheory.IsSetRing`: property of being a ring of sets.

## Main statements

* `MeasureTheory.IsSetSemiring.exists_disjoint_finset_sdiff_eq`: the existence of the `Finset` given
  by the definition `IsSetSemiring.disjointOfDiffUnion` (see above).
* `MeasureTheory.IsSetSemiring.disjointOfUnion_props`: In a `hC : IsSetSemiring C`,
  for a `J : Finset (Set α)` with `J ⊆ C`, there is
  for every `x in J` some `K x ⊆ C` finite, such that
  * `⋃ x ∈ J, K x` are pairwise disjoint and do not contain ∅,
  * `⋃ s ∈ K x, s ⊆ x`,
  * `⋃ x ∈ J, x = ⋃ x ∈ J, ⋃ s ∈ K x, s`.

-/

public section

open Finset Set

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

/-- A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `s \ t` is equal to a disjoint union of finitely many sets in `C`. -/
structure IsSetSemiring (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  inter_mem : ∀ s ∈ C, ∀ t ∈ C, s ∩ t ∈ C
  sdiff_eq_sUnion' : ∀ s ∈ C, ∀ t ∈ C,
    ∃ I : Finset (Set α), ↑I ⊆ C ∧ PairwiseDisjoint (I : Set (Set α)) id ∧ s \ t = ⋃₀ I

/-- A ring of sets `C` is a family of sets containing `∅`, stable by union and set difference.
It is then also stable by intersection (see `IsSetRing.inter_mem`). -/
structure IsSetRing (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  union_mem ⦃s t : Set α⦄ : s ∈ C → t ∈ C → s ∪ t ∈ C
  sdiff_mem ⦃s t : Set α⦄ : s ∈ C → t ∈ C → s \ t ∈ C

namespace IsSetRing

lemma inter_mem (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C := by
  rw [← sdiff_sdiff_right_self]; exact hC.sdiff_mem hs (hC.sdiff_mem hs ht)

lemma isSetSemiring (hC : IsSetRing C) : IsSetSemiring C where
  empty_mem := hC.empty_mem
  inter_mem := fun _ hs _ ht => hC.inter_mem hs ht
  sdiff_eq_sUnion' := by
    refine fun s hs t ht => ⟨{s \ t}, ?_, ?_, ?_⟩
    · simp only [coe_singleton, Set.singleton_subset_iff]
      exact hC.sdiff_mem hs ht
    · simp only [coe_singleton, pairwiseDisjoint_singleton]
    · simp only [coe_singleton, sUnion_singleton]

lemma biUnion_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hs : ∀ n ∈ S, s n ∈ C) :
    ⋃ i ∈ S, s i ∈ C := by
  classical
  induction S using Finset.induction with
  | empty => simp [hC.empty_mem]
  | insert i S _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS ↦ hs n (mem_insert_of_mem hnS))

lemma biInter_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hS : S.Nonempty) (hs : ∀ n ∈ S, s n ∈ C) :
    ⋂ i ∈ S, s i ∈ C := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons i S hiS _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?_
    exact h (fun n hnS ↦ hs.2 n hnS)

lemma finsetSup_mem (hC : IsSetRing C) {ι : Type*} {s : ι → Set α} {t : Finset ι}
    (hs : ∀ i ∈ t, s i ∈ C) :
    t.sup s ∈ C := by
  simpa using biUnion_mem hC _ hs

lemma partialSups_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι → Set α} (hs : ∀ n, s n ∈ C) (n : ι) :
    partialSups s n ∈ C := by
  simpa only [partialSups_apply, sup'_eq_sup] using hC.finsetSup_mem (fun i hi ↦ hs i)

lemma disjointed_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι → Set α} (hs : ∀ j, s j ∈ C) (i : ι) :
    disjointed s i ∈ C :=
  disjointedRec (fun _ j ht ↦ hC.sdiff_mem ht <| hs j) (hs i)

theorem iUnion_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biUnion_le_succ]; exact hC.union_mem hn (hs _)

theorem iInter_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biInter_le_succ]; exact hC.inter_mem hn (hs _)

theorem accumulate_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ i, s i ∈ C) (n : ℕ) :
    accumulate s n ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [accumulate_succ]; exact hC.union_mem hn (hs _)

end IsSetRing

namespace IsSetSemiring

lemma isPiSystem (hC : IsSetSemiring C) : IsPiSystem C := fun s hs t ht _ ↦ hC.inter_mem s hs t ht

theorem exists_finpartition_sdiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ∃ P : Finpartition (s \ t), ↑P.parts ⊆ C := by
  obtain ⟨I, hIC, hI, hst⟩ := hC.sdiff_eq_sUnion' s hs t ht
  refine ⟨.ofErase I (supIndep_iff_pairwiseDisjoint.mpr hI) ?_, ?_⟩
  · rw [sup_id_eq_sSup, sSup_eq_sUnion, hst]
  · grw [Finpartition.ofErase_parts, Finset.erase_subset, hIC]

@[deprecated (since := "2026-06-03")] alias exists_finpartition_diff := exists_finpartition_sdiff

theorem mem_supClosure_iff (hC : IsSetSemiring C) :
    s ∈ supClosure C ↔ ∃ P : Finpartition s, ↑P.parts ⊆ C where
  mp := by
    rintro ⟨S, hS, hSC, rfl⟩
    rw [sup'_eq_sup]
    clear hS
    induction S using Finset.induction with
    | empty =>
      rw [sup_empty]
      exact ⟨.empty _, hSC⟩
    | insert s S _ ih =>
      rw [coe_insert, insert_subset_iff] at hSC
      obtain ⟨hsC, hSC⟩ := hSC
      obtain ⟨P, hP⟩ := ih hSC
      rw [sup_insert, sup_comm, id]
      rcases eq_or_ne s ⊥ with rfl | hs
      · rw [sup_bot_eq]; exact ⟨P, hP⟩
      choose Q hQ using show ∀ t ∈ (P.avoid s).parts, ∃ Q : Finpartition t, ↑Q.parts ⊆ C by
        simp_rw [Finpartition.mem_avoid]
        rintro _ ⟨t, ht, -, rfl⟩
        exact hC.exists_finpartition_sdiff (hP ht) hsC
      exists P.avoid s |>.bind Q |>.extend hs disjoint_sdiff_left (sdiff_sup_self _ _)
      rw [Finpartition.extend_parts, coe_insert, insert_subset_iff, Finpartition.bind_parts,
        coe_biUnion, iUnion₂_subset_iff, Subtype.forall]
      exact ⟨hsC, fun t ht _ => hQ t ht⟩
  mpr := by
    intro ⟨P, hP⟩
    rw [← P.sup_parts, sup_id_set_eq_sUnion]
    exact supClosed_supClosure.sSup_mem
      (Finset.finite_toSet _)
      (subset_supClosure hC.empty_mem)
      (hP.trans subset_supClosure)

theorem sdiff_mem_supClosure (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    s \ t ∈ supClosure C :=
  hC.mem_supClosure_iff.mpr <| hC.exists_finpartition_sdiff hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem_supClosure := sdiff_mem_supClosure

theorem isSetRing_supClosure (hC : IsSetSemiring C) : IsSetRing (supClosure C) where
  empty_mem := subset_supClosure hC.empty_mem
  union_mem _ _ h₁ h₂ := supClosed_supClosure h₁ h₂
  sdiff_mem := by
    rintro s _ hs ⟨T, hT, hTC, rfl⟩
    rw [sup'_eq_sup]
    clear hT
    induction T using Finset.induction generalizing s with
    | empty => simpa
    | insert t T _ ih =>
      simp_rw [sup_insert, id, sup_eq_union, ← sdiff_sdiff]
      rw [coe_insert, insert_subset_iff] at hTC
      obtain ⟨htC, hTC⟩ := hTC
      refine ih ?_ hTC
      obtain ⟨S, hS, hSC, rfl⟩ := hs
      rw [sup'_eq_sup, ← Finset.sup_sdiff_right]
      refine supClosed_supClosure.finsetSup_mem hS fun s hs => ?_
      exact hC.sdiff_mem_supClosure (hSC hs) htC

section disjointOfDiff

/-- In a semi-ring of sets `C`, for all sets `s, t ∈ C`, `s \ t` is equal to a disjoint union of
finitely many sets in `C`. The finite set of sets in the union is not unique, but this definition
gives an arbitrary `Finset (Set α)` that satisfies the equality.

We remove the empty set to ensure that `t ∉ hC.disjointOfDiff hs ht` even if `t = ∅`. -/
noncomputable def disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    Finset (Set α) :=
  (hC.exists_finpartition_sdiff hs ht).choose.parts

lemma empty_notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ∅ ∉ hC.disjointOfDiff hs ht :=
  Finpartition.bot_notMem _

lemma subset_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ↑(hC.disjointOfDiff hs ht) ⊆ C :=
  (hC.exists_finpartition_sdiff hs ht).choose_spec

lemma pairwiseDisjoint_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    PairwiseDisjoint (hC.disjointOfDiff hs ht : Set (Set α)) id :=
  Finpartition.supIndep _ |>.pairwiseDisjoint

lemma sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ⋃₀ hC.disjointOfDiff hs ht = s \ t :=
  (sup_id_eq_sSup _).symm.trans (Finpartition.sup_parts _)

lemma notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    t ∉ hC.disjointOfDiff hs ht := by
  intro hs_mem
  cases disjoint_sdiff_self_right.eq_bot_of_le (Finpartition.le _ hs_mem)
  exact hC.empty_notMem_disjointOfDiff hs ht hs_mem

lemma sUnion_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C)
    (ht : t ∈ C) (hst : t ⊆ s) :
    ⋃₀ insert t (hC.disjointOfDiff hs ht) = s := by
  conv_rhs => rw [← union_sdiff_cancel hst, ← hC.sUnion_disjointOfDiff hs ht]
  simp only [sUnion_insert]

lemma disjoint_sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    Disjoint t (⋃₀ hC.disjointOfDiff hs ht) := by
  rw [hC.sUnion_disjointOfDiff]
  exact disjoint_sdiff_right

lemma pairwiseDisjoint_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C)
    (ht : t ∈ C) :
    PairwiseDisjoint (insert t (hC.disjointOfDiff hs ht) : Set (Set α)) id := by
  have h := hC.pairwiseDisjoint_disjointOfDiff hs ht
  refine PairwiseDisjoint.insert_of_notMem h (hC.notMem_disjointOfDiff hs ht) fun u hu ↦ ?_
  simp_rw [id]
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_disjointOfDiff hs ht)
  exact subset_sUnion_of_mem hu

end disjointOfDiff

section disjointOfDiffUnion

variable {I : Finset (Set α)}

private theorem exists_finpartition_sdiff_sUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∃ P : Finpartition (s \ ⋃₀ I), ↑P.parts ⊆ C := by
  rw [← hC.mem_supClosure_iff, ← sSup_eq_sUnion, ← sup_id_eq_sSup]
  have hC' := hC.isSetRing_supClosure
  exact hC'.sdiff_mem (subset_supClosure hs) <| hC'.finsetSup_mem <| hI.trans subset_supClosure

/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`,
`disjointOfDiffUnion` is a finite set of sets in `C` such that
`s \ ⋃₀ I = ⋃₀ (hC.disjointOfDiffUnion hs I hI)`.
`disjointOfDiff` is a special case of `disjointOfDiffUnion` where `I` is a
singleton. -/
noncomputable def disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    Finset (Set α) :=
  (hC.exists_finpartition_sdiff_sUnion hs hI).choose.parts

lemma empty_notMem_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) :
    ∅ ∉ hC.disjointOfDiffUnion hs hI :=
  Finpartition.bot_notMem _

lemma disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ↑(hC.disjointOfDiffUnion hs hI) ⊆ C :=
  (hC.exists_finpartition_sdiff_sUnion hs hI).choose_spec

lemma pairwiseDisjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : PairwiseDisjoint (hC.disjointOfDiffUnion hs hI : Set (Set α)) id :=
  (Finpartition.supIndep _).pairwiseDisjoint

lemma sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion hs hI :=
  (Finpartition.sup_parts _).symm.trans (sup_id_eq_sSup _)

@[deprecated (since := "2026-06-03")]
alias diff_sUnion_eq_sUnion_disjointOfDiffUnion := sdiff_sUnion_eq_sUnion_disjointOfDiffUnion

/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`, there is a
finite set of sets in `C` whose union is `s \ ⋃₀ I`.
See `IsSetSemiring.disjointOfDiffUnion` for a definition that gives such a set. -/
lemma exists_disjoint_finset_sdiff_eq (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∃ J : Finset (Set α), ↑J ⊆ C ∧ PairwiseDisjoint (J : Set (Set α)) id ∧
      s \ ⋃₀ I = ⋃₀ J :=
  ⟨hC.disjointOfDiffUnion hs hI,
   hC.disjointOfDiffUnion_subset hs hI,
   hC.pairwiseDisjoint_disjointOfDiffUnion hs hI,
   hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI⟩

@[deprecated (since := "2026-06-03")]
alias exists_disjoint_finset_diff_eq := exists_disjoint_finset_sdiff_eq

lemma sUnion_disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : ⋃₀ (hC.disjointOfDiffUnion hs hI : Set (Set α)) ⊆ s := by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]
  exact sdiff_subset

lemma subset_of_diffUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C)
    (t : Set α) (ht : t ∈ (hC.disjointOfDiffUnion hs hI : Set (Set α))) :
    t ⊆ s \ ⋃₀ I := by
  revert t ht
  rw [← sUnion_subset_iff, hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

lemma subset_of_mem_disjointOfDiffUnion (hC : IsSetSemiring C) {I : Finset (Set α)}
    (hs : s ∈ C) (hI : ↑I ⊆ C) (t : Set α)
    (ht : t ∈ (hC.disjointOfDiffUnion hs hI : Set (Set α))) :
    t ⊆ s := by
  apply le_trans <| hC.subset_of_diffUnion_disjointOfDiffUnion hs hI t ht
  exact sdiff_le (a := s) (b := ⋃₀ I)

lemma disjoint_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) :
    Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.disjointOfDiffUnion hs hI) := by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]; exact Set.disjoint_sdiff_right

lemma disjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    Disjoint I (hC.disjointOfDiffUnion hs hI) := by
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨u, huI, hu_disjointOfDiffUnion⟩ := h
  have h_disj : u ≤ ⊥ :=
    hC.disjoint_sUnion_disjointOfDiffUnion hs hI (subset_sUnion_of_mem huI)
    (subset_sUnion_of_mem hu_disjointOfDiffUnion)
  simp only [Set.bot_eq_empty, subset_empty_iff] at h_disj
  refine hC.empty_notMem_disjointOfDiffUnion hs hI ?_
  rwa [h_disj] at hu_disjointOfDiffUnion

lemma pairwiseDisjoint_union_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    PairwiseDisjoint (I ∪ hC.disjointOfDiffUnion hs hI : Set (Set α)) id := by
  rw [pairwiseDisjoint_union]
  refine ⟨h_dis, hC.pairwiseDisjoint_disjointOfDiffUnion hs hI, fun u hu v hv _ ↦ ?_⟩
  simp_rw [id]
  exact disjoint_of_subset (subset_sUnion_of_mem hu) (subset_sUnion_of_mem hv)
    (hC.disjoint_sUnion_disjointOfDiffUnion hs hI)

lemma sUnion_union_sUnion_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C)
    (hs : s ∈ C) (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s) :
    ⋃₀ I ∪ ⋃₀ hC.disjointOfDiffUnion hs hI = s := by
  conv_rhs => rw [← union_sdiff_cancel (Set.sUnion_subset hI_ss : ⋃₀ ↑I ⊆ s),
    hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

lemma sUnion_union_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s) :
    ⋃₀ ↑(I ∪ hC.disjointOfDiffUnion hs hI) = s := by
  conv_rhs => rw [← sUnion_union_sUnion_disjointOfDiffUnion_of_subset hC hs hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

end disjointOfDiffUnion

section disjointOfUnion


variable {j : Set α} {J : Finset (Set α)}

open MeasureTheory Order

private theorem exists_partition_disjointed (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (j : J) :
    ∃ P : Finpartition (disjointed (fun i ↦ (J.equivFin.symm i : Set α)) (J.equivFin j)),
      ↑P.parts ⊆ C :=
  hC.mem_supClosure_iff.mp <|
    hC.isSetRing_supClosure.disjointed_mem (fun _ ↦ subset_supClosure (hJ (Subtype.coe_prop _))) _

/-- For some `hJ : J ⊆ C` and `j : Set α`, where `hC : IsSetSemiring C`, this is
a `Finset (Set α)` such that `K j := hC.disjointOfUnion hJ` are disjoint
and `⋃₀ K j ⊆ j`, for `j ∈ J`.
Using these we write `⋃₀ J` as a disjoint union `⋃₀ J = ⋃₀ ⋃ x ∈ J, (K x)`.
See `MeasureTheory.IsSetSemiring.disjointOfUnion_props`. -/
noncomputable def disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (j : Set α) :
    Finset (Set α) :=
  if hj : j ∈ J then (hC.exists_partition_disjointed hJ ⟨j, hj⟩).choose.parts else ∅

private theorem disjointOfUnion_coe (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (j : J) :
    hC.disjointOfUnion hJ j = (hC.exists_partition_disjointed hJ j).choose.parts := by
  rw [disjointOfUnion, dif_pos j.2]

lemma pairwiseDisjoint_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint J (hC.disjointOfUnion hJ) := by
  refine Pairwise.set_of_subtype _ _ fun j k hjk ↦ ?_
  simp_rw [Function.onFun, hC.disjointOfUnion_coe hJ, Finset.disjoint_iff_ne]
  exact fun s hs t ht ↦ Disjoint.ne (Finpartition.ne_bot _ hs) <|
    .mono (Finpartition.le _ hs) (Finpartition.le _ ht) <|
    disjoint_disjointed _ <| J.equivFin.injective.ne hjk

lemma disjointOfUnion_subset (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    (disjointOfUnion hC hJ j : Set (Set α)) ⊆ C := by
  lift j to J using hj
  rw [hC.disjointOfUnion_coe hJ]
  exact (hC.exists_partition_disjointed hJ j).choose_spec

lemma pairwiseDisjoint_disjointOfUnion_of_mem (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    PairwiseDisjoint (hC.disjointOfUnion hJ j : Set (Set α)) id := by
  lift j to J using hj
  rw [disjointOfUnion_coe, ← supIndep_iff_pairwiseDisjoint]
  exact Finpartition.supIndep _

lemma pairwiseDisjoint_biUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint (⋃ x ∈ J, (hC.disjointOfUnion hJ x : Set (Set α))) id := by
  simp_rw [← SetLike.mem_coe]
  refine Set.PairwiseDisjoint.biUnion
    (Pairwise.set_of_subtype _ _ ?_)
    (fun _ ↦ hC.pairwiseDisjoint_disjointOfUnion_of_mem hJ)
  simp_rw [Function.onFun, disjointOfUnion_coe, SetLike.mem_coe, ← Finset.sup_eq_iSup,
    Finpartition.sup_parts]
  exact (disjoint_disjointed _).comp_of_injective J.equivFin.injective

lemma disjointOfUnion_subset_of_mem (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ⋃₀ hC.disjointOfUnion hJ j ⊆ j := by
  lift j to J using hj
  grw [disjointOfUnion_coe, ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts,
    disjointed_subset, Equiv.symm_apply_apply]

lemma subset_of_mem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) {x : Set α}
    (hx : x ∈ (hC.disjointOfUnion hJ) j) : x ⊆ j :=
  sUnion_subset_iff.mp (hC.disjointOfUnion_subset_of_mem hJ hj) x hx

lemma empty_notMem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ∅ ∉ hC.disjointOfUnion hJ j := by
  lift j to J using hj
  rw [disjointOfUnion_coe]
  exact Finpartition.bot_notMem _

lemma sUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ⋃₀ ⋃ x ∈ J, (hC.disjointOfUnion hJ x : Set (Set α)) = ⋃₀ J := by
  simp_rw [sUnion_iUnion, ← iSup_eq_iUnion, iSup_subtype', disjointOfUnion_coe,
    ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts, J.equivFin.surjective.iSup_comp,
    iSup_disjointed, J.equivFin.symm.surjective.iSup_comp, iSup_subtype, Finset.sup_eq_iSup, id]

theorem disjointOfUnion_props (hC : IsSetSemiring C) (h1 : ↑J ⊆ C) :
    ∃ K : Set α → Finset (Set α),
      PairwiseDisjoint J K
      ∧ (∀ i ∈ J, ↑(K i) ⊆ C)
      ∧ PairwiseDisjoint (⋃ x ∈ J, (K x : Set (Set α))) id
      ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j)
      ∧ (∀ j ∈ J, ∅ ∉ K j)
      ∧ ⋃₀ J = ⋃₀ (⋃ x ∈ J, (K x : Set (Set α))) :=
  ⟨hC.disjointOfUnion h1,
   hC.pairwiseDisjoint_disjointOfUnion h1,
   fun _ ↦ hC.disjointOfUnion_subset h1,
   hC.pairwiseDisjoint_biUnion_disjointOfUnion h1,
   fun _ ↦ hC.disjointOfUnion_subset_of_mem h1,
   fun _ ↦ hC.empty_notMem_disjointOfUnion h1,
   (hC.sUnion_disjointOfUnion h1).symm⟩

end disjointOfUnion

private lemma _root_.Set.Ioc_mem_setOf_Ioc_le [LinearOrder α] (u v : α) :
    Set.Ioc u v ∈ {s : Set α | ∃ u v, u ≤ v ∧ s = Set.Ioc u v} :=
  ⟨u, max u v, by grind, by grind⟩

/-- The set of open-closed intervals is a semi-ring of sets. -/
protected lemma Ioc [LinearOrder α] [Nonempty α] :
    IsSetSemiring {s : Set α | ∃ u v, u ≤ v ∧ s = Set.Ioc u v} where
  empty_mem := by
    inhabit α
    exact ⟨default, default, le_rfl, by simp⟩
  inter_mem := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rw [Set.Ioc_inter_Ioc]
    apply Ioc_mem_setOf_Ioc_le
  sdiff_eq_sUnion' := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rcases le_or_gt u' u with hu | hu
    · rcases Ioc_mem_setOf_Ioc_le (max u v') v with ⟨u'', v'', h'', heq⟩
      exists {Set.Ioc u'' v''}
      grind [coe_singleton, pairwiseDisjoint_singleton]
    rcases le_or_gt v v' with hv | hv
    · rcases Ioc_mem_setOf_Ioc_le u (min u' v) with ⟨u'', v'', h'', heq⟩
      exists {Set.Ioc u'' v''}
      grind [coe_singleton, pairwiseDisjoint_singleton]
    rw [show Set.Ioc u v \ Set.Ioc u' v' = Set.Ioc u u' ∪ Set.Ioc v' v by grind]
    refine ⟨{Set.Ioc u u', Set.Ioc v' v}, by grind, ?_, by simp⟩
    intro a ha b hb hab
    simp [Function.onFun]
    grind

end IsSetSemiring

end MeasureTheory
