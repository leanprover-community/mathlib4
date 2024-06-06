/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.MeasureTheory.PiSystem

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
* `MeasureTheory.IsSetSemiring.diffFinset hs ht`: for `s, t` in a semi-ring `C`
  (with `hC : IsSetSemiring C`) with `hs : s ∈ C`, `ht : t ∈ C`, this is a `Finset` of
  pairwise disjoint sets such that `s \ t = ⋃₀ hC.diffFinset hs ht`.
* `MeasureTheory.IsSetSemiring.diffFinset₀ hs hI`: for `hs : s ∈ C` and a finset `I` of sets in `C`
  (with `hI : ↑I ⊆ C`), this is a `Finset` of pairwise disjoint sets such that
  `s \ ⋃₀ I = ⋃₀ hC.diffFinset₀ hs hI`.

* `MeasureTheory.IsSetRing`: property of being a ring of sets.

## Main statements

* `MeasureTheory.IsSetSemiring.exists_disjoint_finset_diff_eq`: the existence of the `Finset` given
  by the definition `IsSetSemiring.diffFinset₀` (see above).

-/

open Finset Set

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

/-- A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `s \ t` is equal to a disjoint union of finitely many sets in `C`. -/
structure IsSetSemiring (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  inter_mem : ∀ s ∈ C, ∀ t ∈ C, s ∩ t ∈ C
  diff_eq_sUnion' : ∀ s ∈ C, ∀ t ∈ C,
    ∃ I : Finset (Set α), ↑I ⊆ C ∧ PairwiseDisjoint (I : Set (Set α)) id ∧ s \ t = ⋃₀ I

namespace IsSetSemiring

lemma isPiSystem (hC : IsSetSemiring C) : IsPiSystem C := fun s hs t ht _ ↦ hC.inter_mem s hs t ht

section diffFinset

open scoped Classical in
/-- In a semi-ring of sets `C`, for all sets `s, t ∈ C`, `s \ t` is equal to a disjoint union of
finitely many sets in `C`. The finite set of sets in the union is not unique, but this definition
gives an arbitrary `Finset (Set α)` that satisfies the equality.

We remove the empty set to ensure that `t ∉ hC.diffFinset hs ht` even if `t = ∅`. -/
noncomputable def diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    Finset (Set α) :=
  (hC.diff_eq_sUnion' s hs t ht).choose \ {∅}

lemma empty_not_mem_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ∅ ∉ hC.diffFinset hs ht := by
  classical
  simp only [diffFinset, mem_sdiff, Finset.mem_singleton, eq_self_iff_true, not_true,
    and_false_iff, not_false_iff]

lemma diffFinset_subset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ↑(hC.diffFinset hs ht) ⊆ C := by
  classical
  simp only [diffFinset, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  exact (hC.diff_eq_sUnion' s hs t ht).choose_spec.1.trans (Set.subset_insert _ _)

lemma pairwiseDisjoint_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    PairwiseDisjoint (hC.diffFinset hs ht : Set (Set α)) id := by
  classical
  simp only [diffFinset, coe_sdiff, coe_singleton]
  exact Set.PairwiseDisjoint.subset (hC.diff_eq_sUnion' s hs t ht).choose_spec.2.1
      diff_subset

lemma sUnion_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ⋃₀ hC.diffFinset hs ht = s \ t := by
  classical
  rw [(hC.diff_eq_sUnion' s hs t ht).choose_spec.2.2]
  simp only [diffFinset, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  rw [sUnion_diff_singleton_empty]

lemma not_mem_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    t ∉ hC.diffFinset hs ht := by
  intro hs_mem
  suffices t ⊆ s \ t by
    have h := @disjoint_sdiff_self_right _ t s _
    specialize h le_rfl this
    simp only [Set.bot_eq_empty, Set.le_eq_subset, subset_empty_iff] at h
    refine hC.empty_not_mem_diffFinset hs ht ?_
    rwa [← h]
  rw [← hC.sUnion_diffFinset hs ht]
  exact subset_sUnion_of_mem hs_mem

lemma sUnion_insert_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) (hst : t ⊆ s) :
    ⋃₀ insert t (hC.diffFinset hs ht) = s := by
  conv_rhs => rw [← union_diff_cancel hst, ← hC.sUnion_diffFinset hs ht]
  simp only [mem_coe, sUnion_insert]

lemma disjoint_sUnion_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    Disjoint t (⋃₀ hC.diffFinset hs ht) := by
  rw [hC.sUnion_diffFinset]
  exact disjoint_sdiff_right

lemma pairwiseDisjoint_insert_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    PairwiseDisjoint (insert t (hC.diffFinset hs ht) : Set (Set α)) id := by
  have h := hC.pairwiseDisjoint_diffFinset hs ht
  refine PairwiseDisjoint.insert_of_not_mem h (hC.not_mem_diffFinset hs ht) fun u hu ↦ ?_
  simp_rw [id]
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_diffFinset hs ht)
  simp only [Set.le_eq_subset]
  exact subset_sUnion_of_mem hu

end diffFinset

section diffFinset₀

variable {I : Finset (Set α)}

/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`, there is a
finite set of sets in `C` whose union is `s \ ⋃₀ I`.
See `IsSetSemiring.diffFinset₀` for a definition that gives such a set. -/
lemma exists_disjoint_finset_diff_eq (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∃ J : Finset (Set α), ↑J ⊆ C ∧ PairwiseDisjoint (J : Set (Set α)) id ∧
      s \ ⋃₀ I = ⋃₀ J := by
  classical
  induction I using Finset.induction with
  | empty =>
    simp only [coe_empty, sUnion_empty, diff_empty, exists_prop]
    refine ⟨{s}, singleton_subset_set_iff.mpr hs, ?_⟩
    simp only [coe_singleton, pairwiseDisjoint_singleton, sUnion_singleton, eq_self_iff_true,
      and_self_iff]
  | @insert t I' _ h => ?_

  rw [coe_insert] at hI
  have ht : t ∈ C := hI (Set.mem_insert _ _)
  obtain ⟨J, h_ss, h_dis, h_eq⟩ := h ((Set.subset_insert _ _).trans hI)
  let Ju : ∀ u ∈ C, Finset (Set α) := fun u hu ↦ hC.diffFinset hu ht
  have hJu_subset : ∀ (u) (hu : u ∈ C), ↑(Ju u hu) ⊆ C := by
    intro u hu x hx
    exact hC.diffFinset_subset hu ht hx
  have hJu_disj : ∀ (u) (hu : u ∈ C), (Ju u hu : Set (Set α)).PairwiseDisjoint id := fun u hu ↦
    hC.pairwiseDisjoint_diffFinset hu ht
  have hJu_sUnion : ∀ (u) (hu : u ∈ C), ⋃₀ (Ju u hu : Set (Set α)) = u \ t :=
    fun u hu ↦ hC.sUnion_diffFinset hu ht
  have hJu_disj' : ∀ (u) (hu : u ∈ C) (v) (hv : v ∈ C) (_h_dis : Disjoint u v),
      Disjoint (⋃₀ (Ju u hu : Set (Set α))) (⋃₀ ↑(Ju v hv)) :=by
    intro u hu v hv huv_disj
    rw [hJu_sUnion, hJu_sUnion]
    exact disjoint_of_subset Set.diff_subset Set.diff_subset huv_disj
  let J' : Finset (Set α) := Finset.biUnion (Finset.univ : Finset J) fun u ↦ Ju u (h_ss u.prop)
  have hJ'_subset : ↑J' ⊆ C := by
    intro u
    simp only [J' ,Subtype.coe_mk, univ_eq_attach, coe_biUnion, mem_coe, mem_attach, iUnion_true,
      mem_iUnion, Finset.exists_coe, exists₂_imp]
    intro v hv huvt
    exact hJu_subset v (h_ss hv) huvt
  refine ⟨J', hJ'_subset, ?_, ?_⟩
  · rw [Finset.coe_biUnion]
    refine PairwiseDisjoint.biUnion ?_ ?_
    · simp only [univ_eq_attach, mem_coe, id, iSup_eq_iUnion]
      simp_rw [PairwiseDisjoint, Set.Pairwise]
      intro x _ y _ hxy
      have hxy_disj : Disjoint (x : Set α) y := by
        by_contra h_contra
        refine hxy ?_
        refine Subtype.ext ?_
        exact h_dis.elim x.prop y.prop h_contra
      convert hJu_disj' (x : Set α) (h_ss x.prop) y (h_ss y.prop) hxy_disj
      · rw [sUnion_eq_biUnion]
        congr
      · rw [sUnion_eq_biUnion]
        congr
    · exact fun u _ ↦ hJu_disj _ _
  · rw [coe_insert, sUnion_insert, Set.union_comm, ← Set.diff_diff, h_eq]
    simp_rw [J', sUnion_eq_biUnion, Set.iUnion_diff]
    simp only [Subtype.coe_mk, mem_coe, Finset.mem_biUnion, Finset.mem_univ, exists_true_left,
      Finset.exists_coe, iUnion_exists, true_and]
    rw [iUnion_comm]
    refine iUnion_congr fun i ↦ ?_
    by_cases hi : i ∈ J
    · simp only [hi, iUnion_true, exists_prop]
      rw [← hJu_sUnion i (h_ss hi), sUnion_eq_biUnion]
      simp only [mem_coe]
    · simp only [hi, iUnion_of_empty, iUnion_empty]

open scoped Classical in
/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`,
`diffFinset₀` is a finite set of sets in `C` such that `s \ ⋃₀ I = ⋃₀ (hC.diffFinset₀ hs I hI)`.
`diffFinset` is a special case of `diffFinset₀` where `I` is a singleton. -/
noncomputable def diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) : Finset (Set α) :=
  (hC.exists_disjoint_finset_diff_eq hs hI).choose \ {∅}

lemma empty_not_mem_diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∅ ∉ hC.diffFinset₀ hs hI := by
  classical
  simp only [diffFinset₀, mem_sdiff, Finset.mem_singleton, eq_self_iff_true, not_true,
    and_false_iff, not_false_iff]

lemma diffFinset₀_subset (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ↑(hC.diffFinset₀ hs hI) ⊆ C := by
  classical
  simp only [diffFinset₀, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  exact (hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.1.trans (Set.subset_insert _ _)

lemma pairwiseDisjoint_diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    PairwiseDisjoint (hC.diffFinset₀ hs hI : Set (Set α)) id := by
  classical
  simp only [diffFinset₀, coe_sdiff, coe_singleton]
  exact Set.PairwiseDisjoint.subset
    (hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.2.1 diff_subset

lemma diff_sUnion_eq_sUnion_diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    s \ ⋃₀ I = ⋃₀ hC.diffFinset₀ hs hI := by
  classical
  rw [(hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.2.2]
  simp only [diffFinset₀, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  rw [sUnion_diff_singleton_empty]

lemma sUnion_diffFinset₀_subset (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ⋃₀ (hC.diffFinset₀ hs hI : Set (Set α)) ⊆ s := by
  rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀]
  exact diff_subset

lemma disjoint_sUnion_diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.diffFinset₀ hs hI) := by
  rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀]; exact Set.disjoint_sdiff_right

lemma disjoint_diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    Disjoint I (hC.diffFinset₀ hs hI) := by
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨u, huI, hu_diffFinset₀⟩ := h
  have h_disj : u ≤ ⊥ := hC.disjoint_sUnion_diffFinset₀ hs hI (subset_sUnion_of_mem huI)
    (subset_sUnion_of_mem hu_diffFinset₀)
  simp only [Set.bot_eq_empty, Set.le_eq_subset, subset_empty_iff] at h_disj
  refine hC.empty_not_mem_diffFinset₀ hs hI ?_
  rwa [h_disj] at hu_diffFinset₀

lemma pairwiseDisjoint_union_diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    PairwiseDisjoint (I ∪ hC.diffFinset₀ hs hI : Set (Set α)) id := by
  rw [pairwiseDisjoint_union]
  refine ⟨h_dis, hC.pairwiseDisjoint_diffFinset₀ hs hI, fun u hu v hv _ ↦ ?_⟩
  simp_rw [id]
  exact disjoint_of_subset (subset_sUnion_of_mem hu) (subset_sUnion_of_mem hv)
    (hC.disjoint_sUnion_diffFinset₀ hs hI)

lemma sUnion_union_sUnion_diffFinset₀_of_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s) :
    ⋃₀ I ∪ ⋃₀ hC.diffFinset₀ hs hI = s := by
  conv_rhs => rw [← union_diff_cancel (Set.sUnion_subset hI_ss : ⋃₀ ↑I ⊆ s),
    hC.diff_sUnion_eq_sUnion_diffFinset₀ hs hI]

lemma sUnion_union_diffFinset₀_of_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s) [DecidableEq (Set α)] :
    ⋃₀ ↑(I ∪ hC.diffFinset₀ hs hI) = s := by
  conv_rhs => rw [← sUnion_union_sUnion_diffFinset₀_of_subset hC hs hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

end diffFinset₀

end IsSetSemiring

/-- A ring of sets `C` is a family of sets containing `∅`, stable by union and set difference.
It is then also stable by intersection (see `IsSetRing.inter_mem`). -/
structure IsSetRing (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  union_mem ⦃s t⦄ : s ∈ C → t ∈ C → s ∪ t ∈ C
  diff_mem ⦃s t⦄ : s ∈ C → t ∈ C → s \ t ∈ C

namespace IsSetRing

lemma inter_mem (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C := by
  rw [← diff_diff_right_self]; exact hC.diff_mem hs (hC.diff_mem hs ht)

lemma isSetSemiring (hC : IsSetRing C) : IsSetSemiring C where
  empty_mem := hC.empty_mem
  inter_mem := fun s hs t ht => hC.inter_mem hs ht
  diff_eq_sUnion' := by
    refine fun s hs t ht => ⟨{s \ t}, ?_, ?_, ?_⟩
    · simp only [coe_singleton, Set.singleton_subset_iff]
      exact hC.diff_mem hs ht
    · simp only [coe_singleton, pairwiseDisjoint_singleton]
    · simp only [coe_singleton, sUnion_singleton]

lemma biUnion_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hs : ∀ n ∈ S, s n ∈ C) :
    ⋃ i ∈ S, s i ∈ C := by
  classical
  induction' S using Finset.induction with i S _ h hs
  · simp [hC.empty_mem]
  · simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS ↦ hs n (mem_insert_of_mem hnS))

lemma biInter_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hS : S.Nonempty) (hs : ∀ n ∈ S, s n ∈ C) :
    ⋂ i ∈ S, s i ∈ C := by
  classical
  induction' hS using Finset.Nonempty.cons_induction with _ i S hiS _ h hs
  · simpa using hs
  · simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?_
    exact h (fun n hnS ↦ hs.2 n hnS)

end IsSetRing

end MeasureTheory
