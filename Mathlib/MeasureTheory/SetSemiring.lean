/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-! # Semirings of sets

A semi-ring of sets `C` (in the sense of measure theory) is a family of sets containing `∅`,
stable by intersection and such that for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of
finitely many sets in `C`. Note that a semi-ring of sets may not contain unions.

An important example of a semi-ring of sets is intervals in `ℝ`. The intersection of two intervals
is an interval (possibly empty). The union of two intervals may not be an interval.
The set difference of two intervals may not be an interval, but it will be a disjoint union of
two intervals.

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

## Main statements

* `MeasureTheory.IsSetSemiring.exists_disjoint_finset_diff_eq`: the existence of the `Finset` given
  by the definition `IsSetSemiring.disjointOfDiffUnion` (see above).
* `MeasureTheory.IsSetSemiring.disjointOfUnion_props`: In a `hC : IsSetSemiring C`,
  for a `J : Finset (Set α)` with `J ⊆ C`, there is
  for every `x in J` some `K x ⊆ C` finite, such that
  * `⋃ x ∈ J, K x` are pairwise disjoint and do not contain ∅,
  * `⋃ s ∈ K x, s ⊆ x`,
  * `⋃ x ∈ J, x = ⋃ x ∈ J, ⋃ s ∈ K x, s`.
* `MeasureTheory.IsSetSemiring.pi`: For a `Finset s` and family of semirings,
`∀ i ∈ s, IsSetSemiring (C i)`, the cartesian  product `s.pi '' s.pi C` is a semiring.
* `MeasureTheory.IsSetSemiring.pi`: For a `Finset s` and family of semirings,
`∀ i ∈ s, IsSetSemiring (C i)`, the cartesian  product `s.pi '' s.pi C` is a semiring.
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

lemma iff (C : Set (Set α)) : IsSetSemiring C ↔
    (∅ ∈ C ∧ IsPiSystem C ∧ ∀ s ∈ C, ∀ t ∈ C,
    ∃ I : Finset (Set α), ↑I ⊆ C ∧ PairwiseDisjoint (I : Set (Set α)) id ∧ s \ t = ⋃₀ I) :=
  ⟨fun hC ↦ ⟨hC.empty_mem, isPiSystem hC, hC.diff_eq_sUnion'⟩,
    fun ⟨h1, h2, h3⟩ ↦ {
      empty_mem := h1,
      inter_mem := (isPiSystem_iff_of_nmem_empty h1).mpr h2,
      diff_eq_sUnion' := h3} ⟩

lemma iff (C : Set (Set α)) : IsSetSemiring C ↔
    (∅ ∈ C ∧ IsPiSystem C ∧ ∀ s ∈ C, ∀ t ∈ C,
    ∃ I : Finset (Set α), ↑I ⊆ C ∧ PairwiseDisjoint (I : Set (Set α)) id ∧ s \ t = ⋃₀ I) :=
  ⟨fun hC ↦ ⟨hC.empty_mem, isPiSystem hC, hC.diff_eq_sUnion'⟩,
    fun ⟨h1, h2, h3⟩ ↦ {
      empty_mem := h1,
      inter_mem := (isPiSystem_iff_of_nmem_empty h1).mpr h2,
      diff_eq_sUnion' := h3} ⟩

section disjointOfDiff

open scoped Classical in
/-- In a semi-ring of sets `C`, for all sets `s, t ∈ C`, `s \ t` is equal to a disjoint union of
finitely many sets in `C`. The finite set of sets in the union is not unique, but this definition
gives an arbitrary `Finset (Set α)` that satisfies the equality.

We remove the empty set to ensure that `t ∉ hC.disjointOfDiff hs ht` even if `t = ∅`. -/
noncomputable def disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    Finset (Set α) :=
  (hC.diff_eq_sUnion' s hs t ht).choose \ {∅}

lemma empty_notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ∅ ∉ hC.disjointOfDiff hs ht := by
  classical
  simp only [disjointOfDiff, mem_sdiff, Finset.mem_singleton,
    not_true, and_false, not_false_iff]

@[deprecated (since := "2025-05-24")] alias empty_nmem_disjointOfDiff := empty_notMem_disjointOfDiff

lemma subset_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ↑(hC.disjointOfDiff hs ht) ⊆ C := by
  classical
  simp only [disjointOfDiff, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  exact (hC.diff_eq_sUnion' s hs t ht).choose_spec.1.trans (Set.subset_insert _ _)

lemma pairwiseDisjoint_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    PairwiseDisjoint (hC.disjointOfDiff hs ht : Set (Set α)) id := by
  classical
  simp only [disjointOfDiff, coe_sdiff, coe_singleton]
  exact Set.PairwiseDisjoint.subset (hC.diff_eq_sUnion' s hs t ht).choose_spec.2.1
      diff_subset

lemma sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ⋃₀ hC.disjointOfDiff hs ht = s \ t := by
  classical
  rw [(hC.diff_eq_sUnion' s hs t ht).choose_spec.2.2]
  simp only [disjointOfDiff, coe_sdiff, coe_singleton]
  rw [sUnion_diff_singleton_empty]

lemma notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    t ∉ hC.disjointOfDiff hs ht := by
  intro hs_mem
  suffices t ⊆ s \ t by
    have h := @disjoint_sdiff_self_right _ t s _
    specialize h le_rfl this
    simp only [Set.bot_eq_empty, Set.le_eq_subset, subset_empty_iff] at h
    refine hC.empty_notMem_disjointOfDiff hs ht ?_
    rwa [← h]
  rw [← hC.sUnion_disjointOfDiff hs ht]
  exact subset_sUnion_of_mem hs_mem

@[deprecated (since := "2025-05-24")] alias nmem_disjointOfDiff := notMem_disjointOfDiff

lemma sUnion_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s ∈ C)
    (ht : t ∈ C) (hst : t ⊆ s) :
    ⋃₀ insert t (hC.disjointOfDiff hs ht) = s := by
  conv_rhs => rw [← union_diff_cancel hst, ← hC.sUnion_disjointOfDiff hs ht]
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
  simp only [Set.le_eq_subset]
  exact subset_sUnion_of_mem hu

end disjointOfDiff

section disjointOfDiffUnion

variable {I : Finset (Set α)}

/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`, there is a
finite set of sets in `C` whose union is `s \ ⋃₀ I`.
See `IsSetSemiring.disjointOfDiffUnion` for a definition that gives such a set. -/
lemma exists_disjoint_finset_diff_eq (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∃ J : Finset (Set α), ↑J ⊆ C ∧ PairwiseDisjoint (J : Set (Set α)) id ∧
      s \ ⋃₀ I = ⋃₀ J := by
  classical
  induction I using Finset.induction with
  | empty =>
    simp only [coe_empty, sUnion_empty, diff_empty]
    refine ⟨{s}, singleton_subset_set_iff.mpr hs, ?_⟩
    simp only [coe_singleton, pairwiseDisjoint_singleton, sUnion_singleton,
      and_self_iff]
  | insert t I' _ h => ?_
  rw [coe_insert] at hI
  have ht : t ∈ C := hI (Set.mem_insert _ _)
  obtain ⟨J, h_ss, h_dis, h_eq⟩ := h ((Set.subset_insert _ _).trans hI)
  let Ju : ∀ u ∈ C, Finset (Set α) := fun u hu ↦ hC.disjointOfDiff hu ht
  have hJu_subset : ∀ (u) (hu : u ∈ C), ↑(Ju u hu) ⊆ C := by
    intro u hu x hx
    exact hC.subset_disjointOfDiff hu ht hx
  have hJu_disj : ∀ (u) (hu : u ∈ C), (Ju u hu : Set (Set α)).PairwiseDisjoint id := fun u hu ↦
    hC.pairwiseDisjoint_disjointOfDiff hu ht
  have hJu_sUnion : ∀ (u) (hu : u ∈ C), ⋃₀ (Ju u hu : Set (Set α)) = u \ t :=
    fun u hu ↦ hC.sUnion_disjointOfDiff hu ht
  have hJu_disj' : ∀ (u) (hu : u ∈ C) (v) (hv : v ∈ C) (_h_dis : Disjoint u v),
      Disjoint (⋃₀ (Ju u hu : Set (Set α))) (⋃₀ ↑(Ju v hv)) := by
    intro u hu v hv huv_disj
    rw [hJu_sUnion, hJu_sUnion]
    exact disjoint_of_subset Set.diff_subset Set.diff_subset huv_disj
  let J' : Finset (Set α) := Finset.biUnion (Finset.univ : Finset J) fun u ↦ Ju u (h_ss u.prop)
  have hJ'_subset : ↑J' ⊆ C := by
    intro u
    simp only [J', univ_eq_attach, coe_biUnion, mem_coe, mem_attach, iUnion_true,
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
    simp only [mem_coe, Finset.mem_biUnion, Finset.mem_univ,
      Finset.exists_coe, iUnion_exists, true_and]
    rw [iUnion_comm]
    refine iUnion_congr fun i ↦ ?_
    by_cases hi : i ∈ J
    · simp only [hi, iUnion_true]
      rw [← hJu_sUnion i (h_ss hi), sUnion_eq_biUnion]
      simp only [mem_coe]
    · simp only [hi, iUnion_of_empty, iUnion_empty]

open scoped Classical in
/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`,
`disjointOfDiffUnion` is a finite set of sets in `C` such that
`s \ ⋃₀ I = ⋃₀ (hC.disjointOfDiffUnion hs I hI)`.
`disjointOfDiff` is a special case of `disjointOfDiffUnion` where `I` is a
singleton. -/
noncomputable def disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
  (hI : ↑I ⊆ C) : Finset (Set α) :=
  (hC.exists_disjoint_finset_diff_eq hs hI).choose \ {∅}

lemma empty_notMem_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) :
    ∅ ∉ hC.disjointOfDiffUnion hs hI := by
  classical
  simp only [disjointOfDiffUnion, mem_sdiff, Finset.mem_singleton,
    not_true, and_false, not_false_iff]

@[deprecated (since := "2025-05-24")]
alias empty_nmem_disjointOfDiffUnion := empty_notMem_disjointOfDiffUnion

lemma disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ↑(hC.disjointOfDiffUnion hs hI) ⊆ C := by
  classical
  simp only [disjointOfDiffUnion, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  exact (hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.1.trans (Set.subset_insert _ _)

lemma pairwiseDisjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : PairwiseDisjoint (hC.disjointOfDiffUnion hs hI : Set (Set α)) id := by
  classical
  simp only [disjointOfDiffUnion, coe_sdiff, coe_singleton]
  exact Set.PairwiseDisjoint.subset
    (hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.2.1 diff_subset

lemma diff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion hs hI := by
  classical
  rw [(hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.2.2]
  simp only [disjointOfDiffUnion, coe_sdiff, coe_singleton]
  rw [sUnion_diff_singleton_empty]

lemma sUnion_disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) : ⋃₀ (hC.disjointOfDiffUnion hs hI : Set (Set α)) ⊆ s := by
  rw [← hC.diff_sUnion_eq_sUnion_disjointOfDiffUnion]
  exact diff_subset

lemma subset_of_diffUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C)
    (t : Set α) (ht : t ∈ (hC.disjointOfDiffUnion hs hI : Set (Set α))) :
    t ⊆ s \ ⋃₀ I := by
  revert t ht
  rw [← sUnion_subset_iff, hC.diff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

lemma subset_of_mem_disjointOfDiffUnion (hC : IsSetSemiring C) {I : Finset (Set α)}
    (hs : s ∈ C) (hI : ↑I ⊆ C) (t : Set α)
    (ht : t ∈ (hC.disjointOfDiffUnion hs hI : Set (Set α))) :
    t ⊆ s := by
  apply le_trans <| hC.subset_of_diffUnion_disjointOfDiffUnion hs hI t ht
  exact sdiff_le (a := s) (b := ⋃₀ I)

lemma disjoint_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) :
    Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.disjointOfDiffUnion hs hI) := by
  rw [← hC.diff_sUnion_eq_sUnion_disjointOfDiffUnion]; exact Set.disjoint_sdiff_right

lemma disjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    Disjoint I (hC.disjointOfDiffUnion hs hI) := by
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨u, huI, hu_disjointOfDiffUnion⟩ := h
  have h_disj : u ≤ ⊥ :=
    hC.disjoint_sUnion_disjointOfDiffUnion hs hI (subset_sUnion_of_mem huI)
    (subset_sUnion_of_mem hu_disjointOfDiffUnion)
  simp only [Set.bot_eq_empty, Set.le_eq_subset, subset_empty_iff] at h_disj
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
  conv_rhs => rw [← union_diff_cancel (Set.sUnion_subset hI_ss : ⋃₀ ↑I ⊆ s),
    hC.diff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

lemma sUnion_union_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s) [DecidableEq (Set α)] :
    ⋃₀ ↑(I ∪ hC.disjointOfDiffUnion hs hI) = s := by
  conv_rhs => rw [← sUnion_union_sUnion_disjointOfDiffUnion_of_subset hC hs hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

end disjointOfDiffUnion
section disjointOfUnion

variable {j : Set α} {J : Finset (Set α)}

theorem disjointOfUnion_props (hC : IsSetSemiring C) (h1 : ↑J ⊆ C) :
    ∃ K : Set α → Finset (Set α),
      PairwiseDisjoint J K
      ∧ (∀ i ∈ J, ↑(K i) ⊆ C)
      ∧ PairwiseDisjoint (⋃ x ∈ J, (K x : Set (Set α))) id
      ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j)
      ∧ (∀ j ∈ J, ∅ ∉ K j)
      ∧ ⋃₀ J = ⋃₀ (⋃ x ∈ J, (K x : Set (Set α))) := by
  classical
  induction J using Finset.cons_induction with
  | empty => simp
  | cons s J hJ hind =>
    rw [cons_eq_insert, coe_insert, Set.insert_subset_iff] at h1
    obtain ⟨K, hK0, ⟨hK1, hK2, hK3, hK4, hK5⟩⟩ := hind h1.2
    let K1 : Set α → Finset (Set α) := fun (t : Set α) ↦
      if t = s then (hC.disjointOfDiffUnion h1.1 h1.2) else K t
    have hK1s : K1 s = hC.disjointOfDiffUnion h1.1 h1.2 := by simp [K1]
    have hK1_of_ne t (ht : t ≠ s) : K1 t = K t := by simp [K1, ht]
    use K1
    simp only [cons_eq_insert, mem_coe, Finset.mem_insert, sUnion_subset_iff, forall_eq_or_imp,
      coe_insert, sUnion_insert]
    -- two simplification rules for induction hypothesis
    have ht1' : ∀ x ∈ J, K1 x = K x := fun x hx ↦ hK1_of_ne _ (fun h_eq ↦ hJ (h_eq ▸ hx))
    have ht2 : (⋃ x ∈ J, (K1 x : Set (Set α))) = ⋃ x ∈ J, ((K x : Set (Set α))) := by
      apply iUnion₂_congr
      intros x hx
      exact_mod_cast hK1_of_ne _ (ne_of_mem_of_not_mem hx hJ)
    simp only [hK1s]
    refine ⟨?_, ⟨hC.disjointOfDiffUnion_subset h1.1 h1.2, ?_⟩, ?_,
      ⟨hC.subset_of_mem_disjointOfDiffUnion h1.1 h1.2, ?_⟩, ?_, ?_⟩
    · apply Set.Pairwise.insert
      · intro j hj i hi hij
        rw [Function.onFun, ht1' j hj, ht1' i hi]
        exact hK0 hj hi hij
      · intro i hi _
        have h7 : Disjoint ↑(hC.disjointOfDiffUnion h1.1 h1.2) (K i : Set (Set α)) := by
          refine disjoint_of_sSup_disjoint_of_le_of_le
            (hC.subset_of_diffUnion_disjointOfDiffUnion h1.1 h1.2) ?_
            (@disjoint_sdiff_left _ (⋃₀ J) s) (Or.inl
              (hC.empty_notMem_disjointOfDiffUnion h1.1 h1.2))
          simp only [mem_coe, Set.le_eq_subset]
          apply sUnion_subset_iff.mp
          exact (hK3 i hi).trans (subset_sUnion_of_mem hi)
        have h8 : Function.onFun Disjoint K1 s i := by
          refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
          rw [ht1' i hi, hK1s]
          rw [Set.disjoint_iff_inter_eq_empty] at h7
          exact_mod_cast h7
        exact ⟨h8, Disjoint.symm h8⟩
    · intros i hi
      rw [ht1' i hi]
      exact hK1 i hi
    · simp only [iUnion_iUnion_eq_or_left]
      refine pairwiseDisjoint_union.mpr ⟨?_, ?_, ?_⟩
      · rw [hK1s]
        exact hC.pairwiseDisjoint_disjointOfDiffUnion h1.1 h1.2
      · simpa [ht2]
      · simp only [mem_coe, mem_iUnion, exists_prop, ne_eq, id_eq, forall_exists_index, and_imp]
        intros i hi j x hx h3 h4
        obtain ki : i ⊆ s \ ⋃₀ J := hC.subset_of_diffUnion_disjointOfDiffUnion h1.1 h1.2 _
          (hK1s ▸ hi)
        obtain hx2 : j ⊆ x := subset_trans (subset_sUnion_of_mem (ht1' x hx ▸ h3)) (hK3 x hx)
        obtain kj : j ⊆ ⋃₀ J := hx2.trans <| subset_sUnion_of_mem hx
        exact disjoint_of_subset ki kj disjoint_sdiff_left
    · intros a ha
      simp_rw [hK1_of_ne _ (ne_of_mem_of_not_mem ha hJ)]
      change ∀ t' ∈ (K a : Set (Set α)), t' ⊆ a
      rw [← sUnion_subset_iff]
      exact hK3 a ha
    · refine ⟨hC.empty_notMem_disjointOfDiffUnion h1.1 h1.2, ?_⟩
      intros a ha
      rw [ht1' a ha]
      exact hK4 a ha
    · simp only [iUnion_iUnion_eq_or_left, sUnion_union, ht2, K1]
      simp_rw [apply_ite, hK5,
      ← hC.diff_sUnion_eq_sUnion_disjointOfDiffUnion h1.1 h1.2, hK5]
      simp only [↓reduceIte, diff_union_self]

/-- For some `hJ : J ⊆ C` and `j : Set α`, where `hC : IsSetSemiring C`, this is
a `Finset (Set α)` such that `K j := hC.disjointOfUnion hJ` are disjoint
and `⋃₀ K j ⊆ j`, for `j ∈ J`.
Using these we write `⋃₀ J` as a disjoint union `⋃₀ J = ⋃₀ ⋃ x ∈ J, (K x)`.
See `MeasureTheory.IsSetSemiring.disjointOfUnion_props`. -/
noncomputable def disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (j : Set α) :=
  (hC.disjointOfUnion_props hJ).choose j

lemma pairwiseDisjoint_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint J (hC.disjointOfUnion hJ) :=
  (Exists.choose_spec (hC.disjointOfUnion_props hJ)).1

lemma disjointOfUnion_subset (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    (disjointOfUnion hC hJ j : Set (Set α)) ⊆ C :=
  (Exists.choose_spec (hC.disjointOfUnion_props hJ)).2.1 _ hj

lemma pairwiseDisjoint_biUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint (⋃ x ∈ J, (hC.disjointOfUnion hJ x : Set (Set α))) id :=
  (Exists.choose_spec (hC.disjointOfUnion_props hJ)).2.2.1

lemma pairwiseDisjoint_disjointOfUnion_of_mem (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    PairwiseDisjoint (hC.disjointOfUnion hJ j : Set (Set α)) id := by
  apply PairwiseDisjoint.subset (hC.pairwiseDisjoint_biUnion_disjointOfUnion hJ)
  exact subset_iUnion₂_of_subset j hj fun ⦃a⦄ a ↦ a

lemma disjointOfUnion_subset_of_mem (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ⋃₀ hC.disjointOfUnion hJ j ⊆ j :=
  (Exists.choose_spec (hC.disjointOfUnion_props hJ)).2.2.2.1 j hj

lemma subset_of_mem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) {x : Set α}
    (hx : x ∈ (hC.disjointOfUnion hJ) j) : x ⊆ j :=
  sUnion_subset_iff.mp (hC.disjointOfUnion_subset_of_mem hJ hj) x hx

lemma empty_notMem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ∅ ∉ hC.disjointOfUnion hJ j :=
  (Exists.choose_spec (hC.disjointOfUnion_props hJ)).2.2.2.2.1 j hj

@[deprecated (since := "2025-05-24")]
alias empty_nmem_disjointOfUnion := empty_notMem_disjointOfUnion

lemma sUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ⋃₀ ⋃ x ∈ J, (hC.disjointOfUnion hJ x : Set (Set α)) = ⋃₀ J :=
  (Exists.choose_spec (hC.disjointOfUnion_props hJ)).2.2.2.2.2.symm

end disjointOfUnion

section piSemiring

variable {ι : Type*} {α : ι → Type*} {C : (i : ι) → Set (Set (α i))}

/-- For `K' a : Finset (Set α i))`, define the
`Fintype (({a} : Set ι).pi  '' ({a} : Set ι).pi K')`. -/
noncomputable

def fintype_pi_ofFinset (a : ι) (K' : (i : ι) → (Set (Set (α i)))) (K : Finset (Set (α a)))
  (hK' : K = K' a) : Fintype (({a} : Set ι).pi  '' ({a} : Set ι).pi K') := by
  let E : Set (α a) → Set (((i : ι) → α i)) :=
    fun (k : Set (α a)) ↦ { f : ((i : ι) → α i) | f a ∈ k }
  have h (y : _) (hy : y ∈ (({a} : Set ι).pi  '' ({a} : Set ι).pi K')) : ∃ k ∈ K, E k = y := by
    obtain ⟨x, hx1, hx2⟩ := hy
    simp only [singleton_pi, Set.mem_preimage, Function.eval] at hx1
    rw [← hK'] at hx1
    refine ⟨x a, hx1, hx2.symm ▸ Eq.symm (singleton_pi' a x)⟩
  exact Finite.fintype <| Finite.Set.subset (E '' ↑K) h

lemma pairwiseDisjoint_set_pi {a : ι} {K : (i : ι) → Set (Set (α i))}
    (h : PairwiseDisjoint (K a) id) :
      PairwiseDisjoint (({a} : Set ι).pi  '' ({a} : Set ι).pi K) id := by
  intro m hm n hn hmn
  simp only [Set.mem_image] at hm hn
  obtain ⟨o, ho1, ho2⟩ := hm
  obtain ⟨p, hp1, hp2⟩ := hn
  simp only [singleton_pi] at ho1 hp1
  rw [← ho2, ← hp2] at hmn ⊢
  apply Set.Disjoint.set_pi (mem_singleton_iff.mpr rfl)
  exact h ho1 hp1 <| fun h7 ↦  hmn <| Set.pi_congr rfl <| fun i hi ↦ (mem_singleton_iff.mpr hi) ▸ h7

lemma pi_singleton_diff_eq_sUnion {a : ι} {K' : (i : ι) → Set (Set (α i))}
  {x y : (i : ι) → Set (α i)} (hK : x a \ y a = ⋃₀ K' a) :
      (({a} : Set ι).pi x \ ({a} : Set ι).pi y) =
        ⋃₀ (({a} : Set ι).pi  '' ({a} : Set ι).pi K') := by
  classical
  simp only [sUnion_image]
  ext z
  simp only [singleton_pi, mem_diff, Set.mem_preimage, Function.eval, mem_iUnion, exists_prop]
  refine ⟨fun h ↦ ?_, fun ⟨w, hw⟩ ↦ ?_⟩
  · rw [← mem_diff, hK] at h
    obtain ⟨w, ⟨hw1, hw2⟩⟩ := mem_sUnion.mp h
    use fun i ↦ (if h : a = i then h ▸ w else (univ : Set (α i)))
    simp only [↓reduceDIte]
    exact ⟨hw1, hw2⟩
  · rw [← mem_diff, hK, mem_sUnion]
    use w a

lemma pi_inter_image {s t : Set ι} {x : (i : ι) → Set (α i)} (hst : Disjoint s t)
  (hx : ∀ i ∈ t, x i ∈ C i) {K' : Set (Set ((i : ι) → α i))} (hK'1 : K' ⊆ s.pi '' s.pi C) :
  Set.inter (t.pi x) '' K' ⊆ (s ∪ t).pi '' (s ∪ t).pi C := by
  intro a ha
  obtain ⟨b, ⟨hb1, hb2⟩⟩ := ha
  have hb3 := hK'1 hb1
  obtain ⟨c, ⟨hc1, hc2⟩⟩ := hb3
  simp only [Set.mem_image, Set.mem_pi, Set.mem_union]
  classical
  use fun i ↦ if i ∈ s then c i else x i
  refine ⟨?_, ?_⟩
  · rintro i (hi1 | hi2)
    · simp [hi1]
      simp only [Set.mem_pi] at hc1
      exact hc1 i hi1
    · have h : i ∉ s := by
        exact Disjoint.notMem_of_mem_left (Disjoint.symm hst) hi2
      simp only [h, ↓reduceIte]
      exact hx i hi2
  · rw [← hb2, ← hc2, union_pi_ite_of_disjoint hst, inter_comm]
    rfl

lemma pi_inter_image' {s t : Set ι} {x : (i : ι) → Set (α i)} (hst : Disjoint s t)
(hx : ∀ i ∈ t, x i ∈ C i) {K' : (i : ι) → Set (Set (α i))} (hK'1 : ∀ i ∈ s, K' i ⊆ C i) :
  Set.inter (t.pi x) '' (s.pi  '' s.pi K') ⊆ (s ∪ t).pi '' (s ∪ t).pi C := by
  exact pi_inter_image hst hx <| subset_pi_image_of_subset hK'1

/- For a `Finset s` and family of semirings, `∀ i ∈ s, IsSetSemiring (C i)`, the cartesian
product `s.pi '' s.pi C` is a semiring. -/
theorem pi {s : Set ι} (hs : Finite s)
    (hC : ∀ i ∈ s, IsSetSemiring (C i)) : s.Nonempty →  IsSetSemiring (s.pi '' s.pi C) := by
  classical
  refine Set.Finite.induction_on_subset s hs (fun h ↦ False.elim <| Set.not_nonempty_empty h) ?_
  intro a t ha hts t_fin h_ind b; clear b
  refine (IsSetSemiring.iff _).mpr ⟨?_, ?_, ?_⟩
  · simp only [insert_pi, Set.mem_image, mem_inter_iff, Set.mem_pi]
    use fun _ ↦ ∅
    simp only [Set.preimage_empty, Set.empty_inter, and_true]
    refine ⟨(hC a ha).empty_mem, fun i a ↦ (hC i (hts a)).empty_mem⟩
  · exact IsPiSystem.pi_subset (insert a t)
      (fun i hi ↦ (hC i (Set.insert_subset ha hts hi)).isPiSystem)
  · intro u ⟨x, ⟨hx1, hx2⟩⟩ v ⟨y, ⟨hy1, hy2⟩⟩
    simp_rw [Set.mem_pi, Set.mem_insert_iff, insert_pi, ← singleton_pi] at hx1 hx2 hy1 hy2
    -- Write `u : Set ((i : ι) → α i)` as `x : (i : ι) → Set (α i)` with `u = {a}.pi x ∩ t.pi x`.
    have h1 (u : Set ι) (x : (i : ι) → Set (α i)) (hu : ∀ i ∈ u, x i ∈ C i) :
      u.pi x ∈ u.pi '' u.pi C :=
      Set.mem_image_of_mem u.pi <| Set.mem_pi.mpr fun i hi ↦ hu i hi
    have hx1' := h1 t x (fun i hi ↦ hx1 i (Or.inr hi))
    have hy1' := h1 t y (fun i hi ↦ hy1 i (Or.inr hi))
    clear h1
    -- Express `u \ v` using `x` and `y`.
    have h1 : u \ v = (t.pi x ∩ (({a} : Set ι).pi x \ ({a} : Set ι).pi y)) ∪
    ((t.pi x \ t.pi y) ∩ (({a} : Set ι).pi x ∩ ({a} : Set ι).pi y)):=  by
      rw [← hx2, ← hy2, ← union_pi, ← union_pi]
      apply pi_setdiff_eq_union
    -- Show that the two sets from `h1` are disjoint.
    obtain h2 := disjoint_pi_of_interSetdiff_of_interSetdiffInter ({a} : Set ι) t x y
    -- `K : Set (Set (α a))` is such that `x a \ y a = ⋃₀ K`.
    /- Several sets need to be constructed based on `K`.
        We use that convention that for some set system  `X`
        * `hX1` states that `X` is contained in the corresponding structure using the semiring;
        * `hX2` states that the set mentioned in `hX1` is pairwise disjoint;
        * `hX3` states that the union of sets from `hX1` is the corresponding set difference. -/
    obtain ⟨K, ⟨hK1, hK2, hK3⟩⟩ :=
      (hC a ha).diff_eq_sUnion' (x a) (hx1 a (Or.inl rfl)) (y a) (hy1 a (Or.inl rfl))
    -- `K' : (i : ι) → Set (Set (α i))` satisfies `K' a = K`.
    let K' : (i : ι) → Set (Set (α i)) :=
      fun (i : ι) => dite (i = a) (fun h ↦ h ▸ K.toSet) (fun _ ↦ (default : Set (Set (α i))))
    have hKK' : K = K' a := by simp only [dite_eq_ite, ↓reduceIte, K']
    haveI hE' : Fintype (({a} : Set ι).pi  '' ({a} : Set ι).pi K')
      := fintype_pi_ofFinset a K' K (by simp only [↓reduceDIte, K'])
    -- have hE1 := subset_pi_image_of_subset hK'1; clear hK'1
    have hE3 := pi_singleton_diff_eq_sUnion (hKK'.symm ▸ hK3)
    let F := Set.inter (t.pi x) '' (({a} : Set ι).pi  '' ({a} : Set ι).pi K')
    have hF1 : F ⊆ (insert a t).pi '' (insert a t).pi C :=
      pi_inter_image' (Set.disjoint_singleton_left.mpr t_fin) (fun i hi ↦ hx1 i (Or.inr hi))
        (fun i hi ↦ mem_singleton_iff.mp hi ▸ hKK' ▸ hK1)
    have hF2 : PairwiseDisjoint F id :=
      PairwiseDisjoint.image_of_le (pairwiseDisjoint_set_pi (hKK' ▸ hK2)) <|
      fun a b hb ↦ Set.mem_of_mem_inter_right hb
    have hF3 : ⋃₀ F = (t.pi x) ∩ (({a} : Set ι).pi x \ ({a} : Set ι).pi y) := by
      simp_rw [hE3, sUnion_eq_iUnion, iUnion_coe_set, inter_iUnion₂]
      simp only [singleton_pi, Set.mem_image, Set.mem_preimage, Function.eval,
        iUnion_exists, biUnion_and', iUnion_iUnion_eq_right, F]
      rfl
    by_cases h : t.Nonempty
    rotate_left
    · have h : t = ∅ := Set.not_nonempty_iff_eq_empty.mp h;
      use F.toFinset
      simp only [coe_toFinset]
      refine ⟨hF1, hF2, ?_⟩
      simp only [h, empty_pi, Set.univ_inter, sdiff_self, Set.bot_eq_empty,
        Set.empty_inter, Set.union_empty] at hF3 h1
      exact hF3.symm ▸ h1
    · have h_ind' := h_ind h;
      let G := Set.inter (({a} : Set ι).pi y ∩ ({a} : Set ι).pi x) ''
        (h_ind'.disjointOfDiff hx1' hy1')
      have hG1 : G ⊆ (insert a t).pi '' (insert a t).pi C := by
        simp only [G]
        rw [← singleton_union, Set.union_comm, ← Set.pi_inter_distrib]
        exact pi_inter_image (Set.disjoint_singleton_right.mpr t_fin)
          (fun i hi ↦ hi ▸ (hC a ha).inter_mem (y a)
          (hy1 a (Or.inl rfl)) (x a) (hx1 a (Or.inl rfl)))
            <| IsSetSemiring.subset_disjointOfDiff h_ind' hx1' hy1'
      have hG2 : PairwiseDisjoint G id := PairwiseDisjoint.image_of_le
        (h_ind'.pairwiseDisjoint_disjointOfDiff hx1' hy1') <| fun _ _ hb ↦
          Set.mem_of_mem_inter_right hb
      have hG3 : ⋃₀ G = ((({a} : Set ι).pi x ∩ ({a} : Set ι).pi y)) ∩ (t.pi x \ t.pi y) := by
        rw [← h_ind'.sUnion_disjointOfDiff hx1' hy1']
        nth_rewrite 2 [sUnion_eq_iUnion]
        rw [iUnion_coe_set, inter_iUnion₂, inter_comm]
        simp only [mem_coe, sUnion_image, G]
        rfl
      use F.toFinset ∪ G.toFinset
      simp only [coe_union, coe_toFinset]
      refine ⟨union_subset_iff.mpr ⟨hF1, hG1⟩, ?_, ?_⟩
      · apply (pairwiseDisjoint_union_of_disjoint (fun ⦃a b⦄ a ↦ a) hF2 hG2 )
        rw [hF3, hG3]
        nth_rewrite 2 [inter_comm]
        exact h2
      · rw [sUnion_union, hF3, hG3, h1]
        nth_rewrite 2 [inter_comm]
        rfl

end piSemiring

end IsSetSemiring

section piSemiring

variable {ι : Type*} {α : ι → Type*} {C : (i : ι) → Set (Set (α i))}

/-- For `K' a : Finset (Set α i))`, define the
`Fintype (({a} : Set ι).pi  '' ({a} : Set ι).pi K')`. -/
noncomputable

def fintype_pi_ofFinset (a : ι) (K' : (i : ι) → (Set (Set (α i)))) (K : Finset (Set (α a)))
  (hK' : K = K' a) : Fintype (({a} : Set ι).pi  '' ({a} : Set ι).pi K') := by
  let E : Set (α a) → Set (((i : ι) → α i)) :=
    fun (k : Set (α a)) ↦ { f : ((i : ι) → α i) | f a ∈ k }
  have h (y : _) (hy : y ∈ (({a} : Set ι).pi  '' ({a} : Set ι).pi K')) : ∃ k ∈ K, E k = y := by
    obtain ⟨x, hx1, hx2⟩ := hy
    simp only [singleton_pi, Set.mem_preimage, Function.eval] at hx1
    rw [← hK'] at hx1
    refine ⟨x a, hx1, hx2.symm ▸ Eq.symm (singleton_pi' a x)⟩
  simp only [mem_coe] at h
  exact Finite.fintype <| Finite.Set.subset (E '' ↑K) h

lemma pairwiseDisjoint_set_pi {a : ι} {K : (i : ι) → Set (Set (α i))}
    (h : PairwiseDisjoint (K a) id) :
      PairwiseDisjoint (({a} : Set ι).pi  '' ({a} : Set ι).pi K) id := by
  intro m hm n hn hmn
  simp only [↓reduceDIte, Set.mem_image, Set.mem_preimage,
    mem_coe] at hm hn
  obtain ⟨o, ho1, ho2⟩ := hm
  obtain ⟨p, hp1, hp2⟩ := hn
  simp only [singleton_pi, ↓reduceDIte, Function.eval, mem_coe] at ho1 hp1
  rw [← ho2, ← hp2] at hmn ⊢
  apply Set.Disjoint.set_pi (mem_singleton_iff.mpr rfl)
  exact h ho1 hp1 <| fun h7 ↦  hmn <| Set.pi_congr rfl <| fun i hi ↦ (mem_singleton_iff.mpr hi) ▸ h7

lemma pi_singleton_diff_eq_sUnion {a : ι} {K' : (i : ι) → Set (Set (α i))}
  {x y : (i : ι) → Set (α i)} (hK : x a \ y a = ⋃₀ K' a) :
      (({a} : Set ι).pi x \ ({a} : Set ι).pi y) =
        ⋃₀ (({a} : Set ι).pi  '' ({a} : Set ι).pi K') := by
  classical
  simp only [sUnion_image]
  ext z
  simp only [singleton_pi, mem_diff, Set.mem_preimage, Function.eval, mem_iUnion, exists_prop]
  refine ⟨fun h ↦ ?_, fun ⟨w, hw⟩ ↦ ?_⟩
  · rw [← mem_diff, hK] at h
    obtain ⟨w, ⟨hw1, hw2⟩⟩ := mem_sUnion.mp h
    use fun i ↦ (if h : a = i then h ▸ w else (univ : Set (α i)))
    simp only [↓reduceDIte]
    exact ⟨hw1, hw2⟩
  · rw [← mem_diff, hK, mem_sUnion]
    use w a

lemma pi_inter_image {s t : Set ι} {x : (i : ι) → Set (α i)}  (hst : Disjoint s t)
  (hx : ∀ i ∈ t, x i ∈ C i) {K' : Set (Set ((i : ι) → α i))} (hK'1 : K' ⊆ s.pi '' s.pi C) :
  Set.inter (t.pi x) '' K' ⊆ (s ∪ t).pi '' (s ∪ t).pi C := by
  intro a ha
  obtain ⟨b, ⟨hb1, hb2⟩⟩ := ha
  have hb3 := hK'1 hb1
  obtain ⟨c, ⟨hc1, hc2⟩⟩ := hb3
  simp only [Set.mem_image, Set.mem_pi, Set.mem_union]
  classical
  use fun i ↦ if i ∈ s then c i else x i
  refine ⟨?_, ?_⟩
  · rintro i (hi1 | hi2)
    · simp [hi1]
      simp only [Set.mem_pi] at hc1
      exact hc1 i hi1
    · have h : i ∉ s := by
        exact Disjoint.not_mem_of_mem_left (Disjoint.symm hst) hi2
      simp only [h, ↓reduceIte]
      exact hx i hi2
  · rw [← hb2, ← hc2, union_pi_ite_of_disjoint hst, inter_comm]
    rfl

lemma pi_inter_image' {s t : Set ι} {x : (i : ι) → Set (α i)}  (hst : Disjoint s t)
(hx : ∀ i ∈ t, x i ∈ C i) {K' : (i : ι) → Set (Set (α i))} (hK'1 : ∀ i ∈ s, K' i ⊆ C i) :
  Set.inter (t.pi x) '' (s.pi  '' s.pi K') ⊆ (s ∪ t).pi '' (s ∪ t).pi C := by
  exact pi_inter_image hst hx <| subset_pi_image_of_subset hK'1

/- For a `Finset s` and family of semirings, `∀ i ∈ s, IsSetSemiring (C i)`, the cartesian
product `s.pi '' s.pi C` is a semiring. -/
theorem pi {s : Set ι} (hs : Finite s)
    (hC : ∀ i ∈ s, IsSetSemiring (C i)) : s.Nonempty →  IsSetSemiring (s.pi '' s.pi C) := by
  classical
  refine Set.Finite.induction_on_subset s hs (fun h ↦ False.elim <| Set.not_nonempty_empty h) ?_
  intro a t ha hts t_fin h_ind b; clear b
  refine (IsSetSemiring.iff _).mpr ⟨?_, ?_, ?_⟩
  · simp only [insert_pi, Set.mem_image, mem_inter_iff, Set.mem_pi]
    use fun _ ↦ ∅
    simp only [Set.preimage_empty, Set.empty_inter, and_true]
    refine ⟨(hC a ha).empty_mem, fun i a ↦ (hC i (hts a)).empty_mem⟩
  · exact IsPiSystem.pi_subset (insert a t)
      (fun i hi ↦ (hC i (Set.insert_subset ha hts hi)).isPiSystem)
  · intro u ⟨x, ⟨hx1, hx2⟩⟩ v ⟨y, ⟨hy1, hy2⟩⟩
    simp_rw [Set.mem_pi, Set.mem_insert_iff, insert_pi, ← singleton_pi] at hx1 hx2 hy1 hy2
    -- Write `u : Set ((i : ι) → α i)` as `x : (i : ι) → Set (α i)` with `u = {a}.pi x ∩ t.pi x`.
    have h1 (u : Set ι) (x : (i : ι) → Set (α i)) (hu : ∀ i ∈ u, x i ∈ C i) :
      u.pi x ∈ u.pi '' u.pi C :=
      Set.mem_image_of_mem u.pi <| Set.mem_pi.mpr fun i hi ↦ hu i hi
    have hx1' := h1 t x (fun i hi ↦ hx1 i (Or.inr hi))
    have hy1' := h1 t y (fun i hi ↦ hy1 i (Or.inr hi))
    clear h1
    -- Express `u \ v` using `x` and `y`.
    have h1 : u \ v = ((t.pi x \ t.pi y) ∩ (({a} : Set ι).pi x ∩ ({a} : Set ι).pi y))
        ∪ (t.pi x ∩ (({a} : Set ι).pi x \ ({a} : Set ι).pi y)) :=  by
      rw [← hx2, ← hy2, ← union_pi, ← union_pi]
      apply pi_setdiff_eq_union
    -- Show that the two sets from `h1` are disjoint.
    obtain h2 := pi_setdiff_union_disjoint ({a} : Set ι) t x y
    -- `K : Set (Set (α a))` is such that `x a \ y a = ⋃₀ K`.
    /- Several sets need to be constructed based on `K`.
        We use that convention that for some set system  `X`
        * `hX1` states that `X` is contained in the corresponding structure using the semiring;
        * `hX2` states that the set mentioned in `hX1` is pairwise disjoint;
        * `hX3` states that the union of sets from `hX1` is the corresponding set difference. -/
    obtain ⟨K, ⟨hK1, hK2, hK3⟩⟩ :=
      (hC a ha).diff_eq_sUnion' (x a) (hx1 a (Or.inl rfl)) (y a) (hy1 a (Or.inl rfl))
    -- `K' : (i : ι) → Set (Set (α i))` satisfies `K' a = K`.
    let K' : (i : ι) → Set (Set (α i)) :=
      fun (i : ι) => dite (i = a) (fun h ↦ h ▸ K.toSet) (fun _ ↦ (default : Set (Set (α i))))
    have hKK' : K = K' a := by simp only [dite_eq_ite, ↓reduceIte, K']
    haveI hE' : Fintype (({a} : Set ι).pi  '' ({a} : Set ι).pi K')
      := fintype_pi_ofFinset a K' K (by simp only [↓reduceDIte, K'])
    -- have hE1 := subset_pi_image_of_subset hK'1; clear hK'1
    have hE3 := pi_singleton_diff_eq_sUnion (hKK'.symm ▸ hK3)
    let F := Set.inter (t.pi x) '' (({a} : Set ι).pi  '' ({a} : Set ι).pi K')
    have hF1 : F ⊆ (insert a t).pi '' (insert a t).pi C :=
      pi_inter_image' (Set.disjoint_singleton_left.mpr t_fin) (fun i hi ↦ hx1 i (Or.inr hi))
        (fun i hi ↦ mem_singleton_iff.mp hi ▸ hKK' ▸ hK1)
    have hF2 : PairwiseDisjoint F id :=
      PairwiseDisjoint.image_of_le (pairwiseDisjoint_set_pi (hKK' ▸ hK2)) <|
      fun a b hb ↦ Set.mem_of_mem_inter_right hb
    have hF3 : ⋃₀ F = (t.pi x) ∩ (({a} : Set ι).pi x \ ({a} : Set ι).pi y) := by
      simp_rw [hE3, sUnion_eq_iUnion, iUnion_coe_set, inter_iUnion₂]
      simp only [singleton_pi, sUnion_image, Set.mem_image, Set.mem_preimage, Function.eval,
        iUnion_exists, biUnion_and', iUnion_iUnion_eq_right, F]
      rfl
    by_cases h : t.Nonempty
    rotate_left
    · have h : t = ∅ := Set.not_nonempty_iff_eq_empty.mp h; clear h_ind
      use F.toFinset
      simp only [coe_union, coe_toFinset]
      refine ⟨hF1, hF2, ?_⟩
      simp only [h, sdiff_self, Set.bot_eq_empty, Set.empty_inter,
        empty_pi, univ_inter, empty_union] at hF3 h1
      exact hF3.symm ▸ h1
    · have h_ind' := h_ind h; clear h h_ind
      let G := Set.inter (({a} : Set ι).pi y ∩ ({a} : Set ι).pi x) ''
        (h_ind'.disjointOfDiff hx1' hy1')
      have hG1 : G ⊆ (insert a t).pi '' (insert a t).pi C := by
        simp only [G]
        rw [← singleton_union, union_comm, ← Set.pi_inter_distrib]
        exact pi_inter_image (Set.disjoint_singleton_right.mpr t_fin)
          (fun i hi ↦ hi ▸ (hC a ha).inter_mem (y a)
          (hy1 a (Or.inl rfl)) (x a) (hx1 a (Or.inl rfl)))
            <| IsSetSemiring.subset_disjointOfDiff h_ind' hx1' hy1'
      have hG2 : PairwiseDisjoint G id := PairwiseDisjoint.image_of_le
        (h_ind'.pairwiseDisjoint_disjointOfDiff hx1' hy1') <| fun _ _ hb ↦
          Set.mem_of_mem_inter_right hb
      have hG3 : ⋃₀ G = ((({a} : Set ι).pi x ∩ ({a} : Set ι).pi y)) ∩ (t.pi x \ t.pi y) := by
        rw [← h_ind'.sUnion_disjointOfDiff hx1' hy1']
        nth_rewrite 2 [sUnion_eq_iUnion]
        rw [iUnion_coe_set, inter_iUnion₂, inter_comm]
        simp only [mem_coe, sUnion_image, G]
        rfl
      use F.toFinset ∪ G.toFinset
      simp only [coe_union, coe_toFinset]
      refine ⟨union_subset_iff.mpr ⟨hF1, hG1⟩, ?_, ?_⟩
      · apply (pairwiseDisjoint_union_of_disjoint (fun ⦃a b⦄ a ↦ a) hF2 hG2 )
        rw [hF3, hG3]
        nth_rewrite 2 [inter_comm]
        exact (Disjoint.symm h2)
      · rw [sUnion_union, hF3, hG3, h1, union_comm]
        nth_rewrite 2 [inter_comm]
        rfl

end piSemiring

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

/-- A ring is a semi-ring. -/
lemma isSetSemiring (hC : IsSetRing C) : IsSetSemiring C where
  empty_mem := hC.empty_mem
  inter_mem := fun _ hs _ ht => hC.inter_mem hs ht
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
  induction S using Finset.induction with
  | empty => simp [hC.empty_mem]
  | @insert i S _ h =>
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
  classical
  induction t using Finset.induction_on with
  | empty => exact hC.empty_mem
  | @insert m t hm ih =>
    simpa only [sup_insert] using
      hC.union_mem (hs m <| mem_insert_self m t) (ih <| fun i hi ↦ hs _ <| mem_insert_of_mem hi)

lemma partialSups_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι → Set α} (hs : ∀ n, s n ∈ C) (n : ι) :
    partialSups s n ∈ C := by
  simpa only [partialSups_apply, sup'_eq_sup] using hC.finsetSup_mem (fun i hi ↦ hs i)

lemma disjointed_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι → Set α} (hs : ∀ j, s j ∈ C) (i : ι) :
    disjointed s i ∈ C :=
  disjointedRec (fun _ j ht ↦ hC.diff_mem ht <| hs j) (hs i)

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
    Accumulate s n ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [accumulate_succ]; exact hC.union_mem hn (hs _)

end IsSetRing

end MeasureTheory
