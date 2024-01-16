/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.Data.Real.ENNReal
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Data.Finset.Ordered

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

open scoped ENNReal BigOperators

-- TODO: move this
lemma monotone_partialSups {α : Type*} [SemilatticeSup α] (f : ℕ → α) :
    Monotone fun n ↦ partialSups f n :=
  fun n _ hnm ↦ partialSups_le f n _ (fun _ hm'n ↦ le_partialSups_of_le _ (hm'n.trans hnm))

-- TODO: move this
lemma partialSups_eq_sUnion_image {α : Type*} [DecidableEq (Set α)] (s : ℕ → Set α) (n : ℕ) :
    partialSups s n = ⋃₀ ↑(Finset.image s (range (n + 1))) := by
  ext
  simp only [partialSups_eq_biSup, iSup_eq_iUnion, Set.mem_sUnion, mem_iUnion, exists_prop, mem_coe,
  Finset.mem_image, Finset.mem_range, exists_exists_and_eq_and, Nat.lt_succ_iff]

-- TODO: move this
lemma partialSups_eq_biUnion_range {α : Type*} (s : ℕ → Set α) (n : ℕ) :
    partialSups s n = ⋃ i ∈ Finset.range (n + 1), s i := by
  ext a
  simp only [Set.le_eq_subset, partialSups_eq_biSup, iSup_eq_iUnion, mem_iUnion, exists_prop,
    Finset.mem_range, Nat.lt_succ]

lemma Finset.sUnion_disjUnion {α β : Type*} {f : α → Finset (Set β)} (I : Finset α)
    (hf : (I : Set α).PairwiseDisjoint f) :
    ⋃₀ (I.disjiUnion f hf : Set (Set β)) = ⋃ a ∈ I, ⋃₀ ↑(f a) := by
  ext1 b
  simp only [mem_sUnion, mem_iUnion, mem_coe, exists_prop, mem_disjiUnion]
  constructor
  · rintro ⟨t, ⟨a, haI, hatf⟩, hbt⟩
    exact ⟨a, haI, t, hatf, hbt⟩
  · rintro ⟨a, haI, t, hatf, hbt⟩
    exact ⟨t, ⟨a, haI, hatf⟩, hbt⟩

-- TODO: move this
lemma Finset.sum_image_of_disjoint {α ι : Type*} [PartialOrder α] [OrderBot α] [DecidableEq α]
    (m : α → ℝ≥0∞) (m_bot : m ⊥ = 0)
    (f : ι → α) (I : Finset ι) (hf_disj : (I : Set ι).PairwiseDisjoint f) :
    ∑ s in image f I, m s = ∑ i in I, m (f i) := by
  rw [sum_image']
  intro n hnI
  by_cases hfn : f n = ⊥
  · simp only [hfn, m_bot]
    refine (sum_eq_zero fun i hi ↦ ?_).symm
    rw [mem_filter] at hi
    rw [hi.2, m_bot]
  · classical
    have : filter (fun j ↦ f j = f n) I = filter (fun j ↦ j = n) I := by
      ext j
      simp only [mem_filter, and_congr_right_iff]
      intro hj
      refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
      by_contra hij
      have h_dis : Disjoint (f j) (f n) := hf_disj hj hnI hij
      rw [h] at h_dis
      simp only [disjoint_self] at h_dis
      exact hfn h_dis
    simp_rw [this]
    simp only [sum_filter, sum_ite_eq', if_pos hnI]

-- TODO: move this
lemma Finset.sum_image_le {ι α β : Type*} [DecidableEq α] [OrderedSemiring β] (J : Finset ι)
    (g : ι → α) (f : α → β) (hf : ∀ u ∈ J.image g, 0 ≤ f u) :
    ∑ u in J.image g, f u ≤ ∑ u in J, f (g u) := by
  rw [sum_comp f g]
  refine sum_le_sum fun a hag => ?_
  let hag' := hag
  rw [Finset.mem_image] at hag'
  obtain ⟨i, hi, hig⟩ := hag'
  suffices 1 ≤ (J.filter (fun j => g j = a)).card by
    conv_lhs => rw [← one_smul ℕ (f a)]
    simp_rw [nsmul_eq_mul]
    exact mul_le_mul (Nat.mono_cast this) le_rfl (hf a hag) (Nat.cast_nonneg _)
  rw [Nat.succ_le_iff, card_pos]
  refine ⟨i, ?_⟩
  rw [mem_filter]
  exact ⟨hi, hig⟩

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

/-- A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `s \ t` is equal to a disjoint union of finitely many sets in `C`. -/
structure IsSetSemiring (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  inter_mem : ∀ s ∈ C, ∀ t ∈ C, s ∩ t ∈ C
  diff_eq_Union' : ∀ s ∈ C, ∀ t ∈ C,
    ∃ I : Finset (Set α), ↑I ⊆ C ∧ PairwiseDisjoint (I : Set (Set α)) id ∧ s \ t = ⋃₀ I

namespace IsSetSemiring

lemma isPiSystem (hC : IsSetSemiring C) : IsPiSystem C := fun s hs t ht _ ↦ hC.inter_mem s hs t ht

section diffFinset

open Classical in
/-- In a semi-ring of sets `C`, for all sets `s, t ∈ C`, `s \ t` is equal to a disjoint union of
finitely many sets in `C`. The finite set of sets in the union is not unique, but this definition
gives an arbitrary `Finset (Set α)` that satisfies the equality.

We remove the empty set to ensure that `t ∉ hC.diffFinset hs ht` even if `t = ∅`. -/
noncomputable def diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    Finset (Set α) :=
  (hC.diff_eq_Union' s hs t ht).choose \ {∅}

lemma empty_not_mem_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ∅ ∉ hC.diffFinset hs ht := by
  classical
  simp only [diffFinset, mem_sdiff, Finset.mem_singleton, eq_self_iff_true, not_true,
    and_false_iff, not_false_iff]

lemma diffFinset_subset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ↑(hC.diffFinset hs ht) ⊆ C := by
  classical
  simp only [diffFinset, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  exact (hC.diff_eq_Union' s hs t ht).choose_spec.1.trans (Set.subset_insert _ _)

lemma pairwiseDisjoint_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    PairwiseDisjoint (hC.diffFinset hs ht : Set (Set α)) id := by
  classical
  simp only [diffFinset, coe_sdiff, coe_singleton]
  exact Set.PairwiseDisjoint.subset (hC.diff_eq_Union' s hs t ht).choose_spec.2.1
      (Set.diff_subset _ _)

lemma sUnion_diffFinset (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C) :
    ⋃₀ hC.diffFinset hs ht = s \ t := by
  classical
  rw [(hC.diff_eq_Union' s hs t ht).choose_spec.2.2]
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
  simp_rw [id.def]
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
    ∃ (J : Finset (Set α)) (_h_ss : ↑J ⊆ C) (_h_dis : PairwiseDisjoint (J : Set (Set α)) id),
      s \ ⋃₀ I = ⋃₀ J := by
  classical
  revert hI
  refine Finset.induction ?_ ?_ I
  · intro
    simp only [coe_empty, sUnion_empty, diff_empty, exists_prop]
    refine ⟨{s}, singleton_subset_set_iff.mpr hs, ?_⟩
    simp only [coe_singleton, pairwiseDisjoint_singleton, sUnion_singleton, eq_self_iff_true,
      and_self_iff]
  intro t I' _ h h_insert_subset
  rw [coe_insert] at h_insert_subset
  have ht : t ∈ C := h_insert_subset (Set.mem_insert _ _)
  obtain ⟨J, h_ss, h_dis, h_eq⟩ := h ((Set.subset_insert _ _).trans h_insert_subset)
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
    exact disjoint_of_subset (Set.diff_subset u t) (Set.diff_subset v t) huv_disj
  let J' : Finset (Set α) := Finset.biUnion (Finset.univ : Finset J) fun u ↦ Ju u (h_ss u.prop)
  have hJ'_subset : ↑J' ⊆ C := by
    intro u
    simp only [Subtype.coe_mk, univ_eq_attach, coe_biUnion, mem_coe, mem_attach, iUnion_true,
      mem_iUnion, Finset.exists_coe, bex_imp]
    intro v hv huvt
    exact hJu_subset v (h_ss hv) huvt
  refine ⟨J', hJ'_subset, ?_, ?_⟩
  · rw [Finset.coe_biUnion]
    refine PairwiseDisjoint.biUnion ?_ ?_
    · simp only [univ_eq_attach, mem_coe, id.def, iSup_eq_iUnion]
      simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
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
    simp_rw [sUnion_eq_biUnion, Set.iUnion_diff]
    simp only [Subtype.coe_mk, mem_coe, Finset.mem_biUnion, Finset.mem_univ, exists_true_left,
      Finset.exists_coe, iUnion_exists, true_and]
    rw [iUnion_comm]
    refine iUnion_congr fun i ↦ ?_
    by_cases hi : i ∈ J
    · simp only [hi, iUnion_true, exists_prop]
      rw [← hJu_sUnion i (h_ss hi), sUnion_eq_biUnion]
      simp only [mem_coe]
    · simp only [hi, iUnion_of_empty, iUnion_empty]

open Classical in
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
  exact (hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.choose.trans (Set.subset_insert _ _)

lemma pairwiseDisjoint_diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    PairwiseDisjoint (hC.diffFinset₀ hs hI : Set (Set α)) id := by
  classical
  simp only [diffFinset₀, coe_sdiff, coe_singleton]
  exact Set.PairwiseDisjoint.subset
    (hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.choose_spec.choose (Set.diff_subset _ _)

lemma diff_sUnion_eq_sUnion_diffFinset₀ (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    s \ ⋃₀ I = ⋃₀ hC.diffFinset₀ hs hI := by
  classical
  rw [(hC.exists_disjoint_finset_diff_eq hs hI).choose_spec.choose_spec.choose_spec]
  simp only [diffFinset₀, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  rw [sUnion_diff_singleton_empty]

lemma sUnion_diffFinset₀_subset (hC : IsSetSemiring C) (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ⋃₀ (hC.diffFinset₀ hs hI : Set (Set α)) ⊆ s := by
  rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀]
  exact diff_subset _ _

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
  simp_rw [id.def]
  exact disjoint_of_subset (subset_sUnion_of_mem hu) (subset_sUnion_of_mem hv)
    (hC.disjoint_sUnion_diffFinset₀ hs hI)

lemma sUnion_union_sUnion_diffFinset₀_of_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (hI_ss : ⋃₀ ↑I ⊆ s) :
    ⋃₀ I ∪ ⋃₀ hC.diffFinset₀ hs hI = s := by
  conv_rhs => rw [← union_diff_cancel hI_ss, hC.diff_sUnion_eq_sUnion_diffFinset₀ hs hI]

lemma sUnion_union_diffFinset₀_of_subset (hC : IsSetSemiring C) (hs : s ∈ C)
    (hI : ↑I ⊆ C) (hI_ss : ⋃₀ ↑I ⊆ s) [DecidableEq (Set α)] :
    ⋃₀ ↑(I ∪ hC.diffFinset₀ hs hI) = s := by
  conv_rhs => rw [← sUnion_union_sUnion_diffFinset₀_of_subset hC hs hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

end diffFinset₀

section indexedDiffFinset₀

variable [DecidableEq (Set α)]

/-- A finite set of sets in `C` such that
`⋃₀ ↑(hC.indexedDiffFinset₀ J hJ n) = J.ordered n \ ⋃₀ finsetLT J n`. -/
noncomputable def indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : Finset (Set α) :=
  hC.diffFinset₀ (ordered_mem' hJ n) (finsetLT_subset' J hJ n)

lemma sUnion_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ⋃₀ ↑(hC.indexedDiffFinset₀ J hJ n) = J.ordered n \ ⋃₀ finsetLT J n :=
  (hC.diff_sUnion_eq_sUnion_diffFinset₀ _ _).symm

lemma indexedDiffFinset₀_subset (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ↑(hC.indexedDiffFinset₀ J hJ n) ⊆ C :=
  hC.diffFinset₀_subset _ _

lemma sUnion_indexedDiffFinset₀_subset (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) :
    ⋃₀ ↑(hC.indexedDiffFinset₀ J hJ n) ⊆ J.ordered n :=
  subset_trans (hC.sUnion_indexedDiffFinset₀ J hJ n).subset (Set.diff_subset _ _)

lemma empty_not_mem_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) :
    ∅ ∉ hC.indexedDiffFinset₀ J hJ n := by
  rw [indexedDiffFinset₀]; exact hC.empty_not_mem_diffFinset₀ _ _

lemma subset_ordered_of_mem_indexedDiffFinset₀ (hC : IsSetSemiring C)
    (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n : Fin J.card} (h : s ∈ hC.indexedDiffFinset₀ J hJ n) :
    s ⊆ J.ordered n :=
  (subset_sUnion_of_mem h).trans
    (hC.sUnion_diffFinset₀_subset (ordered_mem' hJ n) (finsetLT_subset' J hJ n))

lemma iUnion_sUnion_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    (⋃ i, ⋃₀ (hC.indexedDiffFinset₀ J hJ i : Set (Set α))) = ⋃₀ J := by
  rw [← iUnion_ordered]
  refine subset_antisymm (fun a ↦ ?_) (fun a ↦ ?_)
  · simp_rw [mem_iUnion, mem_sUnion]
    rintro ⟨i, t, ht, hat⟩
    exact ⟨i, subset_ordered_of_mem_indexedDiffFinset₀ hC J hJ ht hat⟩
  · simp_rw [mem_iUnion]
    intro h
    have h' : ∃ (i : ℕ) (hi : i < J.card), a ∈ J.ordered ⟨i, hi⟩ := by
      obtain ⟨i, hai⟩ := h
      refine ⟨i.1, i.2, ?_⟩
      convert hai
    classical
    let i : ℕ := Nat.find h'
    have hi : i < J.card := (Nat.find_spec h').choose
    have ha_mem_i : a ∈ J.ordered ⟨i, hi⟩ := (Nat.find_spec h').choose_spec
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [sUnion_indexedDiffFinset₀, Set.mem_diff]
    refine ⟨ha_mem_i, ?_⟩
    rw [sUnion_finsetLT_eq_bUnion]
    simp only [mem_iUnion, exists_prop, not_exists, not_and]
    intro j hj_lt hj
    have hj_lt' : ↑j < i := by rwa [← Fin.eta j j.2, Fin.mk_lt_mk] at hj_lt
    refine (Nat.lt_find_iff h' j).mp hj_lt' j le_rfl ⟨hj_lt'.trans hi, ?_⟩
    convert hj

lemma disjoint_sUnion_finsetLT_of_mem_indexedDiffFinset₀
    (hC : IsSetSemiring C) (J : Finset (Set α))
    (hJ : ↑J ⊆ C) {n : Fin J.card} (h : s ∈ hC.indexedDiffFinset₀ J hJ n) :
    Disjoint s (⋃₀ finsetLT J n) := by
  refine Disjoint.mono_left (subset_sUnion_of_mem h : s ⊆ ⋃₀ ↑(hC.indexedDiffFinset₀ J hJ n)) ?_
  rw [sUnion_indexedDiffFinset₀ hC J hJ n, Set.disjoint_iff_inter_eq_empty, Set.inter_comm,
    inter_diff_self]

lemma disjoint_ordered_of_mem_indexedDiffFinset₀ (hC : IsSetSemiring C)
    (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (h : s ∈ hC.indexedDiffFinset₀ J hJ n) (hnm : m < n) :
    Disjoint s (J.ordered m) := by
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_finsetLT_of_mem_indexedDiffFinset₀ J hJ h)
  exact subset_sUnion_of_mem (ordered_mem_finsetLT J hnm)

lemma disjoint_of_mem_indexedDiffFinset₀_of_lt (hC : IsSetSemiring C)
    (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n < m) (hs : s ∈ hC.indexedDiffFinset₀ J hJ n)
    (ht : t ∈ hC.indexedDiffFinset₀ J hJ m) : Disjoint s t := by
  have hs_subset : s ⊆ J.ordered n := hC.subset_ordered_of_mem_indexedDiffFinset₀ J hJ hs
  have hs_disj : Disjoint t (J.ordered n) :=
    hC.disjoint_ordered_of_mem_indexedDiffFinset₀ J hJ ht hnm
  exact Disjoint.mono_left hs_subset hs_disj.symm

lemma disjoint_of_mem_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n ≠ m) (hs : s ∈ hC.indexedDiffFinset₀ J hJ n)
    (ht : t ∈ hC.indexedDiffFinset₀ J hJ m) : Disjoint s t := by
  cases' lt_or_lt_iff_ne.mpr hnm with h h
  · exact hC.disjoint_of_mem_indexedDiffFinset₀_of_lt J hJ h hs ht
  · exact (hC.disjoint_of_mem_indexedDiffFinset₀_of_lt J hJ h ht hs).symm

lemma disjoint_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n ≠ m) :
    Disjoint (hC.indexedDiffFinset₀ J hJ n) (hC.indexedDiffFinset₀ J hJ m) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext1 s
  simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false_iff, not_and]
  intro hsn hsm
  have : Disjoint s s := hC.disjoint_of_mem_indexedDiffFinset₀ J hJ hnm hsn hsm
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_self] at this
  rw [this] at hsn
  exact hC.empty_not_mem_indexedDiffFinset₀ _ _ _ hsn

lemma pairwiseDisjoint_indexedDiffFinset₀ (hC : IsSetSemiring C)
    (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint (↑(univ : Finset (Fin J.card))) (hC.indexedDiffFinset₀ J hJ) :=
  fun _ _ _ _ hnm ↦ hC.disjoint_indexedDiffFinset₀ J hJ hnm

lemma pairwiseDisjoint_indexedDiffFinset₀' (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : PairwiseDisjoint ↑(hC.indexedDiffFinset₀ J hJ n) (id : Set α → Set α) :=
  hC.pairwiseDisjoint_diffFinset₀ _ _

end indexedDiffFinset₀

section AllDiffFinset₀

variable [DecidableEq (Set α)]

/-- This is a finset of pairwise disjoint sets in the set semi-ring `C`, such that
`⋃₀ hC.allDiffFinset₀ J hJ = ⋃₀ J`. -/
noncomputable def allDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    Finset (Set α) :=
  Finset.disjiUnion univ (hC.indexedDiffFinset₀ J hJ) (hC.pairwiseDisjoint_indexedDiffFinset₀ J hJ)

lemma pairwiseDisjoint_allDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint ↑(hC.allDiffFinset₀ J hJ) (id : Set α → Set α) := by
  intro u hu v hv huv
  simp_rw [Function.onFun, id.def]
  simp_rw [allDiffFinset₀, mem_coe, Finset.mem_disjiUnion] at hu hv
  obtain ⟨n, _, huBn⟩ := hu
  obtain ⟨m, _, hvBm⟩ := hv
  by_cases hnm : n = m
  · rw [← hnm] at hvBm
    exact hC.pairwiseDisjoint_indexedDiffFinset₀' _ _ n huBn hvBm huv
  · exact hC.disjoint_of_mem_indexedDiffFinset₀ J hJ hnm huBn hvBm

lemma allDiffFinset₀_subset (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ↑(hC.allDiffFinset₀ J hJ) ⊆ C := by
  intro s
  rw [mem_coe, allDiffFinset₀, mem_disjiUnion]
  rintro ⟨n, _, h_mem⟩
  exact hC.indexedDiffFinset₀_subset J hJ n h_mem

lemma sUnion_allDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ⋃₀ (hC.allDiffFinset₀ J hJ : Set (Set α)) = ⋃₀ J := by
  simp only [allDiffFinset₀, Finset.sUnion_disjUnion, Finset.mem_univ, iUnion_true,
    iUnion_sUnion_indexedDiffFinset₀]

end AllDiffFinset₀

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
  diff_eq_Union' := by
    refine fun s hs t ht => ⟨{s \ t}, ?_, ?_, ?_⟩
    · simp only [coe_singleton, Set.singleton_subset_iff]
      exact hC.diff_mem hs ht
    · simp only [coe_singleton, pairwiseDisjoint_singleton]
    · simp only [coe_singleton, sUnion_singleton]

lemma biUnion_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hs : ∀ n ∈ S, s n ∈ C) :
    (⋃ i ∈ S, s i) ∈ C := by
  classical
  revert hs
  refine Finset.induction ?_ ?_ S
  · simp [hC.empty_mem]
  · intro i S _ h hs
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS ↦ hs n (mem_insert_of_mem hnS))

lemma biInter_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hS : S.Nonempty) (hs : ∀ n ∈ S, s n ∈ C) :
    (⋂ i ∈ S, s i) ∈ C := by
  classical
  revert hs
  refine hS.cons_induction ?_ ?_
  · simp
  · intro i S _ _ h hs
    simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?_
    exact h (fun n hnS ↦ hs.2 n hnS)

lemma partialSups_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    partialSups s n ∈ C := by
  rw [partialSups_eq_biUnion_range]
  exact hC.biUnion_mem _ (fun n _ ↦ hs n)

lemma disjointed_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    disjointed s n ∈ C := by
  cases n with
  | zero => rw [disjointed_zero]; exact hs 0
  | succ n => rw [disjointed_succ]; exact hC.diff_mem (hs n.succ) (hC.partialSups_mem hs n)

end IsSetRing

end MeasureTheory
