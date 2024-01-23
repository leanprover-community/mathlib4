
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Basic

open Set

open scoped BigOperators

namespace Finset

variable {α β : Type*}

lemma mem_map_univ_asEmbedding {α β : Type*} [Fintype α] {p : β → Prop}
    (e : α ≃ Subtype p) {b : β} :
    b ∈ Finset.map e.asEmbedding univ ↔ p b := by
  rw [mem_map]
  simp only [Finset.mem_univ, Equiv.asEmbedding_apply, Function.comp_apply, exists_true_left,
    true_and]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := h
    exact (e a).prop
  · obtain ⟨a, ha⟩ := e.surjective ⟨b, h⟩
    refine ⟨a, ?_⟩
    rw [ha]

/-- An ordering of the elements of a finset. -/
noncomputable def ordered (J : Finset α) : Fin J.card ↪ α :=
  J.equivFin.symm.asEmbedding

lemma ordered_mem {J : Finset α} (n : Fin J.card) : J.ordered n ∈ J := by
  simp_rw [Finset.ordered]; exact coe_mem _

lemma map_ordered (J : Finset α) : Finset.map J.ordered (univ : Finset (Fin J.card)) = J := by
  ext; simp_rw [Finset.ordered, Finset.mem_map_univ_asEmbedding]

lemma sum_ordered [AddCommMonoid β] (J : Finset α) (m : α → β) :
    ∑ i : Fin J.card, m (J.ordered i) = ∑ u in J, m u := by
  conv_rhs => rw [← map_ordered J]
  rw [sum_map]

/-- The n first elements in `J.ordered`. -/
noncomputable def finsetLT (J : Finset α) : Fin J.card → Finset α :=
  fun n ↦ (Finset.filter (fun j : Fin J.card ↦ j < n) univ).map J.ordered

@[simp]
lemma mem_finsetLT (J : Finset α) (n : Fin J.card) (s : α) :
    s ∈ finsetLT J n ↔ ∃ m < n, s = J.ordered m := by
  rw [finsetLT, mem_map]
  simp only [mem_filter, Finset.mem_univ, true_and_iff, Equiv.asEmbedding_apply,
    Function.comp_apply, exists_prop]
  simp_rw [@eq_comm _ _ s]

lemma ordered_mem_finsetLT (J : Finset α) {n m : Fin J.card} (hnm : n < m) :
    J.ordered n ∈ finsetLT J m := by rw [mem_finsetLT _ _]; exact ⟨n, hnm, rfl⟩

@[simp]
lemma finsetLT_zero {J : Finset α} (hJ : 0 < J.card) : finsetLT J ⟨0, hJ⟩ = ∅ := by
  rw [finsetLT]
  simp only [univ_eq_attach, map_eq_empty, filter_eq_empty_iff]
  intro n _
  rw [not_lt, ← Fin.eta n n.2, Fin.mk_le_mk]
  exact zero_le'

lemma finsetLT_mono (J : Finset α) : Monotone (finsetLT J) := by
  intro n m hnm s
  rw [finsetLT, mem_map]
  rintro ⟨i, hi, rfl⟩
  refine ordered_mem_finsetLT J ?_
  rw [mem_filter] at hi
  exact hi.2.trans_le hnm

lemma finsetLT_subset (J : Finset α) (n : Fin J.card) : finsetLT J n ⊆ J := by
  intro u; rw [finsetLT, mem_map]; rintro ⟨i, _, rfl⟩; exact ordered_mem i

lemma biUnion_finsetLT (J : Finset α) (n : Fin J.card) :
    ⋃ i ≤ n, (finsetLT J i : Set α) = finsetLT J n := by
  ext x
  simp only [mem_iUnion, mem_coe, mem_finsetLT, exists_prop]
  exact ⟨fun ⟨i, hin, ⟨m, hmi, h⟩⟩ ↦ ⟨m, hmi.trans_le hin, h⟩,
    fun ⟨m, hmn, h⟩ ↦ ⟨n, le_rfl, m, hmn, h⟩⟩

section FinsetSet

variable {C : Set (Set α)} {J : Finset (Set α)}

lemma iUnion_ordered (J : Finset (Set α)) : (⋃ i, J.ordered i) = ⋃₀ J := by
  conv_rhs => rw [← map_ordered J]
  simp_rw [sUnion_eq_biUnion, coe_map, Set.biUnion_image]
  simp only [mem_coe, Finset.mem_univ, iUnion_true]

lemma finsetLT_subset' (J : Finset (Set α)) (hJ : ↑J ⊆ C) (n : Fin J.card) :
    ↑(finsetLT J n) ⊆ C :=
  (Finset.coe_subset.mpr (finsetLT_subset J n)).trans hJ

lemma sUnion_finsetLT_eq_biUnion (J : Finset (Set α)) (n : Fin J.card) :
    ⋃₀ (finsetLT J n : Set (Set α)) = ⋃ i < n, J.ordered i := by
  ext1 a
  simp_rw [mem_sUnion, mem_coe, mem_finsetLT, mem_iUnion]
  constructor
  · rintro ⟨t, ⟨m, hmn, rfl⟩, hat⟩
    exact ⟨m, hmn, hat⟩
  · rintro ⟨m, hmn, hat⟩
    exact ⟨J.ordered m, ⟨m, hmn, rfl⟩, hat⟩

end FinsetSet

end Finset
