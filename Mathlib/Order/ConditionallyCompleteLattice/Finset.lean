/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Conditionally complete lattices and finite sets.

-/


open Set

variable {ι α β γ : Type*}

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

theorem Finset.Nonempty.csSup_eq_max' {s : Finset α} (h : s.Nonempty) : sSup ↑s = s.max' h :=
  eq_of_forall_ge_iff fun _ => (csSup_le_iff s.bddAbove h.to_set).trans (s.max'_le_iff h).symm

theorem Finset.Nonempty.csInf_eq_min' {s : Finset α} (h : s.Nonempty) : sInf ↑s = s.min' h :=
  @Finset.Nonempty.csSup_eq_max' αᵒᵈ _ s h

theorem Finset.Nonempty.csSup_mem {s : Finset α} (h : s.Nonempty) : sSup (s : Set α) ∈ s := by
  rw [h.csSup_eq_max']
  exact s.max'_mem _

theorem Finset.Nonempty.csInf_mem {s : Finset α} (h : s.Nonempty) : sInf (s : Set α) ∈ s :=
  @Finset.Nonempty.csSup_mem αᵒᵈ _ _ h

theorem Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.Finite) : sSup s ∈ s := by
  lift s to Finset α using hs
  exact Finset.Nonempty.csSup_mem h

theorem Set.Nonempty.csInf_mem (h : s.Nonempty) (hs : s.Finite) : sInf s ∈ s :=
  @Set.Nonempty.csSup_mem αᵒᵈ _ _ h hs

theorem Set.Finite.csSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : sSup s < a ↔ ∀ x ∈ s, x < a :=
  ⟨fun h _ hx => (le_csSup hs.bddAbove hx).trans_lt h, fun H => H _ <| h.csSup_mem hs⟩

theorem Set.Finite.lt_csInf_iff (hs : s.Finite) (h : s.Nonempty) : a < sInf s ↔ ∀ x ∈ s, a < x :=
  @Set.Finite.csSup_lt_iff αᵒᵈ _ _ _ hs h

variable (f : ι → α)

theorem Finset.ciSup_eq_max'_image {s : Finset ι} (h : ∃ x ∈ s, sSup ∅ ≤ f x)
    (h' : (s.image f).Nonempty := by classical exact image_nonempty.mpr (h.imp fun _ ↦ And.left)) :
    ⨆ i ∈ s, f i = (s.image f).max' h' := by
  classical
  rw [iSup, ← h'.csSup_eq_max', coe_image]
  refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
  · simp only [ciSup_eq_ite, dite_eq_ite, Set.mem_range, Set.mem_image, mem_coe,
      exists_exists_and_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    split_ifs
    · exact ⟨_, by assumption, le_rfl⟩
    · obtain ⟨a, ha, ha'⟩ := h
      exact ⟨a, ha, ha'⟩
  · simp only [Set.mem_image, mem_coe, ciSup_eq_ite, dite_eq_ite, Set.mem_range,
      exists_exists_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro i hi
    refine ⟨i, ?_⟩
    simp [hi]

theorem Finset.ciInf_eq_min'_image {s : Finset ι} (h : ∃ x ∈ s, f x ≤ sInf ∅)
    (h' : (s.image f).Nonempty := by classical exact image_nonempty.mpr (h.imp fun _ ↦ And.left)) :
    ⨅ i ∈ s, f i = (s.image f).min' h' := by
  classical
  rw [← OrderDual.toDual_inj, toDual_min', toDual_iInf]
  simp only [Function.comp_apply, toDual_iInf]
  rw [ciSup_eq_max'_image _ h]
  simp only [image_image]
  congr

theorem Finset.ciSup_mem_image {s : Finset ι} (h : ∃ x ∈ s, sSup ∅ ≤ f x) :
    ⨆ i ∈ s, f i ∈ s.image f := by
  rw [ciSup_eq_max'_image _ h]
  exact max'_mem (image f s) _

theorem Finset.ciInf_mem_image {s : Finset ι} (h : ∃ x ∈ s, f x ≤ sInf ∅) :
    ⨅ i ∈ s, f i ∈ s.image f := by
  rw [ciInf_eq_min'_image _ h]
  exact min'_mem (image f s) _

theorem Set.Finite.ciSup_mem_image {s : Set ι} (hs : s.Finite) (h : ∃ x ∈ s, sSup ∅ ≤ f x) :
    ⨆ i ∈ s, f i ∈ f '' s := by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciSup_mem_image f h

theorem Set.Finite.ciInf_mem_image {s : Set ι} (hs : s.Finite) (h : ∃ x ∈ s, f x ≤ sInf ∅) :
    ⨅ i ∈ s, f i ∈ f '' s := by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciInf_mem_image f h

theorem Set.Finite.ciSup_lt_iff {s : Set ι} {f : ι → α} (hs : s.Finite)
    (h : ∃ x ∈ s, sSup ∅ ≤ f x) :
    ⨆ i ∈ s, f i < a ↔ ∀ x ∈ s, f x < a := by
  constructor
  · intro h x hx
    refine h.trans_le' (le_csSup ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sSup ∅))).subset ?_).bddAbove
      intro
      simp only [ciSup_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_exists_index]
      intro x hx
      split_ifs at hx
      · exact Or.inr ⟨_, by assumption, hx⟩
      · simp_all
    · simp only [mem_range]
      refine ⟨x, ?_⟩
      simp [hx]
  · intro H
    have := hs.ciSup_mem_image _ h
    simp only [mem_image] at this
    obtain ⟨_, hmem, hx⟩ := this
    rw [← hx]
    exact H _ hmem

theorem Set.Finite.lt_ciInf_iff {s : Set ι} {f : ι → α} (hs : s.Finite)
    (h : ∃ x ∈ s, f x ≤ sInf ∅) :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := by
  constructor
  · intro h x hx
    refine h.trans_le (csInf_le ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sInf ∅))).subset ?_).bddBelow
      intro
      simp only [ciInf_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_exists_index]
      intro x hx
      split_ifs at hx
      · exact Or.inr ⟨_, by assumption, hx⟩
      · simp_all
    · simp only [mem_range]
      refine ⟨x, ?_⟩
      simp [hx]
  · intro H
    have := hs.ciInf_mem_image _ h
    simp only [mem_image] at this
    obtain ⟨_, hmem, hx⟩ := this
    rw [← hx]
    exact H _ hmem

theorem Set.Finite.le_ciSup₂_of_le {ι : Sort*} {κ : ι → Prop} {f : ∀ i, κ i → α}
    (h_fin : (Set.range fun i : ι ↦ ⨆ j : κ i, f i j).Finite) (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  le_ciSup_of_le h_fin.bddAbove i
    (le_ciSup_of_le (Set.finite_range fun j : κ i ↦ f i j).bddAbove j h)

section ListMultiset

lemma List.iSup_mem_map_of_exists_sSup_empty_le {l : List ι} (f : ι → α)
    (h : ∃ x ∈ l, sSup ∅ ≤ f x) :
    ⨆ x ∈ l, f x ∈ l.map f := by
  classical
  simpa using l.toFinset.ciSup_mem_image f (by simpa using h)

lemma List.iInf_mem_map_of_exists_le_sInf_empty {l : List ι} (f : ι → α)
    (h : ∃ x ∈ l, f x ≤ sInf ∅) :
    ⨅ x ∈ l, f x ∈ l.map f := by
  classical
  simpa using l.toFinset.ciInf_mem_image f (by simpa using h)

lemma Multiset.iSup_mem_map_of_exists_sSup_empty_le {s : Multiset ι} (f : ι → α)
    (h : ∃ x ∈ s, sSup ∅ ≤ f x) :
    ⨆ x ∈ s, f x ∈ s.map f := by
  classical
  simpa using s.toFinset.ciSup_mem_image f (by simpa using h)

lemma Multiset.iInf_mem_map_of_exists_le_sInf_empty {s : Multiset ι} (f : ι → α)
    (h : ∃ x ∈ s, f x ≤ sInf ∅) :
    ⨅ x ∈ s, f x ∈ s.map f := by
  classical
  simpa using s.toFinset.ciInf_mem_image f (by simpa using h)

theorem exists_eq_ciSup_of_finite [Nonempty ι] [Finite ι] {f : ι → α} : ∃ i, f i = ⨆ i, f i :=
  Nonempty.csSup_mem (range_nonempty f) (finite_range f)

theorem exists_eq_ciInf_of_finite [Nonempty ι] [Finite ι] {f : ι → α} : ∃ i, f i = ⨅ i, f i :=
  Nonempty.csInf_mem (range_nonempty f) (finite_range f)

end ListMultiset

end ConditionallyCompleteLinearOrder

/-!
### Relation between `sSup` / `sInf` and `Finset.sup'` / `Finset.inf'`

Like the `Sup` of a `ConditionallyCompleteLattice`, `Finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/

namespace Finset

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α]

theorem sup'_eq_csSup_image (s : Finset ι) (H : s.Nonempty) (f : ι → α) :
    s.sup' H f = sSup (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [csSup_le_iff (s.finite_toSet.image f).bddAbove (H.to_set.image f)]

theorem inf'_eq_csInf_image (s : Finset ι) (H : s.Nonempty) (f : ι → α) :
    s.inf' H f = sInf (f '' s) :=
  sup'_eq_csSup_image (α := αᵒᵈ) _ H _

theorem sup'_id_eq_csSup (s : Finset α) (hs) : s.sup' hs id = sSup s := by
  rw [sup'_eq_csSup_image s hs, Set.image_id]

theorem inf'_id_eq_csInf (s : Finset α) (hs) : s.inf' hs id = sInf s :=
  sup'_id_eq_csSup (α := αᵒᵈ) _ hs

variable [Fintype ι] [Nonempty ι]

lemma sup'_univ_eq_ciSup (f : ι → α) : univ.sup' univ_nonempty f = ⨆ i, f i := by
  simp [sup'_eq_csSup_image, iSup]

lemma inf'_univ_eq_ciInf (f : ι → α) : univ.inf' univ_nonempty f = ⨅ i, f i := by
  simp [inf'_eq_csInf_image, iInf]

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α]

lemma sup_univ_eq_ciSup [Fintype ι] (f : ι → α) : univ.sup f = ⨆ i, f i :=
  le_antisymm
    (Finset.sup_le fun _ _ => le_ciSup (finite_range _).bddAbove _)
    (ciSup_le' fun _ => Finset.le_sup (mem_univ _))

theorem sup_eq_ciSup [Nonempty β] (s : Finset β) (f : β → α) :
    s.sup f = ⨆ (b : β) (_ : b ∈ s), f b := by
  apply le_antisymm ?_ (ciSup₂_le fun x ↦ Finset.le_sup)
  · apply Finset.sup_le
    intro a ha
    apply Set.Finite.le_ciSup₂_of_le _ a ha (le_refl (f a))
    have hrange : (Set.range fun b : β ↦ ⨆ _ : b ∈ s, f b) ⊆
      (Set.range fun b : s ↦ f b) ∪ {⊥} := by
      rintro y ⟨x, hxy⟩
      simp only [Set.mem_range, Set.union_singleton, Set.mem_insert_iff] at y ⊢
      by_cases hx : x ∈ s
      · right; simp only [hx, ciSup_pos] at hxy ; exact ⟨⟨x, hx⟩, hxy⟩
      · left; simp only [hx, ciSup_false] at hxy ; exact hxy.symm
    exact ((Set.range fun b : ↥s ↦ f ↑b) ∪ {⊥}).toFinite.subset hrange

end ConditionallyCompleteLinearOrderBot

end Finset

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α] (f : ι → α)

theorem Finset.Nonempty.ciSup_eq_max'_image {s : Finset ι} (h : s.Nonempty)
    (h' : (s.image f).Nonempty := h.image f) :
    ⨆ i ∈ s, f i = (s.image f).max' h' :=
  s.ciSup_eq_max'_image _ (h.imp (by simp)) _

theorem Finset.Nonempty.ciSup_mem_image {s : Finset ι} (h : s.Nonempty) :
    ⨆ i ∈ s, f i ∈ s.image f :=
  s.ciSup_mem_image _ (h.imp (by simp))

theorem Set.Nonempty.ciSup_mem_image {s : Set ι} (h : s.Nonempty) (hs : s.Finite) :
    ⨆ i ∈ s, f i ∈ f '' s :=
  hs.ciSup_mem_image _ (h.imp (by simp))

theorem Set.Nonempty.ciSup_lt_iff {s : Set ι} {a : α} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) :
    ⨆ i ∈ s, f i < a ↔ ∀ x ∈ s, f x < a :=
  hs.ciSup_lt_iff (h.imp (by simp))

section ListMultiset

lemma List.iSup_mem_map_of_ne_nil {l : List ι} (f : ι → α) (h : l ≠ []) :
    ⨆ x ∈ l, f x ∈ l.map f :=
  l.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_nil _ h)

lemma Multiset.iSup_mem_map_of_ne_zero {s : Multiset ι} (f : ι → α) (h : s ≠ 0) :
    ⨆ x ∈ s, f x ∈ s.map f :=
  s.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_zero h)

end ListMultiset

end ConditionallyCompleteLinearOrderBot
