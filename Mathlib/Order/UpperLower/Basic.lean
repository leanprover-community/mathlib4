/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Interval.Set.OrderEmbedding
import Mathlib.Order.SetNotation
import Mathlib.Order.WellFounded

/-!
# Properties of unbundled upper/lower sets

This file proves results on `IsUpperSet` and `IsLowerSet`, including their interactions with
set operations, images, preimages and order duals, and properties that reflect stronger assumptions
on the underlying order (such as `PartialOrder` and `LinearOrder`).

## TODO

* Lattice structure on antichains.
* Order equivalence between upper/lower sets and antichains.
-/

open OrderDual Set

variable {α β : Type*} {ι : Sort*} {κ : ι → Sort*}

attribute [aesop norm unfold] IsUpperSet IsLowerSet

section LE

variable [LE α] {s t : Set α} {a : α}

theorem isUpperSet_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id

theorem isLowerSet_empty : IsLowerSet (∅ : Set α) := fun _ _ _ => id

theorem isUpperSet_univ : IsUpperSet (univ : Set α) := fun _ _ _ => id

theorem isLowerSet_univ : IsLowerSet (univ : Set α) := fun _ _ _ => id

theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ := fun _a _b h hb ha => hb <| hs h ha

theorem IsLowerSet.compl (hs : IsLowerSet s) : IsUpperSet sᶜ := fun _a _b h hb ha => hb <| hs h ha

@[simp]
theorem isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s :=
  ⟨fun h => by
    convert h.compl
    rw [compl_compl], IsLowerSet.compl⟩

@[simp]
theorem isLowerSet_compl : IsLowerSet sᶜ ↔ IsUpperSet s :=
  ⟨fun h => by
    convert h.compl
    rw [compl_compl], IsUpperSet.compl⟩

theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∪ t) :=
  fun _ _ h => Or.imp (hs h) (ht h)

theorem IsLowerSet.union (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∪ t) :=
  fun _ _ h => Or.imp (hs h) (ht h)

theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∩ t) :=
  fun _ _ h => And.imp (hs h) (ht h)

theorem IsLowerSet.inter (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∩ t) :=
  fun _ _ h => And.imp (hs h) (ht h)

theorem isUpperSet_sUnion {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋃₀ S) :=
  fun _ _ h => Exists.imp fun _ hs => ⟨hs.1, hf _ hs.1 h hs.2⟩

theorem isLowerSet_sUnion {S : Set (Set α)} (hf : ∀ s ∈ S, IsLowerSet s) : IsLowerSet (⋃₀ S) :=
  fun _ _ h => Exists.imp fun _ hs => ⟨hs.1, hf _ hs.1 h hs.2⟩

theorem isUpperSet_iUnion {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) :=
  isUpperSet_sUnion <| forall_mem_range.2 hf

theorem isLowerSet_iUnion {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋃ i, f i) :=
  isLowerSet_sUnion <| forall_mem_range.2 hf

theorem isUpperSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋃ (i) (j), f i j) :=
  isUpperSet_iUnion fun i => isUpperSet_iUnion <| hf i

theorem isLowerSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) :
    IsLowerSet (⋃ (i) (j), f i j) :=
  isLowerSet_iUnion fun i => isLowerSet_iUnion <| hf i

theorem isUpperSet_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋂₀ S) :=
  fun _ _ h => forall₂_imp fun s hs => hf s hs h

theorem isLowerSet_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsLowerSet s) : IsLowerSet (⋂₀ S) :=
  fun _ _ h => forall₂_imp fun s hs => hf s hs h

theorem isUpperSet_iInter {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) :=
  isUpperSet_sInter <| forall_mem_range.2 hf

theorem isLowerSet_iInter {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋂ i, f i) :=
  isLowerSet_sInter <| forall_mem_range.2 hf

theorem isUpperSet_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋂ (i) (j), f i j) :=
  isUpperSet_iInter fun i => isUpperSet_iInter <| hf i

theorem isLowerSet_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) :
    IsLowerSet (⋂ (i) (j), f i j) :=
  isLowerSet_iInter fun i => isLowerSet_iInter <| hf i

@[simp]
theorem isLowerSet_preimage_ofDual_iff : IsLowerSet (ofDual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
theorem isUpperSet_preimage_ofDual_iff : IsUpperSet (ofDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[simp]
theorem isLowerSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsLowerSet (toDual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
theorem isUpperSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsUpperSet (toDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

alias ⟨_, IsUpperSet.toDual⟩ := isLowerSet_preimage_ofDual_iff

alias ⟨_, IsLowerSet.toDual⟩ := isUpperSet_preimage_ofDual_iff

alias ⟨_, IsUpperSet.ofDual⟩ := isLowerSet_preimage_toDual_iff

alias ⟨_, IsLowerSet.ofDual⟩ := isUpperSet_preimage_toDual_iff

lemma IsUpperSet.isLowerSet_preimage_coe (hs : IsUpperSet s) :
    IsLowerSet ((↑) ⁻¹' t : Set s) ↔ ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t := by aesop

lemma IsLowerSet.isUpperSet_preimage_coe (hs : IsLowerSet s) :
    IsUpperSet ((↑) ⁻¹' t : Set s) ↔ ∀ b ∈ s, ∀ c ∈ t, c ≤ b → b ∈ t := by aesop

lemma IsUpperSet.sdiff (hs : IsUpperSet s) (ht : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    IsUpperSet (s \ t) :=
  fun _b _c hbc hb ↦ ⟨hs hbc hb.1, fun hc ↦ hb.2 <| ht _ hb.1 _ hc hbc⟩

lemma IsLowerSet.sdiff (hs : IsLowerSet s) (ht : ∀ b ∈ s, ∀ c ∈ t, c ≤ b → b ∈ t) :
    IsLowerSet (s \ t) :=
  fun _b _c hcb hb ↦ ⟨hs hcb hb.1, fun hc ↦ hb.2 <| ht _ hb.1 _ hc hcb⟩

lemma IsUpperSet.sdiff_of_isLowerSet (hs : IsUpperSet s) (ht : IsLowerSet t) : IsUpperSet (s \ t) :=
  hs.sdiff <| by aesop

lemma IsLowerSet.sdiff_of_isUpperSet (hs : IsLowerSet s) (ht : IsUpperSet t) : IsLowerSet (s \ t) :=
  hs.sdiff <| by aesop

lemma IsUpperSet.erase (hs : IsUpperSet s) (has : ∀ b ∈ s, b ≤ a → b = a) : IsUpperSet (s \ {a}) :=
  hs.sdiff <| by simpa using has

lemma IsLowerSet.erase (hs : IsLowerSet s) (has : ∀ b ∈ s, a ≤ b → b = a) : IsLowerSet (s \ {a}) :=
  hs.sdiff <| by simpa using has

end LE

section Preorder

variable [Preorder α] [Preorder β] {s : Set α} {p : α → Prop} (a : α)

theorem isUpperSet_Ici : IsUpperSet (Ici a) := fun _ _ => ge_trans

theorem isLowerSet_Iic : IsLowerSet (Iic a) := fun _ _ => le_trans

theorem isUpperSet_Ioi : IsUpperSet (Ioi a) := fun _ _ => flip lt_of_lt_of_le

theorem isLowerSet_Iio : IsLowerSet (Iio a) := fun _ _ => lt_of_le_of_lt

theorem isUpperSet_iff_Ici_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ici a ⊆ s := by
  simp [IsUpperSet, subset_def, @forall_swap (_ ∈ s)]

theorem isLowerSet_iff_Iic_subset : IsLowerSet s ↔ ∀ ⦃a⦄, a ∈ s → Iic a ⊆ s := by
  simp [IsLowerSet, subset_def, @forall_swap (_ ∈ s)]

alias ⟨IsUpperSet.Ici_subset, _⟩ := isUpperSet_iff_Ici_subset

alias ⟨IsLowerSet.Iic_subset, _⟩ := isLowerSet_iff_Iic_subset

theorem IsUpperSet.Ioi_subset (h : IsUpperSet s) ⦃a⦄ (ha : a ∈ s) : Ioi a ⊆ s :=
  Ioi_subset_Ici_self.trans <| h.Ici_subset ha

theorem IsLowerSet.Iio_subset (h : IsLowerSet s) ⦃a⦄ (ha : a ∈ s) : Iio a ⊆ s :=
  h.toDual.Ioi_subset ha

theorem IsUpperSet.ordConnected (h : IsUpperSet s) : s.OrdConnected :=
  ⟨fun _ ha _ _ => Icc_subset_Ici_self.trans <| h.Ici_subset ha⟩

theorem IsLowerSet.ordConnected (h : IsLowerSet s) : s.OrdConnected :=
  ⟨fun _ _ _ hb => Icc_subset_Iic_self.trans <| h.Iic_subset hb⟩

theorem IsUpperSet.preimage (hs : IsUpperSet s) {f : β → α} (hf : Monotone f) :
    IsUpperSet (f ⁻¹' s : Set β) := fun _ _ h => hs <| hf h

theorem IsLowerSet.preimage (hs : IsLowerSet s) {f : β → α} (hf : Monotone f) :
    IsLowerSet (f ⁻¹' s : Set β) := fun _ _ h => hs <| hf h

theorem IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : IsUpperSet (f '' s : Set β) := by
  change IsUpperSet ((f : α ≃ β) '' s)
  rw [Set.image_equiv_eq_preimage_symm]
  exact hs.preimage f.symm.monotone

theorem IsLowerSet.image (hs : IsLowerSet s) (f : α ≃o β) : IsLowerSet (f '' s : Set β) := by
  change IsLowerSet ((f : α ≃ β) '' s)
  rw [Set.image_equiv_eq_preimage_symm]
  exact hs.preimage f.symm.monotone

theorem OrderEmbedding.image_Ici (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) :
    e '' Ici a = Ici (e a) := by
  rw [← e.preimage_Ici, image_preimage_eq_inter_range,
    inter_eq_left.2 <| he.Ici_subset (mem_range_self _)]

theorem OrderEmbedding.image_Iic (e : α ↪o β) (he : IsLowerSet (range e)) (a : α) :
    e '' Iic a = Iic (e a) :=
  e.dual.image_Ici he a

theorem OrderEmbedding.image_Ioi (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) :
    e '' Ioi a = Ioi (e a) := by
  rw [← e.preimage_Ioi, image_preimage_eq_inter_range,
    inter_eq_left.2 <| he.Ioi_subset (mem_range_self _)]

theorem OrderEmbedding.image_Iio (e : α ↪o β) (he : IsLowerSet (range e)) (a : α) :
    e '' Iio a = Iio (e a) :=
  e.dual.image_Ioi he a

@[simp]
theorem Set.monotone_mem : Monotone (· ∈ s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
theorem Set.antitone_mem : Antitone (· ∈ s) ↔ IsLowerSet s :=
  forall_swap

@[simp]
theorem isUpperSet_setOf : IsUpperSet { a | p a } ↔ Monotone p :=
  Iff.rfl

@[simp]
theorem isLowerSet_setOf : IsLowerSet { a | p a } ↔ Antitone p :=
  forall_swap

lemma IsUpperSet.upperBounds_subset (hs : IsUpperSet s) : s.Nonempty → upperBounds s ⊆ s :=
  fun ⟨_a, ha⟩ _b hb ↦ hs (hb ha) ha

lemma IsLowerSet.lowerBounds_subset (hs : IsLowerSet s) : s.Nonempty → lowerBounds s ⊆ s :=
  fun ⟨_a, ha⟩ _b hb ↦ hs (hb ha) ha

section OrderTop

variable [OrderTop α]

theorem IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun _ => hs le_top h, fun h => h.symm ▸ mem_univ _⟩

theorem IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_a, ha⟩ => hs le_top ha⟩

theorem IsUpperSet.top_notMem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.not.trans not_nonempty_iff_eq_empty

@[deprecated (since := "2025-05-24")]
alias IsUpperSet.not_top_mem := IsUpperSet.top_notMem

end OrderTop

section OrderBot

variable [OrderBot α]

theorem IsUpperSet.bot_mem (hs : IsUpperSet s) : ⊥ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun _ => hs bot_le h, fun h => h.symm ▸ mem_univ _⟩

theorem IsLowerSet.bot_mem (hs : IsLowerSet s) : ⊥ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_a, ha⟩ => hs bot_le ha⟩

theorem IsLowerSet.bot_notMem (hs : IsLowerSet s) : ⊥ ∉ s ↔ s = ∅ :=
  hs.bot_mem.not.trans not_nonempty_iff_eq_empty

@[deprecated (since := "2025-05-24")]
alias IsLowerSet.not_bot_mem := IsLowerSet.bot_notMem

end OrderBot

section NoMaxOrder

variable [NoMaxOrder α]

theorem IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s.Nonempty → ¬BddAbove s := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_ge (hb <| hs ((hb ha).trans hc.le) ha)

theorem not_bddAbove_Ici : ¬BddAbove (Ici a) :=
  (isUpperSet_Ici _).not_bddAbove nonempty_Ici

theorem not_bddAbove_Ioi : ¬BddAbove (Ioi a) :=
  (isUpperSet_Ioi _).not_bddAbove nonempty_Ioi

end NoMaxOrder

section NoMinOrder

variable [NoMinOrder α]

theorem IsLowerSet.not_bddBelow (hs : IsLowerSet s) : s.Nonempty → ¬BddBelow s := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_lt b
  exact hc.not_ge (hb <| hs (hc.le.trans <| hb ha) ha)

theorem not_bddBelow_Iic : ¬BddBelow (Iic a) :=
  (isLowerSet_Iic _).not_bddBelow nonempty_Iic

theorem not_bddBelow_Iio : ¬BddBelow (Iio a) :=
  (isLowerSet_Iio _).not_bddBelow nonempty_Iio

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α}

theorem isUpperSet_iff_forall_lt : IsUpperSet s ↔ ∀ ⦃a b : α⦄, a < b → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]

theorem isLowerSet_iff_forall_lt : IsLowerSet s ↔ ∀ ⦃a b : α⦄, b < a → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]

theorem isUpperSet_iff_Ioi_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ioi a ⊆ s := by
  simp [isUpperSet_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]

theorem isLowerSet_iff_Iio_subset : IsLowerSet s ↔ ∀ ⦃a⦄, a ∈ s → Iio a ⊆ s := by
  simp [isLowerSet_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s t : Set α}

theorem IsUpperSet.total (hs : IsUpperSet s) (ht : IsUpperSet t) : s ⊆ t ∨ t ⊆ s := by
  by_contra! h
  simp_rw [Set.not_subset] at h
  obtain ⟨⟨a, has, hat⟩, b, hbt, hbs⟩ := h
  obtain hab | hba := le_total a b
  · exact hbs (hs hab has)
  · exact hat (ht hba hbt)

theorem IsLowerSet.total (hs : IsLowerSet s) (ht : IsLowerSet t) : s ⊆ t ∨ t ⊆ s :=
  hs.toDual.total ht.toDual

theorem IsUpperSet.eq_empty_or_Ici [WellFoundedLT α] (h : IsUpperSet s) :
    s = ∅ ∨ (∃ a, s = Set.Ici a) := by
  refine or_iff_not_imp_left.2 fun ha ↦ ?_
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 ha
  exact ⟨_, Set.ext fun b ↦ ⟨wellFounded_lt.min_le, (h · <| wellFounded_lt.min_mem _ ⟨a, ha⟩)⟩⟩

theorem IsLowerSet.eq_empty_or_Iic [WellFoundedGT α] (h : IsLowerSet s) :
    s = ∅ ∨ (∃ a, s = Set.Iic a) :=
  IsUpperSet.eq_empty_or_Ici (α := αᵒᵈ) h

theorem IsLowerSet.eq_univ_or_Iio [WellFoundedLT α] (h : IsLowerSet s) :
    s = .univ ∨ (∃ a, s = Set.Iio a) := by
  simp_rw [← @compl_inj_iff _ s]
  simpa using h.compl.eq_empty_or_Ici

theorem IsUpperSet.eq_univ_or_Ioi [WellFoundedGT α] (h : IsUpperSet s) :
    s = .univ ∨ (∃ a, s = Set.Ioi a) :=
  IsLowerSet.eq_univ_or_Iio (α := αᵒᵈ) h

end LinearOrder
