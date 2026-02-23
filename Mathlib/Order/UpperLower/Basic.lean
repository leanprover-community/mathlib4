/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.OrderEmbedding
public import Mathlib.Order.SetNotation
public import Mathlib.Order.WellFounded

/-!
# Properties of unbundled upper/lower sets

This file proves results on `IsUpperSet` and `IsLowerSet`, including their interactions with
set operations, images, preimages and order duals, and properties that reflect stronger assumptions
on the underlying order (such as `PartialOrder` and `LinearOrder`).

## TODO

* Lattice structure on antichains.
* Order equivalence between upper/lower sets and antichains.
-/

public section

open OrderDual Set

variable {α β : Type*} {ι : Sort*} {κ : ι → Sort*}

attribute [aesop norm unfold] IsUpperSet IsLowerSet

section LE

variable [LE α] {s t : Set α} {a : α}

@[to_dual]
theorem isUpperSet_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id

@[to_dual]
theorem isUpperSet_univ : IsUpperSet (univ : Set α) := fun _ _ _ => id

@[to_dual]
theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ := fun _a _b h hb ha => hb <| hs h ha

@[to_dual (attr := simp)]
theorem isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s :=
  ⟨fun h => by
    convert h.compl
    rw [compl_compl], IsLowerSet.compl⟩

@[to_dual]
theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∪ t) :=
  fun _ _ h => Or.imp (hs h) (ht h)

@[to_dual]
theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∩ t) :=
  fun _ _ h => And.imp (hs h) (ht h)

@[to_dual]
theorem isUpperSet_sUnion {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋃₀ S) :=
  fun _ _ h => Exists.imp fun _ hs => ⟨hs.1, hf _ hs.1 h hs.2⟩

@[to_dual]
theorem isUpperSet_iUnion {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) :=
  isUpperSet_sUnion <| forall_mem_range.2 hf

@[to_dual]
theorem isUpperSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋃ (i) (j), f i j) :=
  isUpperSet_iUnion fun i => isUpperSet_iUnion <| hf i

@[to_dual]
theorem isUpperSet_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋂₀ S) :=
  fun _ _ h => forall₂_imp fun s hs => hf s hs h

@[to_dual]
theorem isUpperSet_iInter {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) :=
  isUpperSet_sInter <| forall_mem_range.2 hf

@[to_dual]
theorem isUpperSet_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋂ (i) (j), f i j) :=
  isUpperSet_iInter fun i => isUpperSet_iInter <| hf i

@[to_dual (attr := simp)]
theorem isUpperSet_preimage_ofDual_iff : IsUpperSet (ofDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem isUpperSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsUpperSet (toDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[to_dual] alias ⟨_, IsUpperSet.toDual⟩ := isLowerSet_preimage_ofDual_iff
@[to_dual] alias ⟨_, IsUpperSet.ofDual⟩ := isLowerSet_preimage_toDual_iff

@[to_dual]
lemma IsUpperSet.isLowerSet_preimage_coe (hs : IsUpperSet s) :
    IsLowerSet ((↑) ⁻¹' t : Set s) ↔ ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t := by aesop

@[to_dual]
lemma IsUpperSet.sdiff (hs : IsUpperSet s) (ht : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    IsUpperSet (s \ t) :=
  fun _b _c hbc hb ↦ ⟨hs hbc hb.1, fun hc ↦ hb.2 <| ht _ hb.1 _ hc hbc⟩

@[to_dual]
lemma IsUpperSet.sdiff_of_isLowerSet (hs : IsUpperSet s) (ht : IsLowerSet t) : IsUpperSet (s \ t) :=
  hs.sdiff <| by aesop

@[to_dual]
lemma IsUpperSet.erase (hs : IsUpperSet s) (has : ∀ b ∈ s, b ≤ a → b = a) : IsUpperSet (s \ {a}) :=
  hs.sdiff <| by simpa using has

end LE

section Preorder

variable [Preorder α] [Preorder β] {s : Set α} {p : α → Prop} (a : α)

@[to_dual] theorem isUpperSet_Ici : IsUpperSet (Ici a) := fun _ _ => ge_trans
@[to_dual] theorem isUpperSet_Ioi : IsUpperSet (Ioi a) := fun _ _ => flip lt_of_lt_of_le

@[to_dual]
theorem isUpperSet_iff_Ici_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ici a ⊆ s := by
  simp [IsUpperSet, subset_def, @forall_swap (_ ∈ s)]

@[to_dual] alias ⟨IsUpperSet.Ici_subset, _⟩ := isUpperSet_iff_Ici_subset

@[to_dual]
theorem IsUpperSet.Ioi_subset (h : IsUpperSet s) ⦃a⦄ (ha : a ∈ s) : Ioi a ⊆ s :=
  Ioi_subset_Ici_self.trans <| h.Ici_subset ha

theorem IsUpperSet.ordConnected (h : IsUpperSet s) : s.OrdConnected :=
  ⟨fun _ ha _ _ => Icc_subset_Ici_self.trans <| h.Ici_subset ha⟩

-- `to_dual` cannot yet reorder arguments of arguments
@[to_dual existing]
theorem IsLowerSet.ordConnected (h : IsLowerSet s) : s.OrdConnected :=
  ⟨fun _ _ _ hb => Icc_subset_Iic_self.trans <| h.Iic_subset hb⟩

theorem IsUpperSet.preimage (hs : IsUpperSet s) {f : β → α} (hf : Monotone f) :
    IsUpperSet (f ⁻¹' s : Set β) := fun _ _ h => hs <| hf h

-- `to_dual` cannot yet reorder arguments of arguments
@[to_dual existing]
theorem IsLowerSet.preimage (hs : IsLowerSet s) {f : β → α} (hf : Monotone f) :
    IsLowerSet (f ⁻¹' s : Set β) := fun _ _ h => hs <| hf h

@[to_dual]
theorem IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : IsUpperSet (f '' s : Set β) := by
  change IsUpperSet ((f : α ≃ β) '' s)
  rw [Equiv.image_eq_preimage_symm]
  exact hs.preimage f.symm.monotone

@[to_dual]
theorem OrderEmbedding.image_Ici (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) :
    e '' Ici a = Ici (e a) := by
  rw [← e.preimage_Ici, image_preimage_eq_inter_range,
    inter_eq_left.2 <| he.Ici_subset (mem_range_self _)]

@[to_dual]
theorem OrderEmbedding.image_Ioi (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) :
    e '' Ioi a = Ioi (e a) := by
  rw [← e.preimage_Ioi, image_preimage_eq_inter_range,
    inter_eq_left.2 <| he.Ioi_subset (mem_range_self _)]

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

@[to_dual]
lemma IsUpperSet.upperBounds_subset (hs : IsUpperSet s) : s.Nonempty → upperBounds s ⊆ s :=
  fun ⟨_a, ha⟩ _b hb ↦ hs (hb ha) ha

section OrderTop

variable [OrderTop α]

@[to_dual]
theorem IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun _ => hs le_top h, fun h => h.symm ▸ mem_univ _⟩

@[to_dual]
theorem IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_a, ha⟩ => hs le_top ha⟩

@[to_dual]
theorem IsUpperSet.top_notMem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.not.trans not_nonempty_iff_eq_empty

end OrderTop

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
theorem IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s.Nonempty → ¬BddAbove s := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_ge (hb <| hs ((hb ha).trans hc.le) ha)

@[to_dual]
theorem not_bddAbove_Ici : ¬BddAbove (Ici a) :=
  (isUpperSet_Ici _).not_bddAbove nonempty_Ici

@[to_dual]
theorem not_bddAbove_Ioi : ¬BddAbove (Ioi a) :=
  (isUpperSet_Ioi _).not_bddAbove nonempty_Ioi

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α}

@[to_dual]
theorem isUpperSet_iff_forall_lt : IsUpperSet s ↔ ∀ ⦃a b : α⦄, a < b → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]

@[to_dual]
theorem isUpperSet_iff_Ioi_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ioi a ⊆ s := by
  simp [isUpperSet_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s t : Set α}

@[to_dual]
theorem IsUpperSet.total (hs : IsUpperSet s) (ht : IsUpperSet t) : s ⊆ t ∨ t ⊆ s := by
  by_contra! h
  simp_rw [Set.not_subset] at h
  obtain ⟨⟨a, has, hat⟩, b, hbt, hbs⟩ := h
  obtain hab | hba := le_total a b
  · exact hbs (hs hab has)
  · exact hat (ht hba hbt)

@[to_dual]
theorem IsUpperSet.eq_empty_or_Ici [WellFoundedLT α] (h : IsUpperSet s) :
    s = ∅ ∨ ∃ a, s = Ici a := by
  refine or_iff_not_imp_left.2 fun ha ↦ ?_
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 ha
  exact ⟨_, ext fun b ↦ ⟨wellFounded_lt.min_le, (h · <| wellFounded_lt.min_mem _ ⟨a, ha⟩)⟩⟩

@[to_dual]
theorem IsLowerSet.eq_univ_or_Iio [WellFoundedLT α] (h : IsLowerSet s) :
    s = univ ∨ ∃ a, s = Iio a := by
  simp_rw [← @compl_inj_iff _ s]
  simpa using h.compl.eq_empty_or_Ici

end LinearOrder
