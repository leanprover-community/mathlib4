/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Data.Set.Lattice

/-!
# Up-sets and down-sets

This file defines upper and lower sets in an order.

## Main declarations

* `IsUpperSet`: Predicate for a set to be an upper set. This means every element greater than a
  member of the set is in the set itself.
* `IsLowerSet`: Predicate for a set to be a lower set. This means every element less than a member
  of the set is in the set itself.
* `UpperSet`: The type of upper sets.
* `LowerSet`: The type of lower sets.
* `upperClosure`: The greatest upper set containing a set.
* `lowerClosure`: The least lower set containing a set.
* `UpperSet.Ici`: Principal upper set. `Set.Ici` as an upper set.
* `UpperSet.Ioi`: Strict principal upper set. `Set.Ioi` as an upper set.
* `LowerSet.Iic`: Principal lower set. `Set.Iic` as a lower set.
* `LowerSet.Iio`: Strict principal lower set. `Set.Iio` as a lower set.

## Notation

* `×ˢ` is notation for `UpperSet.prod` / `LowerSet.prod`.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `Filter`.

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-! ### Unbundled upper/lower sets -/


section LE

variable [LE α] {s t : Set α} {a : α}

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
@[aesop norm unfold]
def IsUpperSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
@[aesop norm unfold]
def IsLowerSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s

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

theorem IsUpperSet.not_top_mem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.not.trans not_nonempty_iff_eq_empty

end OrderTop

section OrderBot

variable [OrderBot α]

theorem IsUpperSet.bot_mem (hs : IsUpperSet s) : ⊥ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun _ => hs bot_le h, fun h => h.symm ▸ mem_univ _⟩

theorem IsLowerSet.bot_mem (hs : IsLowerSet s) : ⊥ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_a, ha⟩ => hs bot_le ha⟩

theorem IsLowerSet.not_bot_mem (hs : IsLowerSet s) : ⊥ ∉ s ↔ s = ∅ :=
  hs.bot_mem.not.trans not_nonempty_iff_eq_empty

end OrderBot

section NoMaxOrder

variable [NoMaxOrder α]

theorem IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s.Nonempty → ¬BddAbove s := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_le (hb <| hs ((hb ha).trans hc.le) ha)

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
  exact hc.not_le (hb <| hs (hc.le.trans <| hb ha) ha)

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

/-! ### Upper/lower sets and Fibrations -/

namespace Relation

variable {f : α → β} {s : Set α}

lemma Fibration.isLowerSet_image [LE α] [LE β] (hf : Fibration (· ≤ ·) (· ≤ ·) f)
    {s : Set α} (hs : IsLowerSet s) : IsLowerSet (f '' s) := by
  rintro _ y' e ⟨x, hx, rfl⟩; obtain ⟨y, e', rfl⟩ := hf e; exact ⟨_, hs e' hx, rfl⟩

alias _root_.IsLowerSet.image_fibration := Fibration.isLowerSet_image

lemma fibration_iff_isLowerSet_image_Iic [Preorder α] [LE β] :
    Fibration (· ≤ ·) (· ≤ ·) f ↔ ∀ x, IsLowerSet (f '' Iic x) :=
  ⟨fun h x ↦ (isLowerSet_Iic x).image_fibration h, fun H x _ e ↦ H x e ⟨x, le_rfl, rfl⟩⟩

lemma fibration_iff_isLowerSet_image [Preorder α] [LE β] :
    Fibration (· ≤ ·) (· ≤ ·) f ↔ ∀ s, IsLowerSet s → IsLowerSet (f '' s) :=
  ⟨Fibration.isLowerSet_image,
    fun H ↦ fibration_iff_isLowerSet_image_Iic.mpr (H _ <| isLowerSet_Iic ·)⟩

lemma fibration_iff_image_Iic [Preorder α] [Preorder β] (hf : Monotone f) :
    Fibration (· ≤ ·) (· ≤ ·) f ↔ ∀ x, f '' Iic x = Iic (f x) :=
  ⟨fun H x ↦ le_antisymm (fun _ ⟨_, hy, e⟩ ↦ e ▸ hf hy)
    ((H.isLowerSet_image (isLowerSet_Iic x)).Iic_subset ⟨x, le_rfl, rfl⟩),
    fun H ↦ fibration_iff_isLowerSet_image_Iic.mpr (fun x ↦ (H x).symm ▸ isLowerSet_Iic (f x))⟩

lemma Fibration.isUpperSet_image [LE α] [LE β] (hf : Fibration (· ≥ ·) (· ≥ ·) f)
    {s : Set α} (hs : IsUpperSet s) : IsUpperSet (f '' s) :=
  @Fibration.isLowerSet_image αᵒᵈ βᵒᵈ _ _ _ hf s hs

alias _root_.IsUpperSet.image_fibration := Fibration.isUpperSet_image

lemma fibration_iff_isUpperSet_image_Ici [Preorder α] [LE β] :
    Fibration (· ≥ ·) (· ≥ ·) f ↔ ∀ x, IsUpperSet (f '' Ici x) :=
  @fibration_iff_isLowerSet_image_Iic αᵒᵈ βᵒᵈ _ _ _

lemma fibration_iff_isUpperSet_image [Preorder α] [LE β] :
    Fibration (· ≥ ·) (· ≥ ·) f ↔ ∀ s, IsUpperSet s → IsUpperSet (f '' s) :=
  @fibration_iff_isLowerSet_image αᵒᵈ βᵒᵈ _ _ _

lemma fibration_iff_image_Ici [Preorder α] [Preorder β] (hf : Monotone f) :
    Fibration (· ≥ ·) (· ≥ ·) f ↔ ∀ x, f '' Ici x = Ici (f x) :=
  fibration_iff_image_Iic hf.dual

end Relation

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

end LinearOrder

/-! ### Bundled upper/lower sets -/


section LE

variable [LE α]

@[inherit_doc IsUpperSet]
structure UpperSet (α : Type*) [LE α] where
  /-- The carrier of an `UpperSet`. -/
  carrier : Set α
  /-- The carrier of an `UpperSet` is an upper set. -/
  upper' : IsUpperSet carrier

extend_docs UpperSet before "The type of upper sets of an order."

@[inherit_doc IsLowerSet]
structure LowerSet (α : Type*) [LE α] where
  /-- The carrier of a `LowerSet`. -/
  carrier : Set α
  /-- The carrier of a `LowerSet` is a lower set. -/
  lower' : IsLowerSet carrier

extend_docs LowerSet before "The type of lower sets of an order."

namespace UpperSet

instance : SetLike (UpperSet α) α where
  coe := UpperSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : UpperSet α) : Set α := s

initialize_simps_projections UpperSet (carrier → coe)

@[ext]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

@[simp]
theorem carrier_eq_coe (s : UpperSet α) : s.carrier = s :=
  rfl

@[simp] protected lemma upper (s : UpperSet α) : IsUpperSet (s : Set α) := s.upper'

@[simp, norm_cast] lemma coe_mk (s : Set α) (hs) : mk s hs = s := rfl
@[simp] lemma mem_mk {s : Set α} (hs) {a : α} : a ∈ mk s hs ↔ a ∈ s := Iff.rfl

end UpperSet

namespace LowerSet

instance : SetLike (LowerSet α) α where
  coe := LowerSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : LowerSet α) : Set α := s

initialize_simps_projections LowerSet (carrier → coe)

@[ext]
theorem ext {s t : LowerSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

@[simp]
theorem carrier_eq_coe (s : LowerSet α) : s.carrier = s :=
  rfl

@[simp] protected lemma lower (s : LowerSet α) : IsLowerSet (s : Set α) := s.lower'

@[simp, norm_cast] lemma coe_mk (s : Set α) (hs) : mk s hs = s := rfl
@[simp] lemma mem_mk {s : Set α} (hs) {a : α} : a ∈ mk s hs ↔ a ∈ s := Iff.rfl

end LowerSet

/-! #### Order -/

namespace UpperSet

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

instance : Sup (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

instance : Inf (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

instance : Top (UpperSet α) :=
  ⟨⟨∅, isUpperSet_empty⟩⟩

instance : Bot (UpperSet α) :=
  ⟨⟨univ, isUpperSet_univ⟩⟩

instance : SupSet (UpperSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isUpperSet_iInter₂ fun s _ => s.upper⟩⟩

instance : InfSet (UpperSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isUpperSet_iUnion₂ fun s _ => s.upper⟩⟩

instance completeLattice : CompleteLattice (UpperSet α) :=
  (toDual.injective.comp SetLike.coe_injective).completeLattice _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance completelyDistribLattice : CompletelyDistribLattice (UpperSet α) :=
  .ofMinimalAxioms <|
    (toDual.injective.comp SetLike.coe_injective).completelyDistribLatticeMinimalAxioms .of _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[simp 1100, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ t ≤ s :=
  Iff.rfl

@[simp 1100, norm_cast] lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ t < s := Iff.rfl

@[simp, norm_cast]
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊥ := by simp [SetLike.ext'_iff]

@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤ := by simp [SetLike.ext'_iff]

@[simp, norm_cast] lemma coe_nonempty : (s : Set α).Nonempty ↔ s ≠ ⊤ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]
theorem coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = (s : Set α) ∩ t :=
  rfl

@[simp, norm_cast]
theorem coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = (s : Set α) ∪ t :=
  rfl

@[simp, norm_cast]
theorem coe_sSup (S : Set (UpperSet α)) : (↑(sSup S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp, norm_cast]
theorem coe_sInf (S : Set (UpperSet α)) : (↑(sInf S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl

@[simp, norm_cast]
theorem coe_iSup (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by simp [iSup]

@[simp, norm_cast]
theorem coe_iInf (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [iInf]

@[norm_cast] -- Porting note: no longer a `simp`
theorem coe_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by simp_rw [coe_iSup]

@[norm_cast] -- Porting note: no longer a `simp`
theorem coe_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by simp_rw [coe_iInf]

@[simp]
theorem not_mem_top : a ∉ (⊤ : UpperSet α) :=
  id

@[simp]
theorem mem_bot : a ∈ (⊥ : UpperSet α) :=
  trivial

@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_sSup_iff : a ∈ sSup S ↔ ∀ s ∈ S, a ∈ s :=
  mem_iInter₂

@[simp]
theorem mem_sInf_iff : a ∈ sInf S ↔ ∃ s ∈ S, a ∈ s :=
  mem_iUnion₂.trans <| by simp only [exists_prop, SetLike.mem_coe]

@[simp]
theorem mem_iSup_iff {f : ι → UpperSet α} : (a ∈ ⨆ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iSup]
  exact mem_iInter

@[simp]
theorem mem_iInf_iff {f : ι → UpperSet α} : (a ∈ ⨅ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iInf]
  exact mem_iUnion

-- Porting note: no longer a @[simp]
theorem mem_iSup₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_iSup_iff]

-- Porting note: no longer a @[simp]
theorem mem_iInf₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_iInf_iff]

@[simp, norm_cast]
theorem codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]

end UpperSet

namespace LowerSet

variable {S : Set (LowerSet α)} {s t : LowerSet α} {a : α}

instance : Sup (LowerSet α) :=
  ⟨fun s t => ⟨s ∪ t, fun _ _ h => Or.imp (s.lower h) (t.lower h)⟩⟩

instance : Inf (LowerSet α) :=
  ⟨fun s t => ⟨s ∩ t, fun _ _ h => And.imp (s.lower h) (t.lower h)⟩⟩

instance : Top (LowerSet α) :=
  ⟨⟨univ, fun _ _ _ => id⟩⟩

instance : Bot (LowerSet α) :=
  ⟨⟨∅, fun _ _ _ => id⟩⟩

instance : SupSet (LowerSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isLowerSet_iUnion₂ fun s _ => s.lower⟩⟩

instance : InfSet (LowerSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isLowerSet_iInter₂ fun s _ => s.lower⟩⟩

instance completeLattice : CompleteLattice (LowerSet α) :=
  SetLike.coe_injective.completeLattice _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl

instance completelyDistribLattice : CompletelyDistribLattice (LowerSet α) :=
  .ofMinimalAxioms <| SetLike.coe_injective.completelyDistribLatticeMinimalAxioms .of _
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (LowerSet α) :=
  ⟨⊥⟩

@[norm_cast] lemma coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t := Iff.rfl

@[norm_cast] lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t := Iff.rfl

@[simp, norm_cast]
theorem coe_top : ((⊤ : LowerSet α) : Set α) = univ :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : LowerSet α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊤ := by simp [SetLike.ext'_iff]

@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊥ := by simp [SetLike.ext'_iff]

@[simp, norm_cast] lemma coe_nonempty : (s : Set α).Nonempty ↔ s ≠ ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]
theorem coe_sup (s t : LowerSet α) : (↑(s ⊔ t) : Set α) = (s : Set α) ∪ t :=
  rfl

@[simp, norm_cast]
theorem coe_inf (s t : LowerSet α) : (↑(s ⊓ t) : Set α) = (s : Set α) ∩ t :=
  rfl

@[simp, norm_cast]
theorem coe_sSup (S : Set (LowerSet α)) : (↑(sSup S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl

@[simp, norm_cast]
theorem coe_sInf (S : Set (LowerSet α)) : (↑(sInf S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp, norm_cast]
theorem coe_iSup (f : ι → LowerSet α) : (↑(⨆ i, f i) : Set α) = ⋃ i, f i := by
  simp_rw [iSup, coe_sSup, mem_range, iUnion_exists, iUnion_iUnion_eq']

@[simp, norm_cast]
theorem coe_iInf (f : ι → LowerSet α) : (↑(⨅ i, f i) : Set α) = ⋂ i, f i := by
  simp_rw [iInf, coe_sInf, mem_range, iInter_exists, iInter_iInter_eq']

@[norm_cast] -- Porting note: no longer a `simp`
theorem coe_iSup₂ (f : ∀ i, κ i → LowerSet α) :
    (↑(⨆ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by simp_rw [coe_iSup]

@[norm_cast] -- Porting note: no longer a `simp`
theorem coe_iInf₂ (f : ∀ i, κ i → LowerSet α) :
    (↑(⨅ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by simp_rw [coe_iInf]

@[simp]
theorem mem_top : a ∈ (⊤ : LowerSet α) :=
  trivial

@[simp]
theorem not_mem_bot : a ∉ (⊥ : LowerSet α) :=
  id

@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_sSup_iff : a ∈ sSup S ↔ ∃ s ∈ S, a ∈ s :=
  mem_iUnion₂.trans <| by simp only [exists_prop, SetLike.mem_coe]

@[simp]
theorem mem_sInf_iff : a ∈ sInf S ↔ ∀ s ∈ S, a ∈ s :=
  mem_iInter₂

@[simp]
theorem mem_iSup_iff {f : ι → LowerSet α} : (a ∈ ⨆ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iSup]
  exact mem_iUnion

@[simp]
theorem mem_iInf_iff {f : ι → LowerSet α} : (a ∈ ⨅ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iInf]
  exact mem_iInter

-- Porting note: no longer a @[simp]
theorem mem_iSup₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_iSup_iff]

-- Porting note: no longer a @[simp]
theorem mem_iInf₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_iInf_iff]

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, SetLike.ext'_iff]

end LowerSet

/-! #### Complement -/

/-- The complement of a lower set as an upper set. -/
def UpperSet.compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩

/-- The complement of a lower set as an upper set. -/
def LowerSet.compl (s : LowerSet α) : UpperSet α :=
  ⟨sᶜ, s.lower.compl⟩

namespace UpperSet

variable {s t : UpperSet α} {a : α}

@[simp]
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = (↑s)ᶜ :=
  rfl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl

@[simp]
nonrec theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
  UpperSet.ext <| compl_compl _

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl

@[simp]
protected theorem compl_sup (s t : UpperSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  LowerSet.ext compl_inf

@[simp]
protected theorem compl_inf (s t : UpperSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  LowerSet.ext compl_sup

@[simp]
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty

@[simp]
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ

@[simp]
protected theorem compl_sSup (S : Set (UpperSet α)) : (sSup S).compl = ⨆ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_sSup, compl_iInter₂, LowerSet.coe_iSup₂]

@[simp]
protected theorem compl_sInf (S : Set (UpperSet α)) : (sInf S).compl = ⨅ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_sInf, compl_iUnion₂, LowerSet.coe_iInf₂]

@[simp]
protected theorem compl_iSup (f : ι → UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_iSup, compl_iInter, LowerSet.coe_iSup]

@[simp]
protected theorem compl_iInf (f : ι → UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_iInf, compl_iUnion, LowerSet.coe_iInf]

-- Porting note: no longer a @[simp]
theorem compl_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [UpperSet.compl_iSup]

-- Porting note: no longer a @[simp]
theorem compl_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [UpperSet.compl_iInf]

end UpperSet

namespace LowerSet

variable {s t : LowerSet α} {a : α}

@[simp]
theorem coe_compl (s : LowerSet α) : (s.compl : Set α) = (↑s)ᶜ :=
  rfl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl

@[simp]
nonrec theorem compl_compl (s : LowerSet α) : s.compl.compl = s :=
  LowerSet.ext <| compl_compl _

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl

protected theorem compl_sup (s t : LowerSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  UpperSet.ext compl_sup

protected theorem compl_inf (s t : LowerSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  UpperSet.ext compl_inf

protected theorem compl_top : (⊤ : LowerSet α).compl = ⊤ :=
  UpperSet.ext compl_univ

protected theorem compl_bot : (⊥ : LowerSet α).compl = ⊥ :=
  UpperSet.ext compl_empty

protected theorem compl_sSup (S : Set (LowerSet α)) : (sSup S).compl = ⨆ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_sSup, compl_iUnion₂, UpperSet.coe_iSup₂]

protected theorem compl_sInf (S : Set (LowerSet α)) : (sInf S).compl = ⨅ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_sInf, compl_iInter₂, UpperSet.coe_iInf₂]

protected theorem compl_iSup (f : ι → LowerSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_iSup, compl_iUnion, UpperSet.coe_iSup]

protected theorem compl_iInf (f : ι → LowerSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_iInf, compl_iInter, UpperSet.coe_iInf]

@[simp]
theorem compl_iSup₂ (f : ∀ i, κ i → LowerSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_iSup]

@[simp]
theorem compl_iInf₂ (f : ∀ i, κ i → LowerSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_iInf]

end LowerSet

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
def upperSetIsoLowerSet : UpperSet α ≃o LowerSet α where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := UpperSet.compl_le_compl

end LE

section LinearOrder
variable [LinearOrder α]

instance UpperSet.isTotal_le : IsTotal (UpperSet α) (· ≤ ·) := ⟨fun s t => t.upper.total s.upper⟩

instance LowerSet.isTotal_le : IsTotal (LowerSet α) (· ≤ ·) := ⟨fun s t => s.lower.total t.lower⟩

noncomputable instance UpperSet.instLinearOrder : LinearOrder (UpperSet α) := by
  classical exact Lattice.toLinearOrder _

noncomputable instance LowerSet.instLinearOrder : LinearOrder (LowerSet α) := by
  classical exact Lattice.toLinearOrder _

noncomputable instance UpperSet.instCompleteLinearOrder : CompleteLinearOrder (UpperSet α) :=
  { completelyDistribLattice, instLinearOrder with }

noncomputable instance LowerSet.instCompleteLinearOrder : CompleteLinearOrder (LowerSet α) :=
  { completelyDistribLattice, instLinearOrder with }

end LinearOrder

/-! #### Map -/


section

variable [Preorder α] [Preorder β] [Preorder γ]

namespace UpperSet

variable {f : α ≃o β} {s t : UpperSet α} {a : α} {b : β}

/-- An order isomorphism of Preorders induces an order isomorphism of their upper sets. -/
def map (f : α ≃o β) : UpperSet α ≃o UpperSet β where
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩
  left_inv _ := ext <| f.preimage_image _
  right_inv _ := ext <| f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  DFunLike.ext _ _ fun s => ext <| by convert Set.preimage_equiv_eq_image_symm s f.toEquiv

@[simp]
theorem mem_map : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl

@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp

@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp

variable (f s t)

@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl

end UpperSet

namespace LowerSet

variable {f : α ≃o β} {s t : LowerSet α} {a : α}

/-- An order isomorphism of Preorders induces an order isomorphism of their lower sets. -/
def map (f : α ≃o β) : LowerSet α ≃o LowerSet β where
  toFun s := ⟨f '' s, s.lower.image f⟩
  invFun t := ⟨f ⁻¹' t, t.lower.preimage f.monotone⟩
  left_inv _ := SetLike.coe_injective <| f.preimage_image _
  right_inv _ := SetLike.coe_injective <| f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  DFunLike.ext _ _ fun s => ext <| by convert Set.preimage_equiv_eq_image_symm s f.toEquiv

@[simp]
theorem mem_map {f : α ≃o β} {b : β} : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl

@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp

@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp

variable (f s t)

@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl

end LowerSet

namespace UpperSet

@[simp]
theorem compl_map (f : α ≃o β) (s : UpperSet α) : (map f s).compl = LowerSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.bijective).symm

end UpperSet

namespace LowerSet

@[simp]
theorem compl_map (f : α ≃o β) (s : LowerSet α) : (map f s).compl = UpperSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.bijective).symm

end LowerSet

end

/-! #### Principal sets -/


namespace UpperSet

section Preorder

variable [Preorder α] [Preorder β] {s : UpperSet α} {a b : α}

/-- The smallest upper set containing a given element. -/
nonrec def Ici (a : α) : UpperSet α :=
  ⟨Ici a, isUpperSet_Ici a⟩

/-- The smallest upper set containing a given element. -/
nonrec def Ioi (a : α) : UpperSet α :=
  ⟨Ioi a, isUpperSet_Ioi a⟩

@[simp]
theorem coe_Ici (a : α) : ↑(Ici a) = Set.Ici a :=
  rfl

@[simp]
theorem coe_Ioi (a : α) : ↑(Ioi a) = Set.Ioi a :=
  rfl

@[simp]
theorem mem_Ici_iff : b ∈ Ici a ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem mem_Ioi_iff : b ∈ Ioi a ↔ a < b :=
  Iff.rfl

@[simp]
theorem map_Ici (f : α ≃o β) (a : α) : map f (Ici a) = Ici (f a) := by
  ext
  simp

@[simp]
theorem map_Ioi (f : α ≃o β) (a : α) : map f (Ioi a) = Ioi (f a) := by
  ext
  simp

theorem Ici_le_Ioi (a : α) : Ici a ≤ Ioi a :=
  Ioi_subset_Ici_self

@[simp]
nonrec theorem Ici_bot [OrderBot α] : Ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot

@[simp]
nonrec theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top

@[simp] lemma Ici_ne_top : Ici a ≠ ⊤ := SetLike.coe_ne_coe.1 nonempty_Ici.ne_empty
@[simp] lemma Ici_lt_top : Ici a < ⊤ := lt_top_iff_ne_top.2 Ici_ne_top
@[simp] lemma le_Ici : s ≤ Ici a ↔ a ∈ s := ⟨fun h ↦ h le_rfl, fun ha ↦ s.upper.Ici_subset ha⟩

end Preorder

section PartialOrder
variable [PartialOrder α] {a b : α}

nonrec lemma Ici_injective : Injective (Ici : α → UpperSet α) := fun _a _b hab ↦
  Ici_injective <| congr_arg ((↑) : _ → Set α) hab

@[simp] lemma Ici_inj : Ici a = Ici b ↔ a = b := Ici_injective.eq_iff

lemma Ici_ne_Ici : Ici a ≠ Ici b ↔ a ≠ b := Ici_inj.not

end PartialOrder

@[simp]
theorem Ici_sup [SemilatticeSup α] (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b :=
  ext Ici_inter_Ici.symm

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Ici_sSup (S : Set α) : Ici (sSup S) = ⨆ a ∈ S, Ici a :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, sSup_le_iff]

@[simp]
theorem Ici_iSup (f : ι → α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i) :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, iSup_le_iff]

-- Porting note: no longer a @[simp]
theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⨆ (i) (j), Ici (f i j) := by
  simp_rw [Ici_iSup]

end CompleteLattice

end UpperSet

namespace LowerSet

section Preorder

variable [Preorder α] [Preorder β] {s : LowerSet α} {a b : α}

/-- Principal lower set. `Set.Iic` as a lower set. The smallest lower set containing a given
element. -/
nonrec def Iic (a : α) : LowerSet α :=
  ⟨Iic a, isLowerSet_Iic a⟩

/-- Strict principal lower set. `Set.Iio` as a lower set. -/
nonrec def Iio (a : α) : LowerSet α :=
  ⟨Iio a, isLowerSet_Iio a⟩

@[simp]
theorem coe_Iic (a : α) : ↑(Iic a) = Set.Iic a :=
  rfl

@[simp]
theorem coe_Iio (a : α) : ↑(Iio a) = Set.Iio a :=
  rfl

@[simp]
theorem mem_Iic_iff : b ∈ Iic a ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem mem_Iio_iff : b ∈ Iio a ↔ b < a :=
  Iff.rfl

@[simp]
theorem map_Iic (f : α ≃o β) (a : α) : map f (Iic a) = Iic (f a) := by
  ext
  simp

@[simp]
theorem map_Iio (f : α ≃o β) (a : α) : map f (Iio a) = Iio (f a) := by
  ext
  simp

theorem Ioi_le_Ici (a : α) : Ioi a ≤ Ici a :=
  Ioi_subset_Ici_self

@[simp]
nonrec theorem Iic_top [OrderTop α] : Iic (⊤ : α) = ⊤ :=
  SetLike.coe_injective Iic_top

@[simp]
nonrec theorem Iio_bot [OrderBot α] : Iio (⊥ : α) = ⊥ :=
  SetLike.coe_injective Iio_bot

@[simp] lemma Iic_ne_bot : Iic a ≠ ⊥ := SetLike.coe_ne_coe.1 nonempty_Iic.ne_empty
@[simp] lemma bot_lt_Iic : ⊥ < Iic a := bot_lt_iff_ne_bot.2 Iic_ne_bot
@[simp] lemma Iic_le : Iic a ≤ s ↔ a ∈ s := ⟨fun h ↦ h le_rfl, fun ha ↦ s.lower.Iic_subset ha⟩

end Preorder

section PartialOrder
variable [PartialOrder α] {a b : α}

nonrec lemma Iic_injective : Injective (Iic : α → LowerSet α) := fun _a _b hab ↦
  Iic_injective <| congr_arg ((↑) : _ → Set α) hab

@[simp] lemma Iic_inj : Iic a = Iic b ↔ a = b := Iic_injective.eq_iff

lemma Iic_ne_Iic : Iic a ≠ Iic b ↔ a ≠ b := Iic_inj.not

end PartialOrder

@[simp]
theorem Iic_inf [SemilatticeInf α] (a b : α) : Iic (a ⊓ b) = Iic a ⊓ Iic b :=
  SetLike.coe_injective Iic_inter_Iic.symm

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Iic_sInf (S : Set α) : Iic (sInf S) = ⨅ a ∈ S, Iic a :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_iInf₂_iff, le_sInf_iff]

@[simp]
theorem Iic_iInf (f : ι → α) : Iic (⨅ i, f i) = ⨅ i, Iic (f i) :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_iInf_iff, le_iInf_iff]

-- Porting note: no longer a @[simp]
theorem Iic_iInf₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⨅ (i) (j), Iic (f i j) := by
  simp_rw [Iic_iInf]

end CompleteLattice

end LowerSet

section closure

variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

/-- The greatest upper set containing a given set. -/
def upperClosure (s : Set α) : UpperSet α :=
  ⟨{ x | ∃ a ∈ s, a ≤ x }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hx.2.trans hle⟩⟩

/-- The least lower set containing a given set. -/
def lowerClosure (s : Set α) : LowerSet α :=
  ⟨{ x | ∃ a ∈ s, x ≤ a }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hle.trans hx.2⟩⟩

-- Porting note (#11215): TODO: move `GaloisInsertion`s up, use them to prove lemmas

@[simp]
theorem mem_upperClosure : x ∈ upperClosure s ↔ ∃ a ∈ s, a ≤ x :=
  Iff.rfl

@[simp]
theorem mem_lowerClosure : x ∈ lowerClosure s ↔ ∃ a ∈ s, x ≤ a :=
  Iff.rfl

-- We do not tag those two as `simp` to respect the abstraction.
@[norm_cast]
theorem coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a ∈ s, Ici a := by
  ext
  simp

@[norm_cast]
theorem coe_lowerClosure (s : Set α) : ↑(lowerClosure s) = ⋃ a ∈ s, Iic a := by
  ext
  simp

instance instDecidablePredMemUpperClosure [DecidablePred (∃ a ∈ s, a ≤ ·)] :
    DecidablePred (· ∈ upperClosure s) := ‹DecidablePred _›

instance instDecidablePredMemLowerClosure [DecidablePred (∃ a ∈ s, · ≤ a)] :
    DecidablePred (· ∈ lowerClosure s) := ‹DecidablePred _›

theorem subset_upperClosure : s ⊆ upperClosure s := fun x hx => ⟨x, hx, le_rfl⟩

theorem subset_lowerClosure : s ⊆ lowerClosure s := fun x hx => ⟨x, hx, le_rfl⟩

theorem upperClosure_min (h : s ⊆ t) (ht : IsUpperSet t) : ↑(upperClosure s) ⊆ t :=
  fun _a ⟨_b, hb, hba⟩ => ht hba <| h hb

theorem lowerClosure_min (h : s ⊆ t) (ht : IsLowerSet t) : ↑(lowerClosure s) ⊆ t :=
  fun _a ⟨_b, hb, hab⟩ => ht hab <| h hb

protected theorem IsUpperSet.upperClosure (hs : IsUpperSet s) : ↑(upperClosure s) = s :=
  (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure

protected theorem IsLowerSet.lowerClosure (hs : IsLowerSet s) : ↑(lowerClosure s) = s :=
  (lowerClosure_min Subset.rfl hs).antisymm subset_lowerClosure

@[simp]
protected theorem UpperSet.upperClosure (s : UpperSet α) : upperClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.upperClosure

@[simp]
protected theorem LowerSet.lowerClosure (s : LowerSet α) : lowerClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.lowerClosure

@[simp]
theorem upperClosure_image (f : α ≃o β) :
    upperClosure (f '' s) = UpperSet.map f (upperClosure s) := by
  rw [← f.symm_symm, ← UpperSet.symm_map, f.symm_symm]
  ext
  simp [-UpperSet.symm_map, UpperSet.map, OrderIso.symm, ← f.le_symm_apply]

@[simp]
theorem lowerClosure_image (f : α ≃o β) :
    lowerClosure (f '' s) = LowerSet.map f (lowerClosure s) := by
  rw [← f.symm_symm, ← LowerSet.symm_map, f.symm_symm]
  ext
  simp [-LowerSet.symm_map, LowerSet.map, OrderIso.symm, ← f.symm_apply_le]

@[simp]
theorem UpperSet.iInf_Ici (s : Set α) : ⨅ a ∈ s, UpperSet.Ici a = upperClosure s := by
  ext
  simp

@[simp]
theorem LowerSet.iSup_Iic (s : Set α) : ⨆ a ∈ s, LowerSet.Iic a = lowerClosure s := by
  ext
  simp

@[simp] lemma lowerClosure_le {t : LowerSet α} : lowerClosure s ≤ t ↔ s ⊆ t :=
  ⟨fun h ↦ subset_lowerClosure.trans <| LowerSet.coe_subset_coe.2 h,
    fun h ↦ lowerClosure_min h t.lower⟩

@[simp] lemma le_upperClosure {s : UpperSet α} : s ≤ upperClosure t ↔ t ⊆ s :=
  ⟨fun h ↦ subset_upperClosure.trans <| UpperSet.coe_subset_coe.2 h,
    fun h ↦ upperClosure_min h s.upper⟩

theorem gc_upperClosure_coe :
    GaloisConnection (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) :=
  fun _s _t ↦ le_upperClosure

theorem gc_lowerClosure_coe :
    GaloisConnection (lowerClosure : Set α → LowerSet α) (↑) := fun _s _t ↦ lowerClosure_le

/-- `upperClosure` forms a reversed Galois insertion with the coercion from upper sets to sets. -/
def giUpperClosureCoe :
    GaloisInsertion (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) where
  choice s hs := toDual (⟨s, fun a _b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
  choice_eq _s hs := ofDual.injective <| SetLike.coe_injective <| subset_upperClosure.antisymm hs

/-- `lowerClosure` forms a Galois insertion with the coercion from lower sets to sets. -/
def giLowerClosureCoe : GaloisInsertion (lowerClosure : Set α → LowerSet α) (↑) where
  choice s hs := ⟨s, fun a _b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
  choice_eq _s hs := SetLike.coe_injective <| subset_lowerClosure.antisymm hs

theorem upperClosure_anti : Antitone (upperClosure : Set α → UpperSet α) :=
  gc_upperClosure_coe.monotone_l

theorem lowerClosure_mono : Monotone (lowerClosure : Set α → LowerSet α) :=
  gc_lowerClosure_coe.monotone_l

@[simp]
theorem upperClosure_empty : upperClosure (∅ : Set α) = ⊤ :=
  (@gc_upperClosure_coe α).l_bot

@[simp]
theorem lowerClosure_empty : lowerClosure (∅ : Set α) = ⊥ :=
  (@gc_lowerClosure_coe α).l_bot

@[simp]
theorem upperClosure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.Ici a := by
  ext
  simp

@[simp]
theorem lowerClosure_singleton (a : α) : lowerClosure ({a} : Set α) = LowerSet.Iic a := by
  ext
  simp

@[simp]
theorem upperClosure_univ : upperClosure (univ : Set α) = ⊥ :=
  bot_unique subset_upperClosure

@[simp]
theorem lowerClosure_univ : lowerClosure (univ : Set α) = ⊤ :=
  top_unique subset_lowerClosure

@[simp]
theorem upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅ :=
  (@gc_upperClosure_coe α _).l_eq_bot.trans subset_empty_iff

@[simp]
theorem lowerClosure_eq_bot_iff : lowerClosure s = ⊥ ↔ s = ∅ :=
  (@gc_lowerClosure_coe α _).l_eq_bot.trans subset_empty_iff

@[simp]
theorem upperClosure_union (s t : Set α) : upperClosure (s ∪ t) = upperClosure s ⊓ upperClosure t :=
  (@gc_upperClosure_coe α _).l_sup

@[simp]
theorem lowerClosure_union (s t : Set α) : lowerClosure (s ∪ t) = lowerClosure s ⊔ lowerClosure t :=
  (@gc_lowerClosure_coe α _).l_sup

@[simp]
theorem upperClosure_iUnion (f : ι → Set α) : upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i) :=
  (@gc_upperClosure_coe α _).l_iSup

@[simp]
theorem lowerClosure_iUnion (f : ι → Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i) :=
  (@gc_lowerClosure_coe α _).l_iSup

@[simp]
theorem upperClosure_sUnion (S : Set (Set α)) : upperClosure (⋃₀ S) = ⨅ s ∈ S, upperClosure s := by
  simp_rw [sUnion_eq_biUnion, upperClosure_iUnion]

@[simp]
theorem lowerClosure_sUnion (S : Set (Set α)) : lowerClosure (⋃₀ S) = ⨆ s ∈ S, lowerClosure s := by
  simp_rw [sUnion_eq_biUnion, lowerClosure_iUnion]

theorem Set.OrdConnected.upperClosure_inter_lowerClosure (h : s.OrdConnected) :
    ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun _a ⟨⟨_b, hb, hba⟩, _c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩

theorem ordConnected_iff_upperClosure_inter_lowerClosure :
    s.OrdConnected ↔ ↑(upperClosure s) ∩ ↑(lowerClosure s) = s := by
  refine ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => ?_⟩
  rw [← h]
  exact (UpperSet.upper _).ordConnected.inter (LowerSet.lower _).ordConnected

@[simp]
theorem upperBounds_lowerClosure : upperBounds (lowerClosure s : Set α) = upperBounds s :=
  (upperBounds_mono_set subset_lowerClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ ↦ hcb.trans <| ha hc

@[simp]
theorem lowerBounds_upperClosure : lowerBounds (upperClosure s : Set α) = lowerBounds s :=
  (lowerBounds_mono_set subset_upperClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ ↦ (ha hc).trans hcb

@[simp]
theorem bddAbove_lowerClosure : BddAbove (lowerClosure s : Set α) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_lowerClosure]

@[simp]
theorem bddBelow_upperClosure : BddBelow (upperClosure s : Set α) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_upperClosure]

protected alias ⟨BddAbove.of_lowerClosure, BddAbove.lowerClosure⟩ := bddAbove_lowerClosure

protected alias ⟨BddBelow.of_upperClosure, BddBelow.upperClosure⟩ := bddBelow_upperClosure

@[simp] lemma IsLowerSet.disjoint_upperClosure_left (ht : IsLowerSet t) :
    Disjoint ↑(upperClosure s) t ↔ Disjoint s t := by
  refine ⟨Disjoint.mono_left subset_upperClosure, ?_⟩
  simp only [disjoint_left, SetLike.mem_coe, mem_upperClosure, forall_exists_index, and_imp]
  exact fun h a b hb hba ha ↦ h hb <| ht hba ha

@[simp] lemma IsLowerSet.disjoint_upperClosure_right (hs : IsLowerSet s) :
    Disjoint s (upperClosure t) ↔ Disjoint s t := by
  simpa only [disjoint_comm] using hs.disjoint_upperClosure_left

@[simp] lemma IsUpperSet.disjoint_lowerClosure_left (ht : IsUpperSet t) :
    Disjoint ↑(lowerClosure s) t ↔ Disjoint s t := ht.toDual.disjoint_upperClosure_left

@[simp] lemma IsUpperSet.disjoint_lowerClosure_right (hs : IsUpperSet s) :
    Disjoint s (lowerClosure t) ↔ Disjoint s t := hs.toDual.disjoint_upperClosure_right

@[simp] lemma upperClosure_eq :
    ↑(upperClosure s) = s ↔ IsUpperSet s :=
  ⟨(· ▸ UpperSet.upper _), IsUpperSet.upperClosure⟩

@[simp] lemma lowerClosure_eq :
    ↑(lowerClosure s) = s ↔ IsLowerSet s :=
  @upperClosure_eq αᵒᵈ _ _

end closure

/-! ### Set Difference -/

namespace LowerSet
variable [Preorder α] {s : LowerSet α} {t : Set α} {a : α}

/-- The biggest lower subset of a lower set `s` disjoint from a set `t`. -/
def sdiff (s : LowerSet α) (t : Set α) : LowerSet α where
  carrier := s \ upperClosure t
  lower' := s.lower.sdiff_of_isUpperSet (upperClosure t).upper

/-- The biggest lower subset of a lower set `s` not containing an element `a`. -/
def erase (s : LowerSet α) (a : α) : LowerSet α where
  carrier := s \ UpperSet.Ici a
  lower' := s.lower.sdiff_of_isUpperSet (UpperSet.Ici a).upper

@[simp, norm_cast]
lemma coe_sdiff (s : LowerSet α) (t : Set α) : s.sdiff t = (s : Set α) \ upperClosure t := rfl

@[simp, norm_cast]
lemma coe_erase (s : LowerSet α) (a : α) : s.erase a = (s : Set α) \ UpperSet.Ici a := rfl

@[simp] lemma sdiff_singleton (s : LowerSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]

lemma sdiff_le_left : s.sdiff t ≤ s := diff_subset
lemma erase_le : s.erase a ≤ s := diff_subset

@[simp] protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[simp] lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[simp] lemma sdiff_lt_left : s.sdiff t < s ↔ ¬ Disjoint ↑s t :=
  sdiff_le_left.lt_iff_ne.trans LowerSet.sdiff_eq_left.not

@[simp] lemma erase_lt : s.erase a < s ↔ a ∈ s := erase_le.lt_iff_ne.trans erase_eq.not_left

@[simp] protected lemma sdiff_idem (s : LowerSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[simp] lemma erase_idem (s : LowerSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

lemma sdiff_sup_lowerClosure (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, c ≤ b → b ∈ t) :
    s.sdiff t ⊔ lowerClosure t = s := by
  refine le_antisymm (sup_le sdiff_le_left <| lowerClosure_le.2 hts) fun a ha ↦ ?_
  obtain hat | hat := em (a ∈ t)
  · exact subset_union_right (subset_lowerClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hba⟩
    exact hat <| hst _ ha _ hb hba

lemma lowerClosure_sup_sdiff (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, c ≤ b → b ∈ t) :
    lowerClosure t ⊔ s.sdiff t = s := by rw [sup_comm, sdiff_sup_lowerClosure hts hst]

lemma erase_sup_Iic (ha : a ∈ s) (has : ∀ b ∈ s, a ≤ b → b = a) : s.erase a ⊔ Iic a = s := by
  rw [← lowerClosure_singleton, ← sdiff_singleton, sdiff_sup_lowerClosure] <;> simpa

lemma Iic_sup_erase (ha : a ∈ s) (has : ∀ b ∈ s, a ≤ b → b = a) : Iic a ⊔ s.erase a = s := by
  rw [sup_comm, erase_sup_Iic ha has]

end LowerSet

namespace UpperSet
variable [Preorder α] {s : UpperSet α} {t : Set α} {a : α}

/-- The biggest upper subset of a upper set `s` disjoint from a set `t`. -/
def sdiff (s : UpperSet α) (t : Set α) : UpperSet α where
  carrier := s \ lowerClosure t
  upper' := s.upper.sdiff_of_isLowerSet (lowerClosure t).lower

/-- The biggest upper subset of a upper set `s` not containing an element `a`. -/
def erase (s : UpperSet α) (a : α) : UpperSet α where
  carrier := s \ LowerSet.Iic a
  upper' := s.upper.sdiff_of_isLowerSet (LowerSet.Iic a).lower

@[simp, norm_cast]
lemma coe_sdiff (s : UpperSet α) (t : Set α) : s.sdiff t = (s : Set α) \ lowerClosure t := rfl

@[simp, norm_cast]
lemma coe_erase (s : UpperSet α) (a : α) : s.erase a = (s : Set α) \ LowerSet.Iic a := rfl

@[simp] lemma sdiff_singleton (s : UpperSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]

lemma le_sdiff_left : s ≤ s.sdiff t := diff_subset
lemma le_erase : s ≤ s.erase a := diff_subset

@[simp] protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[simp] lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[simp] lemma lt_sdiff_left : s < s.sdiff t ↔ ¬ Disjoint ↑s t :=
  le_sdiff_left.gt_iff_ne.trans UpperSet.sdiff_eq_left.not

@[simp] lemma lt_erase : s < s.erase a ↔ a ∈ s := le_erase.gt_iff_ne.trans erase_eq.not_left

@[simp] protected lemma sdiff_idem (s : UpperSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[simp] lemma erase_idem (s : UpperSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

lemma sdiff_inf_upperClosure (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    s.sdiff t ⊓ upperClosure t = s := by
  refine ge_antisymm (le_inf le_sdiff_left <| le_upperClosure.2 hts) fun a ha ↦ ?_
  obtain hat | hat := em (a ∈ t)
  · exact subset_union_right (subset_upperClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hab⟩
    exact hat <| hst _ ha _ hb hab

lemma upperClosure_inf_sdiff (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    upperClosure t ⊓ s.sdiff t = s := by rw [inf_comm, sdiff_inf_upperClosure hts hst]

lemma erase_inf_Ici (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : s.erase a ⊓ Ici a = s := by
  rw [← upperClosure_singleton, ← sdiff_singleton, sdiff_inf_upperClosure] <;> simpa

lemma Ici_inf_erase (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : Ici a ⊓ s.erase a = s := by
  rw [inf_comm, erase_inf_Ici ha has]

end UpperSet

/-! ### Product -/


section Preorder

variable [Preorder α] [Preorder β]

section

variable {s : Set α} {t : Set β}

theorem IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

theorem IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

end

namespace UpperSet

variable (s s₁ s₂ : UpperSet α) (t t₁ t₂ : UpperSet β) {x : α × β}

/-- The product of two upper sets as an upper set. -/
def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.prod t.2⟩

instance instSProd : SProd (UpperSet α) (UpperSet β) (UpperSet (α × β)) where
  sprod := UpperSet.prod

@[simp, norm_cast]
theorem coe_prod : ((s ×ˢ t : UpperSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t :=
  rfl

@[simp]
theorem mem_prod {s : UpperSet α} {t : UpperSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl

theorem Ici_prod (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2 :=
  rfl

@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) :=
  rfl

@[simp]
theorem prod_top : s ×ˢ (⊤ : UpperSet β) = ⊤ :=
  ext prod_empty

@[simp]
theorem top_prod : (⊤ : UpperSet α) ×ˢ t = ⊤ :=
  ext empty_prod

@[simp]
theorem bot_prod_bot : (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥ :=
  ext univ_prod_univ

@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext inter_prod

@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_inter

@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext union_prod

@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_union

theorem prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂) :=
  ext prod_inter_prod

variable {s s₁ s₂ t t₁ t₂}

@[mono]
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  Set.prod_mono

theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  Set.prod_mono_left

theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  Set.prod_mono_right

@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self

@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self

theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤ :=
  prod_subset_prod_iff.trans <| by simp

@[simp]
theorem prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]
theorem codisjoint_prod :
    Codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Codisjoint s₁ s₂ ∨ Codisjoint t₁ t₂ := by
  simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]

end UpperSet

namespace LowerSet

variable (s s₁ s₂ : LowerSet α) (t t₁ t₂ : LowerSet β) {x : α × β}

/-- The product of two lower sets as a lower set. -/
def prod : LowerSet (α × β) := ⟨s ×ˢ t, s.2.prod t.2⟩

instance instSProd : SProd (LowerSet α) (LowerSet β) (LowerSet (α × β)) where
  sprod := LowerSet.prod

@[simp, norm_cast]
theorem coe_prod : ((s ×ˢ t : LowerSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t := rfl

@[simp]
theorem mem_prod {s : LowerSet α} {t : LowerSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl

theorem Iic_prod (x : α × β) : Iic x = Iic x.1 ×ˢ Iic x.2 :=
  rfl

@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl

@[simp]
theorem prod_bot : s ×ˢ (⊥ : LowerSet β) = ⊥ :=
  ext prod_empty

@[simp]
theorem bot_prod : (⊥ : LowerSet α) ×ˢ t = ⊥ :=
  ext empty_prod

@[simp]
theorem top_prod_top : (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤ :=
  ext univ_prod_univ

@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext inter_prod

@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_inter

@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext union_prod

@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_union

theorem prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂) :=
  ext prod_inter_prod

variable {s s₁ s₂ t t₁ t₂}

theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ := Set.prod_mono

theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t := Set.prod_mono_left

theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ := Set.prod_mono_right

@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self

@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self

theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥ :=
  prod_subset_prod_iff.trans <| by simp

@[simp]
theorem prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]

end LowerSet

@[simp]
theorem upperClosure_prod (s : Set α) (t : Set β) :
    upperClosure (s ×ˢ t) = upperClosure s ×ˢ upperClosure t := by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ ∈ t)]

@[simp]
theorem lowerClosure_prod (s : Set α) (t : Set β) :
    lowerClosure (s ×ˢ t) = lowerClosure s ×ˢ lowerClosure t := by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ ∈ t)]

end Preorder

set_option linter.style.longFile 1900
