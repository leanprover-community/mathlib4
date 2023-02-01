/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta

! This file was ported from Lean 3 source module order.upper_lower.basic
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Set.Intervals.OrdConnected
import Mathbin.Data.Set.Intervals.OrderIso

/-!
# Up-sets and down-sets

This file defines upper and lower sets in an order.

## Main declarations

* `is_upper_set`: Predicate for a set to be an upper set. This means every element greater than a
  member of the set is in the set itself.
* `is_lower_set`: Predicate for a set to be a lower set. This means every element less than a member
  of the set is in the set itself.
* `upper_set`: The type of upper sets.
* `lower_set`: The type of lower sets.
* `upper_closure`: The greatest upper set containing a set.
* `lower_closure`: The least lower set containing a set.
* `upper_set.Ici`: Principal upper set. `set.Ici` as an upper set.
* `upper_set.Ioi`: Strict principal upper set. `set.Ioi` as an upper set.
* `lower_set.Iic`: Principal lower set. `set.Iic` as an lower set.
* `lower_set.Iio`: Strict principal lower set. `set.Iio` as an lower set.

## Notation

`×ˢ` is notation for `upper_set.prod`/`lower_set.prod`.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `filter`.

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/


open OrderDual Set

variable {α β γ : Type _} {ι : Sort _} {κ : ι → Sort _}

/-! ### Unbundled upper/lower sets -/


section LE

variable [LE α] [LE β] {s t : Set α}

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
def IsUpperSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s
#align is_upper_set IsUpperSet

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
def IsLowerSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s
#align is_lower_set IsLowerSet

theorem isUpperSet_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id
#align is_upper_set_empty isUpperSet_empty

theorem isLowerSet_empty : IsLowerSet (∅ : Set α) := fun _ _ _ => id
#align is_lower_set_empty isLowerSet_empty

theorem isUpperSet_univ : IsUpperSet (univ : Set α) := fun _ _ _ => id
#align is_upper_set_univ isUpperSet_univ

theorem isLowerSet_univ : IsLowerSet (univ : Set α) := fun _ _ _ => id
#align is_lower_set_univ isLowerSet_univ

theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet (sᶜ) := fun a b h hb ha => hb <| hs h ha
#align is_upper_set.compl IsUpperSet.compl

theorem IsLowerSet.compl (hs : IsLowerSet s) : IsUpperSet (sᶜ) := fun a b h hb ha => hb <| hs h ha
#align is_lower_set.compl IsLowerSet.compl

@[simp]
theorem isUpperSet_compl : IsUpperSet (sᶜ) ↔ IsLowerSet s :=
  ⟨fun h => by
    convert h.compl
    rw [compl_compl], IsLowerSet.compl⟩
#align is_upper_set_compl isUpperSet_compl

@[simp]
theorem isLowerSet_compl : IsLowerSet (sᶜ) ↔ IsUpperSet s :=
  ⟨fun h => by
    convert h.compl
    rw [compl_compl], IsUpperSet.compl⟩
#align is_lower_set_compl isLowerSet_compl

theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∪ t) :=
  fun a b h => Or.imp (hs h) (ht h)
#align is_upper_set.union IsUpperSet.union

theorem IsLowerSet.union (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∪ t) :=
  fun a b h => Or.imp (hs h) (ht h)
#align is_lower_set.union IsLowerSet.union

theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∩ t) :=
  fun a b h => And.imp (hs h) (ht h)
#align is_upper_set.inter IsUpperSet.inter

theorem IsLowerSet.inter (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∩ t) :=
  fun a b h => And.imp (hs h) (ht h)
#align is_lower_set.inter IsLowerSet.inter

theorem isUpperSet_unionᵢ {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) :=
  fun a b h => Exists₂.imp <| forall_range_iff.2 fun i => hf i h
#align is_upper_set_Union isUpperSet_unionᵢ

theorem isLowerSet_unionᵢ {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋃ i, f i) :=
  fun a b h => Exists₂.imp <| forall_range_iff.2 fun i => hf i h
#align is_lower_set_Union isLowerSet_unionᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem isUpperSet_Union₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋃ (i) (j), f i j) :=
  isUpperSet_unionᵢ fun i => isUpperSet_unionᵢ <| hf i
#align is_upper_set_Union₂ isUpperSet_Union₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem isLowerSet_Union₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) :
    IsLowerSet (⋃ (i) (j), f i j) :=
  isLowerSet_unionᵢ fun i => isLowerSet_unionᵢ <| hf i
#align is_lower_set_Union₂ isLowerSet_Union₂

theorem isUpperSet_unionₛ {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋃₀ S) :=
  fun a b h => Exists₂.imp fun s hs => hf s hs h
#align is_upper_set_sUnion isUpperSet_unionₛ

theorem isLowerSet_unionₛ {S : Set (Set α)} (hf : ∀ s ∈ S, IsLowerSet s) : IsLowerSet (⋃₀ S) :=
  fun a b h => Exists₂.imp fun s hs => hf s hs h
#align is_lower_set_sUnion isLowerSet_unionₛ

theorem isUpperSet_interᵢ {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) :=
  fun a b h => forall₂_imp <| forall_range_iff.2 fun i => hf i h
#align is_upper_set_Inter isUpperSet_interᵢ

theorem isLowerSet_interᵢ {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋂ i, f i) :=
  fun a b h => forall₂_imp <| forall_range_iff.2 fun i => hf i h
#align is_lower_set_Inter isLowerSet_interᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem isUpperSet_Inter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋂ (i) (j), f i j) :=
  isUpperSet_interᵢ fun i => isUpperSet_interᵢ <| hf i
#align is_upper_set_Inter₂ isUpperSet_Inter₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem isLowerSet_Inter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) :
    IsLowerSet (⋂ (i) (j), f i j) :=
  isLowerSet_interᵢ fun i => isLowerSet_interᵢ <| hf i
#align is_lower_set_Inter₂ isLowerSet_Inter₂

theorem isUpperSet_interₛ {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋂₀ S) :=
  fun a b h => forall₂_imp fun s hs => hf s hs h
#align is_upper_set_sInter isUpperSet_interₛ

theorem isLowerSet_interₛ {S : Set (Set α)} (hf : ∀ s ∈ S, IsLowerSet s) : IsLowerSet (⋂₀ S) :=
  fun a b h => forall₂_imp fun s hs => hf s hs h
#align is_lower_set_sInter isLowerSet_interₛ

@[simp]
theorem isLowerSet_preimage_ofDual_iff : IsLowerSet (ofDual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl
#align is_lower_set_preimage_of_dual_iff isLowerSet_preimage_ofDual_iff

@[simp]
theorem isUpperSet_preimage_ofDual_iff : IsUpperSet (ofDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl
#align is_upper_set_preimage_of_dual_iff isUpperSet_preimage_ofDual_iff

@[simp]
theorem isLowerSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsLowerSet (toDual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl
#align is_lower_set_preimage_to_dual_iff isLowerSet_preimage_toDual_iff

@[simp]
theorem isUpperSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsUpperSet (toDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl
#align is_upper_set_preimage_to_dual_iff isUpperSet_preimage_toDual_iff

alias isLowerSet_preimage_ofDual_iff ↔ _ IsUpperSet.ofDual
#align is_upper_set.of_dual IsUpperSet.ofDual

alias isUpperSet_preimage_ofDual_iff ↔ _ IsLowerSet.ofDual
#align is_lower_set.of_dual IsLowerSet.ofDual

alias isLowerSet_preimage_toDual_iff ↔ _ IsUpperSet.toDual
#align is_upper_set.to_dual IsUpperSet.toDual

alias isUpperSet_preimage_toDual_iff ↔ _ IsLowerSet.toDual
#align is_lower_set.to_dual IsLowerSet.toDual

end LE

section Preorder

variable [Preorder α] [Preorder β] {s : Set α} {p : α → Prop} (a : α)

theorem isUpperSet_Ici : IsUpperSet (Ici a) := fun _ _ => ge_trans
#align is_upper_set_Ici isUpperSet_Ici

theorem isLowerSet_Iic : IsLowerSet (Iic a) := fun _ _ => le_trans
#align is_lower_set_Iic isLowerSet_Iic

theorem isUpperSet_Ioi : IsUpperSet (Ioi a) := fun _ _ => flip lt_of_lt_of_le
#align is_upper_set_Ioi isUpperSet_Ioi

theorem isLowerSet_Iio : IsLowerSet (Iio a) := fun _ _ => lt_of_le_of_lt
#align is_lower_set_Iio isLowerSet_Iio

theorem isUpperSet_iff_Ici_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ici a ⊆ s := by
  simp [IsUpperSet, subset_def, @forall_swap (_ ∈ s)]
#align is_upper_set_iff_Ici_subset isUpperSet_iff_Ici_subset

theorem isLowerSet_iff_Iic_subset : IsLowerSet s ↔ ∀ ⦃a⦄, a ∈ s → Iic a ⊆ s := by
  simp [IsLowerSet, subset_def, @forall_swap (_ ∈ s)]
#align is_lower_set_iff_Iic_subset isLowerSet_iff_Iic_subset

alias isUpperSet_iff_Ici_subset ↔ IsUpperSet.Ici_subset _
#align is_upper_set.Ici_subset IsUpperSet.Ici_subset

alias isLowerSet_iff_Iic_subset ↔ IsLowerSet.Iic_subset _
#align is_lower_set.Iic_subset IsLowerSet.Iic_subset

theorem IsUpperSet.ordConnected (h : IsUpperSet s) : s.OrdConnected :=
  ⟨fun a ha b _ => Icc_subset_Ici_self.trans <| h.Ici_subset ha⟩
#align is_upper_set.ord_connected IsUpperSet.ordConnected

theorem IsLowerSet.ordConnected (h : IsLowerSet s) : s.OrdConnected :=
  ⟨fun a _ b hb => Icc_subset_Iic_self.trans <| h.Iic_subset hb⟩
#align is_lower_set.ord_connected IsLowerSet.ordConnected

theorem IsUpperSet.preimage (hs : IsUpperSet s) {f : β → α} (hf : Monotone f) :
    IsUpperSet (f ⁻¹' s : Set β) := fun x y hxy => hs <| hf hxy
#align is_upper_set.preimage IsUpperSet.preimage

theorem IsLowerSet.preimage (hs : IsLowerSet s) {f : β → α} (hf : Monotone f) :
    IsLowerSet (f ⁻¹' s : Set β) := fun x y hxy => hs <| hf hxy
#align is_lower_set.preimage IsLowerSet.preimage

theorem IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : IsUpperSet (f '' s : Set β) :=
  by
  change IsUpperSet ((f : α ≃ β) '' s)
  rw [Set.image_equiv_eq_preimage_symm]
  exact hs.preimage f.symm.monotone
#align is_upper_set.image IsUpperSet.image

theorem IsLowerSet.image (hs : IsLowerSet s) (f : α ≃o β) : IsLowerSet (f '' s : Set β) :=
  by
  change IsLowerSet ((f : α ≃ β) '' s)
  rw [Set.image_equiv_eq_preimage_symm]
  exact hs.preimage f.symm.monotone
#align is_lower_set.image IsLowerSet.image

@[simp]
theorem Set.monotone_mem : Monotone (· ∈ s) ↔ IsUpperSet s :=
  Iff.rfl
#align set.monotone_mem Set.monotone_mem

@[simp]
theorem Set.antitone_mem : Antitone (· ∈ s) ↔ IsLowerSet s :=
  forall_swap
#align set.antitone_mem Set.antitone_mem

@[simp]
theorem isUpperSet_setOf : IsUpperSet { a | p a } ↔ Monotone p :=
  Iff.rfl
#align is_upper_set_set_of isUpperSet_setOf

@[simp]
theorem isLowerSet_setOf : IsLowerSet { a | p a } ↔ Antitone p :=
  forall_swap
#align is_lower_set_set_of isLowerSet_setOf

section OrderTop

variable [OrderTop α]

theorem IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun a => hs le_top h, fun h => h.symm ▸ mem_univ _⟩
#align is_lower_set.top_mem IsLowerSet.top_mem

theorem IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨a, ha⟩ => hs le_top ha⟩
#align is_upper_set.top_mem IsUpperSet.top_mem

theorem IsUpperSet.not_top_mem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.Not.trans not_nonempty_iff_eq_empty
#align is_upper_set.not_top_mem IsUpperSet.not_top_mem

end OrderTop

section OrderBot

variable [OrderBot α]

theorem IsUpperSet.bot_mem (hs : IsUpperSet s) : ⊥ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun a => hs bot_le h, fun h => h.symm ▸ mem_univ _⟩
#align is_upper_set.bot_mem IsUpperSet.bot_mem

theorem IsLowerSet.bot_mem (hs : IsLowerSet s) : ⊥ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨a, ha⟩ => hs bot_le ha⟩
#align is_lower_set.bot_mem IsLowerSet.bot_mem

theorem IsLowerSet.not_bot_mem (hs : IsLowerSet s) : ⊥ ∉ s ↔ s = ∅ :=
  hs.bot_mem.Not.trans not_nonempty_iff_eq_empty
#align is_lower_set.not_bot_mem IsLowerSet.not_bot_mem

end OrderBot

section NoMaxOrder

variable [NoMaxOrder α] (a)

theorem IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s.Nonempty → ¬BddAbove s :=
  by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_le (hb <| hs ((hb ha).trans hc.le) ha)
#align is_upper_set.not_bdd_above IsUpperSet.not_bddAbove

theorem not_bddAbove_Ici : ¬BddAbove (Ici a) :=
  (isUpperSet_Ici _).not_bddAbove nonempty_Ici
#align not_bdd_above_Ici not_bddAbove_Ici

theorem not_bddAbove_Ioi : ¬BddAbove (Ioi a) :=
  (isUpperSet_Ioi _).not_bddAbove nonempty_Ioi
#align not_bdd_above_Ioi not_bddAbove_Ioi

end NoMaxOrder

section NoMinOrder

variable [NoMinOrder α] (a)

theorem IsLowerSet.not_bddBelow (hs : IsLowerSet s) : s.Nonempty → ¬BddBelow s :=
  by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_lt b
  exact hc.not_le (hb <| hs (hc.le.trans <| hb ha) ha)
#align is_lower_set.not_bdd_below IsLowerSet.not_bddBelow

theorem not_bddBelow_Iic : ¬BddBelow (Iic a) :=
  (isLowerSet_Iic _).not_bddBelow nonempty_Iic
#align not_bdd_below_Iic not_bddBelow_Iic

theorem not_bddBelow_Iio : ¬BddBelow (Iio a) :=
  (isLowerSet_Iio _).not_bddBelow nonempty_Iio
#align not_bdd_below_Iio not_bddBelow_Iio

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α}

theorem isUpperSet_iff_forall_lt : IsUpperSet s ↔ ∀ ⦃a b : α⦄, a < b → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]
#align is_upper_set_iff_forall_lt isUpperSet_iff_forall_lt

theorem isLowerSet_iff_forall_lt : IsLowerSet s ↔ ∀ ⦃a b : α⦄, b < a → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]
#align is_lower_set_iff_forall_lt isLowerSet_iff_forall_lt

theorem isUpperSet_iff_Ioi_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ioi a ⊆ s := by
  simp [isUpperSet_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]
#align is_upper_set_iff_Ioi_subset isUpperSet_iff_Ioi_subset

theorem isLowerSet_iff_Iio_subset : IsLowerSet s ↔ ∀ ⦃a⦄, a ∈ s → Iio a ⊆ s := by
  simp [isLowerSet_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]
#align is_lower_set_iff_Iio_subset isLowerSet_iff_Iio_subset

alias isUpperSet_iff_Ioi_subset ↔ IsUpperSet.Ioi_subset _
#align is_upper_set.Ioi_subset IsUpperSet.Ioi_subset

alias isLowerSet_iff_Iio_subset ↔ IsLowerSet.Iio_subset _
#align is_lower_set.Iio_subset IsLowerSet.Iio_subset

end PartialOrder

/-! ### Bundled upper/lower sets -/


section LE

variable [LE α]

/-- The type of upper sets of an order. -/
structure UpperSet (α : Type _) [LE α] where
  carrier : Set α
  upper' : IsUpperSet carrier
#align upper_set UpperSet

/-- The type of lower sets of an order. -/
structure LowerSet (α : Type _) [LE α] where
  carrier : Set α
  lower' : IsLowerSet carrier
#align lower_set LowerSet

namespace UpperSet

instance : SetLike (UpperSet α) α where
  coe := UpperSet.carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

@[ext]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'
#align upper_set.ext UpperSet.ext

@[simp]
theorem carrier_eq_coe (s : UpperSet α) : s.carrier = s :=
  rfl
#align upper_set.carrier_eq_coe UpperSet.carrier_eq_coe

protected theorem upper (s : UpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'
#align upper_set.upper UpperSet.upper

@[simp]
theorem mem_mk (carrier : Set α) (upper') {a : α} : a ∈ mk carrier upper' ↔ a ∈ carrier :=
  Iff.rfl
#align upper_set.mem_mk UpperSet.mem_mk

end UpperSet

namespace LowerSet

instance : SetLike (LowerSet α) α where
  coe := LowerSet.carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

@[ext]
theorem ext {s t : LowerSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'
#align lower_set.ext LowerSet.ext

@[simp]
theorem carrier_eq_coe (s : LowerSet α) : s.carrier = s :=
  rfl
#align lower_set.carrier_eq_coe LowerSet.carrier_eq_coe

protected theorem lower (s : LowerSet α) : IsLowerSet (s : Set α) :=
  s.lower'
#align lower_set.lower LowerSet.lower

@[simp]
theorem mem_mk (carrier : Set α) (lower') {a : α} : a ∈ mk carrier lower' ↔ a ∈ carrier :=
  Iff.rfl
#align lower_set.mem_mk LowerSet.mem_mk

end LowerSet

/-! #### Order -/


namespace UpperSet

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

instance : HasSup (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

instance : HasInf (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

instance : Top (UpperSet α) :=
  ⟨⟨∅, isUpperSet_empty⟩⟩

instance : Bot (UpperSet α) :=
  ⟨⟨univ, isUpperSet_univ⟩⟩

instance : SupSet (UpperSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isUpperSet_Inter₂ fun s _ => s.upper⟩⟩

instance : InfSet (UpperSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isUpperSet_Union₂ fun s _ => s.upper⟩⟩

instance : CompleteDistribLattice (UpperSet α) :=
  (toDual.Injective.comp <| SetLike.coe_injective).CompleteDistribLattice _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ t ≤ s :=
  Iff.rfl
#align upper_set.coe_subset_coe UpperSet.coe_subset_coe

@[simp, norm_cast]
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl
#align upper_set.coe_top UpperSet.coe_top

@[simp, norm_cast]
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl
#align upper_set.coe_bot UpperSet.coe_bot

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊥ := by simp [SetLike.ext'_iff]
#align upper_set.coe_eq_univ UpperSet.coe_eq_univ

@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤ := by simp [SetLike.ext'_iff]
#align upper_set.coe_eq_empty UpperSet.coe_eq_empty

@[simp, norm_cast]
theorem coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = s ∩ t :=
  rfl
#align upper_set.coe_sup UpperSet.coe_sup

@[simp, norm_cast]
theorem coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = s ∪ t :=
  rfl
#align upper_set.coe_inf UpperSet.coe_inf

@[simp, norm_cast]
theorem coe_supₛ (S : Set (UpperSet α)) : (↑(supₛ S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl
#align upper_set.coe_Sup UpperSet.coe_supₛ

@[simp, norm_cast]
theorem coe_infₛ (S : Set (UpperSet α)) : (↑(infₛ S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl
#align upper_set.coe_Inf UpperSet.coe_infₛ

@[simp, norm_cast]
theorem coe_supᵢ (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by simp [supᵢ]
#align upper_set.coe_supr UpperSet.coe_supᵢ

@[simp, norm_cast]
theorem coe_infᵢ (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [infᵢ]
#align upper_set.coe_infi UpperSet.coe_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_supr₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j :=
  by simp_rw [coe_supr]
#align upper_set.coe_supr₂ UpperSet.coe_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_infi₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j :=
  by simp_rw [coe_infi]
#align upper_set.coe_infi₂ UpperSet.coe_infi₂

@[simp]
theorem not_mem_top : a ∉ (⊤ : UpperSet α) :=
  id
#align upper_set.not_mem_top UpperSet.not_mem_top

@[simp]
theorem mem_bot : a ∈ (⊥ : UpperSet α) :=
  trivial
#align upper_set.mem_bot UpperSet.mem_bot

@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl
#align upper_set.mem_sup_iff UpperSet.mem_sup_iff

@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl
#align upper_set.mem_inf_iff UpperSet.mem_inf_iff

@[simp]
theorem mem_supₛ_iff : a ∈ supₛ S ↔ ∀ s ∈ S, a ∈ s :=
  mem_interᵢ₂
#align upper_set.mem_Sup_iff UpperSet.mem_supₛ_iff

@[simp]
theorem mem_infₛ_iff : a ∈ infₛ S ↔ ∃ s ∈ S, a ∈ s :=
  mem_unionᵢ₂
#align upper_set.mem_Inf_iff UpperSet.mem_infₛ_iff

@[simp]
theorem mem_supᵢ_iff {f : ι → UpperSet α} : (a ∈ ⨆ i, f i) ↔ ∀ i, a ∈ f i :=
  by
  rw [← SetLike.mem_coe, coe_supr]
  exact mem_Inter
#align upper_set.mem_supr_iff UpperSet.mem_supᵢ_iff

@[simp]
theorem mem_infᵢ_iff {f : ι → UpperSet α} : (a ∈ ⨅ i, f i) ↔ ∃ i, a ∈ f i :=
  by
  rw [← SetLike.mem_coe, coe_infi]
  exact mem_Union
#align upper_set.mem_infi_iff UpperSet.mem_infᵢ_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem mem_supr₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_supr_iff]
#align upper_set.mem_supr₂_iff UpperSet.mem_supr₂_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem mem_infi₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_infi_iff]
#align upper_set.mem_infi₂_iff UpperSet.mem_infi₂_iff

@[simp, norm_cast]
theorem codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]
#align upper_set.codisjoint_coe UpperSet.codisjoint_coe

end UpperSet

namespace LowerSet

variable {S : Set (LowerSet α)} {s t : LowerSet α} {a : α}

instance : HasSup (LowerSet α) :=
  ⟨fun s t => ⟨s ∪ t, fun a b h => Or.imp (s.lower h) (t.lower h)⟩⟩

instance : HasInf (LowerSet α) :=
  ⟨fun s t => ⟨s ∩ t, fun a b h => And.imp (s.lower h) (t.lower h)⟩⟩

instance : Top (LowerSet α) :=
  ⟨⟨univ, fun a b h => id⟩⟩

instance : Bot (LowerSet α) :=
  ⟨⟨∅, fun a b h => id⟩⟩

instance : SupSet (LowerSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isLowerSet_Union₂ fun s _ => s.lower⟩⟩

instance : InfSet (LowerSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isLowerSet_Inter₂ fun s _ => s.lower⟩⟩

instance : CompleteDistribLattice (LowerSet α) :=
  SetLike.coe_injective.CompleteDistribLattice _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl

instance : Inhabited (LowerSet α) :=
  ⟨⊥⟩

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  Iff.rfl
#align lower_set.coe_subset_coe LowerSet.coe_subset_coe

@[simp, norm_cast]
theorem coe_top : ((⊤ : LowerSet α) : Set α) = univ :=
  rfl
#align lower_set.coe_top LowerSet.coe_top

@[simp, norm_cast]
theorem coe_bot : ((⊥ : LowerSet α) : Set α) = ∅ :=
  rfl
#align lower_set.coe_bot LowerSet.coe_bot

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊤ := by simp [SetLike.ext'_iff]
#align lower_set.coe_eq_univ LowerSet.coe_eq_univ

@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊥ := by simp [SetLike.ext'_iff]
#align lower_set.coe_eq_empty LowerSet.coe_eq_empty

@[simp, norm_cast]
theorem coe_sup (s t : LowerSet α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align lower_set.coe_sup LowerSet.coe_sup

@[simp, norm_cast]
theorem coe_inf (s t : LowerSet α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align lower_set.coe_inf LowerSet.coe_inf

@[simp, norm_cast]
theorem coe_supₛ (S : Set (LowerSet α)) : (↑(supₛ S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl
#align lower_set.coe_Sup LowerSet.coe_supₛ

@[simp, norm_cast]
theorem coe_infₛ (S : Set (LowerSet α)) : (↑(infₛ S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl
#align lower_set.coe_Inf LowerSet.coe_infₛ

@[simp, norm_cast]
theorem coe_supᵢ (f : ι → LowerSet α) : (↑(⨆ i, f i) : Set α) = ⋃ i, f i := by
  simp_rw [supᵢ, coe_Sup, mem_range, Union_exists, Union_Union_eq']
#align lower_set.coe_supr LowerSet.coe_supᵢ

@[simp, norm_cast]
theorem coe_infᵢ (f : ι → LowerSet α) : (↑(⨅ i, f i) : Set α) = ⋂ i, f i := by
  simp_rw [infᵢ, coe_Inf, mem_range, Inter_exists, Inter_Inter_eq']
#align lower_set.coe_infi LowerSet.coe_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_supr₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j :=
  by simp_rw [coe_supr]
#align lower_set.coe_supr₂ LowerSet.coe_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_infi₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j :=
  by simp_rw [coe_infi]
#align lower_set.coe_infi₂ LowerSet.coe_infi₂

@[simp]
theorem mem_top : a ∈ (⊤ : LowerSet α) :=
  trivial
#align lower_set.mem_top LowerSet.mem_top

@[simp]
theorem not_mem_bot : a ∉ (⊥ : LowerSet α) :=
  id
#align lower_set.not_mem_bot LowerSet.not_mem_bot

@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl
#align lower_set.mem_sup_iff LowerSet.mem_sup_iff

@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl
#align lower_set.mem_inf_iff LowerSet.mem_inf_iff

@[simp]
theorem mem_supₛ_iff : a ∈ supₛ S ↔ ∃ s ∈ S, a ∈ s :=
  mem_unionᵢ₂
#align lower_set.mem_Sup_iff LowerSet.mem_supₛ_iff

@[simp]
theorem mem_infₛ_iff : a ∈ infₛ S ↔ ∀ s ∈ S, a ∈ s :=
  mem_interᵢ₂
#align lower_set.mem_Inf_iff LowerSet.mem_infₛ_iff

@[simp]
theorem mem_supᵢ_iff {f : ι → LowerSet α} : (a ∈ ⨆ i, f i) ↔ ∃ i, a ∈ f i :=
  by
  rw [← SetLike.mem_coe, coe_supr]
  exact mem_Union
#align lower_set.mem_supr_iff LowerSet.mem_supᵢ_iff

@[simp]
theorem mem_infᵢ_iff {f : ι → LowerSet α} : (a ∈ ⨅ i, f i) ↔ ∀ i, a ∈ f i :=
  by
  rw [← SetLike.mem_coe, coe_infi]
  exact mem_Inter
#align lower_set.mem_infi_iff LowerSet.mem_infᵢ_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem mem_supr₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_supr_iff]
#align lower_set.mem_supr₂_iff LowerSet.mem_supr₂_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem mem_infi₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_infi_iff]
#align lower_set.mem_infi₂_iff LowerSet.mem_infi₂_iff

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, SetLike.ext'_iff]
#align lower_set.disjoint_coe LowerSet.disjoint_coe

end LowerSet

/-! #### Complement -/


/-- The complement of a lower set as an upper set. -/
def UpperSet.compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩
#align upper_set.compl UpperSet.compl

/-- The complement of a lower set as an upper set. -/
def LowerSet.compl (s : LowerSet α) : UpperSet α :=
  ⟨sᶜ, s.lower.compl⟩
#align lower_set.compl LowerSet.compl

namespace UpperSet

variable {s t : UpperSet α} {a : α}

@[simp]
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = sᶜ :=
  rfl
#align upper_set.coe_compl UpperSet.coe_compl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl
#align upper_set.mem_compl_iff UpperSet.mem_compl_iff

@[simp]
theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
  UpperSet.ext <| compl_compl _
#align upper_set.compl_compl UpperSet.compl_compl

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl
#align upper_set.compl_le_compl UpperSet.compl_le_compl

@[simp]
protected theorem compl_sup (s t : UpperSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  LowerSet.ext compl_inf
#align upper_set.compl_sup UpperSet.compl_sup

@[simp]
protected theorem compl_inf (s t : UpperSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  LowerSet.ext compl_sup
#align upper_set.compl_inf UpperSet.compl_inf

@[simp]
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty
#align upper_set.compl_top UpperSet.compl_top

@[simp]
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ
#align upper_set.compl_bot UpperSet.compl_bot

@[simp]
protected theorem compl_supₛ (S : Set (UpperSet α)) : (supₛ S).compl = ⨆ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_Sup, compl_Inter₂, LowerSet.coe_supr₂]
#align upper_set.compl_Sup UpperSet.compl_supₛ

@[simp]
protected theorem compl_infₛ (S : Set (UpperSet α)) : (infₛ S).compl = ⨅ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_Inf, compl_Union₂, LowerSet.coe_infi₂]
#align upper_set.compl_Inf UpperSet.compl_infₛ

@[simp]
protected theorem compl_supᵢ (f : ι → UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_supr, compl_Inter, LowerSet.coe_supᵢ]
#align upper_set.compl_supr UpperSet.compl_supᵢ

@[simp]
protected theorem compl_infᵢ (f : ι → UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_infi, compl_Union, LowerSet.coe_infᵢ]
#align upper_set.compl_infi UpperSet.compl_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem compl_supr₂ (f : ∀ i, κ i → UpperSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [UpperSet.compl_supᵢ]
#align upper_set.compl_supr₂ UpperSet.compl_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem compl_infi₂ (f : ∀ i, κ i → UpperSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [UpperSet.compl_infᵢ]
#align upper_set.compl_infi₂ UpperSet.compl_infi₂

end UpperSet

namespace LowerSet

variable {s t : LowerSet α} {a : α}

@[simp]
theorem coe_compl (s : LowerSet α) : (s.compl : Set α) = sᶜ :=
  rfl
#align lower_set.coe_compl LowerSet.coe_compl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl
#align lower_set.mem_compl_iff LowerSet.mem_compl_iff

@[simp]
theorem compl_compl (s : LowerSet α) : s.compl.compl = s :=
  LowerSet.ext <| compl_compl _
#align lower_set.compl_compl LowerSet.compl_compl

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl
#align lower_set.compl_le_compl LowerSet.compl_le_compl

protected theorem compl_sup (s t : LowerSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  UpperSet.ext compl_sup
#align lower_set.compl_sup LowerSet.compl_sup

protected theorem compl_inf (s t : LowerSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  UpperSet.ext compl_inf
#align lower_set.compl_inf LowerSet.compl_inf

protected theorem compl_top : (⊤ : LowerSet α).compl = ⊤ :=
  UpperSet.ext compl_univ
#align lower_set.compl_top LowerSet.compl_top

protected theorem compl_bot : (⊥ : LowerSet α).compl = ⊥ :=
  UpperSet.ext compl_empty
#align lower_set.compl_bot LowerSet.compl_bot

protected theorem compl_supₛ (S : Set (LowerSet α)) : (supₛ S).compl = ⨆ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_Sup, compl_Union₂, UpperSet.coe_supr₂]
#align lower_set.compl_Sup LowerSet.compl_supₛ

protected theorem compl_infₛ (S : Set (LowerSet α)) : (infₛ S).compl = ⨅ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_Inf, compl_Inter₂, UpperSet.coe_infi₂]
#align lower_set.compl_Inf LowerSet.compl_infₛ

protected theorem compl_supᵢ (f : ι → LowerSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_supr, compl_Union, UpperSet.coe_supᵢ]
#align lower_set.compl_supr LowerSet.compl_supᵢ

protected theorem compl_infᵢ (f : ι → LowerSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_infi, compl_Inter, UpperSet.coe_infᵢ]
#align lower_set.compl_infi LowerSet.compl_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem compl_supr₂ (f : ∀ i, κ i → LowerSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_supᵢ]
#align lower_set.compl_supr₂ LowerSet.compl_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem compl_infi₂ (f : ∀ i, κ i → LowerSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_infᵢ]
#align lower_set.compl_infi₂ LowerSet.compl_infi₂

end LowerSet

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
def upperSetIsoLowerSet : UpperSet α ≃o LowerSet α
    where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' _ _ := UpperSet.compl_le_compl
#align upper_set_iso_lower_set upperSetIsoLowerSet

end LE

/-! #### Map -/


section

variable [Preorder α] [Preorder β] [Preorder γ]

namespace UpperSet

variable {f : α ≃o β} {s t : UpperSet α} {a : α} {b : β}

/-- An order isomorphism of preorders induces an order isomorphism of their upper sets. -/
def map (f : α ≃o β) : UpperSet α ≃o UpperSet β
    where
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.Preimage f.Monotone⟩
  left_inv _ := ext <| f.preimage_image _
  right_inv _ := ext <| f.image_preimage _
  map_rel_iff' s t := image_subset_image_iff f.Injective
#align upper_set.map UpperSet.map

@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  FunLike.ext _ _ fun s => ext <| Set.preimage_equiv_eq_image_symm _ _
#align upper_set.symm_map UpperSet.symm_map

@[simp]
theorem mem_map : b ∈ map f s ↔ f.symm b ∈ s :=
  by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl
#align upper_set.mem_map UpperSet.mem_map

@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ :=
  by
  ext
  simp
#align upper_set.map_refl UpperSet.map_refl

@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s :=
  by
  ext
  simp
#align upper_set.map_map UpperSet.map_map

variable (f s t)

@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl
#align upper_set.coe_map UpperSet.coe_map

end UpperSet

namespace LowerSet

variable {f : α ≃o β} {s t : LowerSet α} {a : α} {b : β}

/-- An order isomorphism of preorders induces an order isomorphism of their lower sets. -/
def map (f : α ≃o β) : LowerSet α ≃o LowerSet β
    where
  toFun s := ⟨f '' s, s.lower.image f⟩
  invFun t := ⟨f ⁻¹' t, t.lower.Preimage f.Monotone⟩
  left_inv _ := SetLike.coe_injective <| f.preimage_image _
  right_inv _ := SetLike.coe_injective <| f.image_preimage _
  map_rel_iff' s t := image_subset_image_iff f.Injective
#align lower_set.map LowerSet.map

@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  FunLike.ext _ _ fun s => SetLike.coe_injective <| Set.preimage_equiv_eq_image_symm _ _
#align lower_set.symm_map LowerSet.symm_map

@[simp]
theorem mem_map {f : α ≃o β} {b : β} : b ∈ map f s ↔ f.symm b ∈ s :=
  by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl
#align lower_set.mem_map LowerSet.mem_map

@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ :=
  by
  ext
  simp
#align lower_set.map_refl LowerSet.map_refl

@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s :=
  by
  ext
  simp
#align lower_set.map_map LowerSet.map_map

variable (f s t)

@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl
#align lower_set.coe_map LowerSet.coe_map

end LowerSet

namespace UpperSet

@[simp]
theorem compl_map (f : α ≃o β) (s : UpperSet α) : (map f s).compl = LowerSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.Bijective).symm
#align upper_set.compl_map UpperSet.compl_map

end UpperSet

namespace LowerSet

@[simp]
theorem compl_map (f : α ≃o β) (s : LowerSet α) : (map f s).compl = UpperSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.Bijective).symm
#align lower_set.compl_map LowerSet.compl_map

end LowerSet

end

/-! #### Principal sets -/


namespace UpperSet

section Preorder

variable [Preorder α] [Preorder β] {s : UpperSet α} {a b : α}

/-- The smallest upper set containing a given element. -/
def ici (a : α) : UpperSet α :=
  ⟨Ici a, isUpperSet_Ici a⟩
#align upper_set.Ici UpperSet.ici

/-- The smallest upper set containing a given element. -/
def ioi (a : α) : UpperSet α :=
  ⟨Ioi a, isUpperSet_Ioi a⟩
#align upper_set.Ioi UpperSet.ioi

@[simp]
theorem coe_ici (a : α) : ↑(ici a) = Set.Ici a :=
  rfl
#align upper_set.coe_Ici UpperSet.coe_ici

@[simp]
theorem coe_ioi (a : α) : ↑(ioi a) = Set.Ioi a :=
  rfl
#align upper_set.coe_Ioi UpperSet.coe_ioi

@[simp]
theorem mem_ici_iff : b ∈ ici a ↔ a ≤ b :=
  Iff.rfl
#align upper_set.mem_Ici_iff UpperSet.mem_ici_iff

@[simp]
theorem mem_ioi_iff : b ∈ ioi a ↔ a < b :=
  Iff.rfl
#align upper_set.mem_Ioi_iff UpperSet.mem_ioi_iff

@[simp]
theorem map_ici (f : α ≃o β) (a : α) : map f (ici a) = ici (f a) :=
  by
  ext
  simp
#align upper_set.map_Ici UpperSet.map_ici

@[simp]
theorem map_ioi (f : α ≃o β) (a : α) : map f (ioi a) = ioi (f a) :=
  by
  ext
  simp
#align upper_set.map_Ioi UpperSet.map_ioi

theorem ici_le_ioi (a : α) : ici a ≤ ioi a :=
  Ioi_subset_Ici_self
#align upper_set.Ici_le_Ioi UpperSet.ici_le_ioi

@[simp]
theorem ioi_top [OrderTop α] : ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top
#align upper_set.Ioi_top UpperSet.ioi_top

@[simp]
theorem ici_bot [OrderBot α] : ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot
#align upper_set.Ici_bot UpperSet.ici_bot

end Preorder

@[simp]
theorem ici_sup [SemilatticeSup α] (a b : α) : ici (a ⊔ b) = ici a ⊔ ici b :=
  ext Ici_inter_Ici.symm
#align upper_set.Ici_sup UpperSet.ici_sup

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem ici_supₛ (S : Set α) : ici (supₛ S) = ⨆ a ∈ S, ici a :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_supr_iff, supₛ_le_iff]
#align upper_set.Ici_Sup UpperSet.ici_supₛ

@[simp]
theorem ici_supᵢ (f : ι → α) : ici (⨆ i, f i) = ⨆ i, ici (f i) :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_supr_iff, supᵢ_le_iff]
#align upper_set.Ici_supr UpperSet.ici_supᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem ici_supr₂ (f : ∀ i, κ i → α) : ici (⨆ (i) (j), f i j) = ⨆ (i) (j), ici (f i j) := by
  simp_rw [Ici_supr]
#align upper_set.Ici_supr₂ UpperSet.ici_supr₂

end CompleteLattice

end UpperSet

namespace LowerSet

section Preorder

variable [Preorder α] [Preorder β] {s : LowerSet α} {a b : α}

/-- Principal lower set. `set.Iic` as a lower set. The smallest lower set containing a given
element. -/
def iic (a : α) : LowerSet α :=
  ⟨Iic a, isLowerSet_Iic a⟩
#align lower_set.Iic LowerSet.iic

/-- Strict principal lower set. `set.Iio` as a lower set. -/
def iio (a : α) : LowerSet α :=
  ⟨Iio a, isLowerSet_Iio a⟩
#align lower_set.Iio LowerSet.iio

@[simp]
theorem coe_iic (a : α) : ↑(iic a) = Set.Iic a :=
  rfl
#align lower_set.coe_Iic LowerSet.coe_iic

@[simp]
theorem coe_iio (a : α) : ↑(iio a) = Set.Iio a :=
  rfl
#align lower_set.coe_Iio LowerSet.coe_iio

@[simp]
theorem mem_iic_iff : b ∈ iic a ↔ b ≤ a :=
  Iff.rfl
#align lower_set.mem_Iic_iff LowerSet.mem_iic_iff

@[simp]
theorem mem_iio_iff : b ∈ iio a ↔ b < a :=
  Iff.rfl
#align lower_set.mem_Iio_iff LowerSet.mem_iio_iff

@[simp]
theorem map_iic (f : α ≃o β) (a : α) : map f (iic a) = iic (f a) :=
  by
  ext
  simp
#align lower_set.map_Iic LowerSet.map_iic

@[simp]
theorem map_iio (f : α ≃o β) (a : α) : map f (iio a) = iio (f a) :=
  by
  ext
  simp
#align lower_set.map_Iio LowerSet.map_iio

theorem Ioi_le_Ici (a : α) : Ioi a ≤ Ici a :=
  Ioi_subset_Ici_self
#align lower_set.Ioi_le_Ici LowerSet.Ioi_le_Ici

@[simp]
theorem iic_top [OrderTop α] : iic (⊤ : α) = ⊤ :=
  SetLike.coe_injective Iic_top
#align lower_set.Iic_top LowerSet.iic_top

@[simp]
theorem iio_bot [OrderBot α] : iio (⊥ : α) = ⊥ :=
  SetLike.coe_injective Iio_bot
#align lower_set.Iio_bot LowerSet.iio_bot

end Preorder

@[simp]
theorem iic_inf [SemilatticeInf α] (a b : α) : iic (a ⊓ b) = iic a ⊓ iic b :=
  SetLike.coe_injective Iic_inter_Iic.symm
#align lower_set.Iic_inf LowerSet.iic_inf

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem iic_infₛ (S : Set α) : iic (infₛ S) = ⨅ a ∈ S, iic a :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_infi₂_iff, le_infₛ_iff]
#align lower_set.Iic_Inf LowerSet.iic_infₛ

@[simp]
theorem iic_infᵢ (f : ι → α) : iic (⨅ i, f i) = ⨅ i, iic (f i) :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_infi_iff, le_infᵢ_iff]
#align lower_set.Iic_infi LowerSet.iic_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem iic_infi₂ (f : ∀ i, κ i → α) : iic (⨅ (i) (j), f i j) = ⨅ (i) (j), iic (f i j) := by
  simp_rw [Iic_infi]
#align lower_set.Iic_infi₂ LowerSet.iic_infi₂

end CompleteLattice

end LowerSet

section closure

variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

/-- The greatest upper set containing a given set. -/
def upperClosure (s : Set α) : UpperSet α :=
  ⟨{ x | ∃ a ∈ s, a ≤ x }, fun x y h => Exists₂.imp fun a _ => h.trans'⟩
#align upper_closure upperClosure

/-- The least lower set containing a given set. -/
def lowerClosure (s : Set α) : LowerSet α :=
  ⟨{ x | ∃ a ∈ s, x ≤ a }, fun x y h => Exists₂.imp fun a _ => h.trans⟩
#align lower_closure lowerClosure

@[simp]
theorem mem_upperClosure : x ∈ upperClosure s ↔ ∃ a ∈ s, a ≤ x :=
  Iff.rfl
#align mem_upper_closure mem_upperClosure

@[simp]
theorem mem_lowerClosure : x ∈ lowerClosure s ↔ ∃ a ∈ s, x ≤ a :=
  Iff.rfl
#align mem_lower_closure mem_lowerClosure

-- We do not tag those two as `simp` to respect the abstraction.
@[norm_cast]
theorem coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a ∈ s, Ici a :=
  by
  ext
  simp
#align coe_upper_closure coe_upperClosure

@[norm_cast]
theorem coe_lowerClosure (s : Set α) : ↑(lowerClosure s) = ⋃ a ∈ s, Iic a :=
  by
  ext
  simp
#align coe_lower_closure coe_lowerClosure

theorem subset_upperClosure : s ⊆ upperClosure s := fun x hx => ⟨x, hx, le_rfl⟩
#align subset_upper_closure subset_upperClosure

theorem subset_lowerClosure : s ⊆ lowerClosure s := fun x hx => ⟨x, hx, le_rfl⟩
#align subset_lower_closure subset_lowerClosure

theorem upperClosure_min (h : s ⊆ t) (ht : IsUpperSet t) : ↑(upperClosure s) ⊆ t :=
  fun a ⟨b, hb, hba⟩ => ht hba <| h hb
#align upper_closure_min upperClosure_min

theorem lowerClosure_min (h : s ⊆ t) (ht : IsLowerSet t) : ↑(lowerClosure s) ⊆ t :=
  fun a ⟨b, hb, hab⟩ => ht hab <| h hb
#align lower_closure_min lowerClosure_min

protected theorem IsUpperSet.upperClosure (hs : IsUpperSet s) : ↑(upperClosure s) = s :=
  (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure
#align is_upper_set.upper_closure IsUpperSet.upperClosure

protected theorem IsLowerSet.lowerClosure (hs : IsLowerSet s) : ↑(lowerClosure s) = s :=
  (lowerClosure_min Subset.rfl hs).antisymm subset_lowerClosure
#align is_lower_set.lower_closure IsLowerSet.lowerClosure

@[simp]
protected theorem UpperSet.upperClosure (s : UpperSet α) : upperClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.upperClosure
#align upper_set.upper_closure UpperSet.upperClosure

@[simp]
protected theorem LowerSet.lowerClosure (s : LowerSet α) : lowerClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.lowerClosure
#align lower_set.lower_closure LowerSet.lowerClosure

@[simp]
theorem upperClosure_image (f : α ≃o β) : upperClosure (f '' s) = UpperSet.map f (upperClosure s) :=
  by
  rw [← f.symm_symm, ← UpperSet.symm_map, f.symm_symm]
  ext
  simp [-UpperSet.symm_map, UpperSet.map, OrderIso.symm, ← f.le_symm_apply]
#align upper_closure_image upperClosure_image

@[simp]
theorem lowerClosure_image (f : α ≃o β) : lowerClosure (f '' s) = LowerSet.map f (lowerClosure s) :=
  by
  rw [← f.symm_symm, ← LowerSet.symm_map, f.symm_symm]
  ext
  simp [-LowerSet.symm_map, LowerSet.map, OrderIso.symm, ← f.symm_apply_le]
#align lower_closure_image lowerClosure_image

@[simp]
theorem UpperSet.infᵢ_ici (s : Set α) : (⨅ a ∈ s, UpperSet.ici a) = upperClosure s :=
  by
  ext
  simp
#align upper_set.infi_Ici UpperSet.infᵢ_ici

@[simp]
theorem LowerSet.supᵢ_iic (s : Set α) : (⨆ a ∈ s, LowerSet.iic a) = lowerClosure s :=
  by
  ext
  simp
#align lower_set.supr_Iic LowerSet.supᵢ_iic

theorem gc_upperClosure_coe :
    GaloisConnection (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) (coe ∘ ofDual) := fun s t =>
  ⟨fun h => subset_upperClosure.trans <| UpperSet.coe_subset_coe.2 h, fun h =>
    upperClosure_min h t.upper⟩
#align gc_upper_closure_coe gc_upperClosure_coe

theorem gc_lowerClosure_coe : GaloisConnection (lowerClosure : Set α → LowerSet α) coe := fun s t =>
  ⟨fun h => subset_lowerClosure.trans <| LowerSet.coe_subset_coe.2 h, fun h =>
    lowerClosure_min h t.lower⟩
#align gc_lower_closure_coe gc_lowerClosure_coe

/-- `upper_closure` forms a reversed Galois insertion with the coercion from upper sets to sets. -/
def giUpperClosureCoe :
    GaloisInsertion (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) (coe ∘ ofDual)
    where
  choice s hs := toDual (⟨s, fun a b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
  choice_eq s hs := ofDual.Injective <| SetLike.coe_injective <| subset_upperClosure.antisymm hs
#align gi_upper_closure_coe giUpperClosureCoe

/-- `lower_closure` forms a Galois insertion with the coercion from lower sets to sets. -/
def giLowerClosureCoe : GaloisInsertion (lowerClosure : Set α → LowerSet α) coe
    where
  choice s hs := ⟨s, fun a b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
  choice_eq s hs := SetLike.coe_injective <| subset_lowerClosure.antisymm hs
#align gi_lower_closure_coe giLowerClosureCoe

theorem upperClosure_anti : Antitone (upperClosure : Set α → UpperSet α) :=
  gc_upperClosure_coe.monotone_l
#align upper_closure_anti upperClosure_anti

theorem lowerClosure_mono : Monotone (lowerClosure : Set α → LowerSet α) :=
  gc_lowerClosure_coe.monotone_l
#align lower_closure_mono lowerClosure_mono

@[simp]
theorem upperClosure_empty : upperClosure (∅ : Set α) = ⊤ :=
  by
  ext
  simp
#align upper_closure_empty upperClosure_empty

@[simp]
theorem lowerClosure_empty : lowerClosure (∅ : Set α) = ⊥ :=
  by
  ext
  simp
#align lower_closure_empty lowerClosure_empty

@[simp]
theorem upperClosure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.ici a :=
  by
  ext
  simp
#align upper_closure_singleton upperClosure_singleton

@[simp]
theorem lowerClosure_singleton (a : α) : lowerClosure ({a} : Set α) = LowerSet.iic a :=
  by
  ext
  simp
#align lower_closure_singleton lowerClosure_singleton

@[simp]
theorem upperClosure_univ : upperClosure (univ : Set α) = ⊥ :=
  le_bot_iff.1 subset_upperClosure
#align upper_closure_univ upperClosure_univ

@[simp]
theorem lowerClosure_univ : lowerClosure (univ : Set α) = ⊤ :=
  top_le_iff.1 subset_lowerClosure
#align lower_closure_univ lowerClosure_univ

@[simp]
theorem upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅ :=
  ⟨fun h => subset_empty_iff.1 <| subset_upperClosure.trans (congr_arg coe h).Subset,
    by
    rintro rfl
    exact upperClosure_empty⟩
#align upper_closure_eq_top_iff upperClosure_eq_top_iff

@[simp]
theorem lowerClosure_eq_bot_iff : lowerClosure s = ⊥ ↔ s = ∅ :=
  ⟨fun h => subset_empty_iff.1 <| subset_lowerClosure.trans (congr_arg coe h).Subset,
    by
    rintro rfl
    exact lowerClosure_empty⟩
#align lower_closure_eq_bot_iff lowerClosure_eq_bot_iff

@[simp]
theorem upperClosure_union (s t : Set α) : upperClosure (s ∪ t) = upperClosure s ⊓ upperClosure t :=
  by
  ext
  simp [or_and_right, exists_or]
#align upper_closure_union upperClosure_union

@[simp]
theorem lowerClosure_union (s t : Set α) : lowerClosure (s ∪ t) = lowerClosure s ⊔ lowerClosure t :=
  by
  ext
  simp [or_and_right, exists_or]
#align lower_closure_union lowerClosure_union

@[simp]
theorem upperClosure_unionᵢ (f : ι → Set α) : upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i) :=
  by
  ext
  simp [← exists_and_right, @exists_comm α]
#align upper_closure_Union upperClosure_unionᵢ

@[simp]
theorem lowerClosure_unionᵢ (f : ι → Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i) :=
  by
  ext
  simp [← exists_and_right, @exists_comm α]
#align lower_closure_Union lowerClosure_unionᵢ

@[simp]
theorem upperClosure_unionₛ (S : Set (Set α)) : upperClosure (⋃₀ S) = ⨅ s ∈ S, upperClosure s := by
  simp_rw [sUnion_eq_bUnion, upperClosure_unionᵢ]
#align upper_closure_sUnion upperClosure_unionₛ

@[simp]
theorem lowerClosure_unionₛ (S : Set (Set α)) : lowerClosure (⋃₀ S) = ⨆ s ∈ S, lowerClosure s := by
  simp_rw [sUnion_eq_bUnion, lowerClosure_unionᵢ]
#align lower_closure_sUnion lowerClosure_unionₛ

theorem Set.OrdConnected.upperClosure_inter_lowerClosure (h : s.OrdConnected) :
    ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun a ⟨⟨b, hb, hba⟩, c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩
#align set.ord_connected.upper_closure_inter_lower_closure Set.OrdConnected.upperClosure_inter_lowerClosure

theorem ordConnected_iff_upperClosure_inter_lowerClosure :
    s.OrdConnected ↔ ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  by
  refine' ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => _⟩
  rw [← h]
  exact (UpperSet.upper _).OrdConnected.inter (LowerSet.lower _).OrdConnected
#align ord_connected_iff_upper_closure_inter_lower_closure ordConnected_iff_upperClosure_inter_lowerClosure

end closure

/-! ### Product -/


section Preorder

variable [Preorder α] [Preorder β]

section

variable {s : Set α} {t : Set β} {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ t) :=
  fun a b h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
#align is_upper_set.prod IsUpperSet.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ t) :=
  fun a b h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
#align is_lower_set.prod IsLowerSet.prod

end

namespace UpperSet

variable (s s₁ s₂ : UpperSet α) (t t₁ t₂ : UpperSet β) {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two upper sets as an upper set. -/
def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.Prod t.2⟩
#align upper_set.prod UpperSet.prod

-- mathport name: upper_set.prod
infixr:82 " ×ˢ " => prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, norm_cast]
theorem coe_prod : (↑(s ×ˢ t) : Set (α × β)) = s ×ˢ t :=
  rfl
#align upper_set.coe_prod UpperSet.coe_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mem_prod {s : UpperSet α} {t : UpperSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl
#align upper_set.mem_prod UpperSet.mem_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ici_prod (x : α × β) : ici x = ici x.1 ×ˢ ici x.2 :=
  rfl
#align upper_set.Ici_prod UpperSet.ici_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem ici_prod_ici (a : α) (b : β) : ici a ×ˢ ici b = ici (a, b) :=
  rfl
#align upper_set.Ici_prod_Ici UpperSet.ici_prod_ici

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_top : s ×ˢ (⊤ : UpperSet β) = ⊤ :=
  ext prod_empty
#align upper_set.prod_top UpperSet.prod_top

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem top_prod : (⊤ : UpperSet α) ×ˢ t = ⊤ :=
  ext empty_prod
#align upper_set.top_prod UpperSet.top_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bot_prod_bot : (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥ :=
  ext univ_prod_univ
#align upper_set.bot_prod_bot UpperSet.bot_prod_bot

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext inter_prod
#align upper_set.sup_prod UpperSet.sup_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_inter
#align upper_set.prod_sup UpperSet.prod_sup

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext union_prod
#align upper_set.inf_prod UpperSet.inf_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_union
#align upper_set.prod_inf UpperSet.prod_inf

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂) :=
  ext prod_inter_prod
#align upper_set.prod_sup_prod UpperSet.prod_sup_prod

variable {s s₁ s₂ t t₁ t₂}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  prod_mono
#align upper_set.prod_mono UpperSet.prod_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  prod_mono_left
#align upper_set.prod_mono_left UpperSet.prod_mono_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  prod_mono_right
#align upper_set.prod_mono_right UpperSet.prod_mono_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self
#align upper_set.prod_self_le_prod_self UpperSet.prod_self_le_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self
#align upper_set.prod_self_lt_prod_self UpperSet.prod_self_lt_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤ :=
  prod_subset_prod_iff.trans <| by simp
#align upper_set.prod_le_prod_iff UpperSet.prod_le_prod_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤ :=
  by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff
#align upper_set.prod_eq_top UpperSet.prod_eq_top

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem codisjoint_prod : Codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Codisjoint s₁ s₂ ∨ Codisjoint t₁ t₂ :=
  by simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]
#align upper_set.codisjoint_prod UpperSet.codisjoint_prod

end UpperSet

namespace LowerSet

variable (s s₁ s₂ : LowerSet α) (t t₁ t₂ : LowerSet β) {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two lower sets as a lower set. -/
def prod : LowerSet (α × β) :=
  ⟨s ×ˢ t, s.2.Prod t.2⟩
#align lower_set.prod LowerSet.prod

-- mathport name: lower_set.prod
infixr:82 " ×ˢ " => LowerSet.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, norm_cast]
theorem coe_prod : (↑(s ×ˢ t) : Set (α × β)) = s ×ˢ t :=
  rfl
#align lower_set.coe_prod LowerSet.coe_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mem_prod {s : LowerSet α} {t : LowerSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl
#align lower_set.mem_prod LowerSet.mem_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem iic_prod (x : α × β) : iic x = iic x.1 ×ˢ iic x.2 :=
  rfl
#align lower_set.Iic_prod LowerSet.iic_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : iic a ×ˢ iic b = iic (a, b) :=
  rfl
#align lower_set.Ici_prod_Ici LowerSet.Ici_prod_Ici

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_bot : s ×ˢ (⊥ : LowerSet β) = ⊥ :=
  ext prod_empty
#align lower_set.prod_bot LowerSet.prod_bot

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bot_prod : (⊥ : LowerSet α) ×ˢ t = ⊥ :=
  ext empty_prod
#align lower_set.bot_prod LowerSet.bot_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem top_prod_top : (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤ :=
  ext univ_prod_univ
#align lower_set.top_prod_top LowerSet.top_prod_top

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext inter_prod
#align lower_set.inf_prod LowerSet.inf_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_inter
#align lower_set.prod_inf LowerSet.prod_inf

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext union_prod
#align lower_set.sup_prod LowerSet.sup_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_union
#align lower_set.prod_sup LowerSet.prod_sup

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂) :=
  ext prod_inter_prod
#align lower_set.prod_inf_prod LowerSet.prod_inf_prod

variable {s s₁ s₂ t t₁ t₂}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  prod_mono
#align lower_set.prod_mono LowerSet.prod_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  prod_mono_left
#align lower_set.prod_mono_left LowerSet.prod_mono_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  prod_mono_right
#align lower_set.prod_mono_right LowerSet.prod_mono_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self
#align lower_set.prod_self_le_prod_self LowerSet.prod_self_le_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self
#align lower_set.prod_self_lt_prod_self LowerSet.prod_self_lt_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥ :=
  prod_subset_prod_iff.trans <| by simp
#align lower_set.prod_le_prod_iff LowerSet.prod_le_prod_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥ :=
  by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff
#align lower_set.prod_eq_bot LowerSet.prod_eq_bot

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]
#align lower_set.disjoint_prod LowerSet.disjoint_prod

end LowerSet

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem upperClosure_prod (s : Set α) (t : Set β) :
    upperClosure (s ×ˢ t) = upperClosure s ×ˢ upperClosure t :=
  by
  ext
  simp [Prod.le_def, and_and_and_comm _ (_ ∈ t)]
#align upper_closure_prod upperClosure_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem lowerClosure_prod (s : Set α) (t : Set β) :
    lowerClosure (s ×ˢ t) = lowerClosure s ×ˢ lowerClosure t :=
  by
  ext
  simp [Prod.le_def, and_and_and_comm _ (_ ∈ t)]
#align lower_closure_prod lowerClosure_prod

end Preorder

