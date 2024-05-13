/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.NAry
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.SupClosed

#align_import data.set.sups from "leanprover-community/mathlib"@"20715f4ac6819ef2453d9e5106ecd086a5dc2a5e"

/-!
# Set family operations

This file defines a few binary operations on `Set α` for use in set family combinatorics.

## Main declarations

* `s ⊻ t`: Set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.

## Notation

We define the following notation in locale `SetFamily`:
* `s ⊻ t`
* `s ⊼ t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/


open Function

variable {F α β : Type*}

/-- Notation typeclass for pointwise supremum `⊻`. -/
class HasSups (α : Type*) where
  /-- The point-wise supremum `a ⊔ b` of `a, b : α`. -/
  sups : α → α → α
#align has_sups HasSups

/-- Notation typeclass for pointwise infimum `⊼`. -/
class HasInfs (α : Type*) where
  /-- The point-wise infimum `a ⊓ b` of `a, b : α`. -/
  infs : α → α → α
#align has_infs HasInfs

-- This notation is meant to have higher precedence than `⊔` and `⊓`, but still within the
-- realm of other binary notation.
@[inherit_doc]
infixl:74 " ⊻ " => HasSups.sups

@[inherit_doc]
infixl:75 " ⊼ " => HasInfs.infs

namespace Set

section Sups
variable [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Set α)

/-- `s ⊻ t` is the set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
protected def hasSups : HasSups (Set α) :=
  ⟨image2 (· ⊔ ·)⟩
#align set.has_sups Set.hasSups

scoped[SetFamily] attribute [instance] Set.hasSups
-- Porting note: opening SetFamily, because otherwise the Set.hasSups does not seem to be an
-- instance
open SetFamily

variable {s s₁ s₂ t t₁ t₂ u} {a b c : α}

@[simp]
lemma mem_sups : c ∈ s ⊻ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊔ b = c := by simp [(· ⊻ ·)]
#align set.mem_sups Set.mem_sups

lemma sup_mem_sups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t :=
  mem_image2_of_mem
#align set.sup_mem_sups Set.sup_mem_sups

lemma sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ :=
  image2_subset
#align set.sups_subset Set.sups_subset

lemma sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ :=
  image2_subset_left
#align set.sups_subset_left Set.sups_subset_left

lemma sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t :=
  image2_subset_right
#align set.sups_subset_right Set.sups_subset_right

lemma image_subset_sups_left : b ∈ t → (fun a => a ⊔ b) '' s ⊆ s ⊻ t :=
  image_subset_image2_left
#align set.image_subset_sups_left Set.image_subset_sups_left

lemma image_subset_sups_right : a ∈ s → (· ⊔ ·) a '' t ⊆ s ⊻ t :=
  image_subset_image2_right
#align set.image_subset_sups_right Set.image_subset_sups_right

lemma forall_sups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊔ b) :=
  forall_image2_iff
#align set.forall_sups_iff Set.forall_sups_iff

@[simp]
lemma sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊔ b ∈ u :=
  image2_subset_iff
#align set.sups_subset_iff Set.sups_subset_iff

@[simp]
lemma sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.sups_nonempty Set.sups_nonempty

protected lemma Nonempty.sups : s.Nonempty → t.Nonempty → (s ⊻ t).Nonempty :=
  Nonempty.image2
#align set.nonempty.sups Set.Nonempty.sups

lemma Nonempty.of_sups_left : (s ⊻ t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_sups_left Set.Nonempty.of_sups_left

lemma Nonempty.of_sups_right : (s ⊻ t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_sups_right Set.Nonempty.of_sups_right

@[simp]
lemma empty_sups : ∅ ⊻ t = ∅ :=
  image2_empty_left
#align set.empty_sups Set.empty_sups

@[simp]
lemma sups_empty : s ⊻ ∅ = ∅ :=
  image2_empty_right
#align set.sups_empty Set.sups_empty

@[simp]
lemma sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.sups_eq_empty Set.sups_eq_empty

@[simp]
lemma singleton_sups : {a} ⊻ t = t.image fun b => a ⊔ b :=
  image2_singleton_left
#align set.singleton_sups Set.singleton_sups

@[simp]
lemma sups_singleton : s ⊻ {b} = s.image fun a => a ⊔ b :=
  image2_singleton_right
#align set.sups_singleton Set.sups_singleton

lemma singleton_sups_singleton : ({a} ⊻ {b} : Set α) = {a ⊔ b} :=
  image2_singleton
#align set.singleton_sups_singleton Set.singleton_sups_singleton

lemma sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t :=
  image2_union_left
#align set.sups_union_left Set.sups_union_left

lemma sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ :=
  image2_union_right
#align set.sups_union_right Set.sups_union_right

lemma sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t :=
  image2_inter_subset_left
#align set.sups_inter_subset_left Set.sups_inter_subset_left

lemma sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ :=
  image2_inter_subset_right
#align set.sups_inter_subset_right Set.sups_inter_subset_right

lemma image_sups (f : F) (s t : Set α) : f '' (s ⊻ t) = f '' s ⊻ f '' t :=
  image_image2_distrib <| map_sup f

lemma subset_sups_self : s ⊆ s ⊻ s := fun _a ha ↦ mem_sups.2 ⟨_, ha, _, ha, sup_idem _⟩
lemma sups_subset_self : s ⊻ s ⊆ s ↔ SupClosed s := sups_subset_iff

@[simp] lemma sups_eq_self : s ⊻ s = s ↔ SupClosed s :=
  subset_sups_self.le.le_iff_eq.symm.trans sups_subset_self

lemma sep_sups_le (s t : Set α) (a : α) :
    {b ∈ s ⊻ t | b ≤ a} = {b ∈ s | b ≤ a} ⊻ {b ∈ t | b ≤ a} := by ext; aesop

variable (s t u)

lemma iUnion_image_sup_left : ⋃ a ∈ s, (· ⊔ ·) a '' t = s ⊻ t :=
  iUnion_image_left _
#align set.Union_image_sup_left Set.iUnion_image_sup_left

lemma iUnion_image_sup_right : ⋃ b ∈ t, (· ⊔ b) '' s = s ⊻ t :=
  iUnion_image_right _
#align set.Union_image_sup_right Set.iUnion_image_sup_right

@[simp]
lemma image_sup_prod (s t : Set α) : Set.image2 (· ⊔ ·) s t = s ⊻ t := rfl
#align set.image_sup_prod Set.image_sup_prod

lemma sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) := image2_assoc sup_assoc
#align set.sups_assoc Set.sups_assoc

lemma sups_comm : s ⊻ t = t ⊻ s := image2_comm sup_comm
#align set.sups_comm Set.sups_comm

lemma sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image2_left_comm sup_left_comm
#align set.sups_left_comm Set.sups_left_comm

lemma sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image2_right_comm sup_right_comm
#align set.sups_right_comm Set.sups_right_comm

lemma sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v) :=
  image2_image2_image2_comm sup_sup_sup_comm
#align set.sups_sups_sups_comm Set.sups_sups_sups_comm

end Sups

section Infs

variable [SemilatticeInf α] [SemilatticeInf β] [FunLike F α β] [InfHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Set α)

/-- `s ⊼ t` is the set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
protected def hasInfs : HasInfs (Set α) :=
  ⟨image2 (· ⊓ ·)⟩
#align set.has_infs Set.hasInfs

scoped[SetFamily] attribute [instance] Set.hasInfs
-- Porting note: opening SetFamily, because otherwise the Set.hasSups does not seem to be an
-- instance
open SetFamily

variable {s s₁ s₂ t t₁ t₂ u} {a b c : α}

@[simp]
lemma mem_infs : c ∈ s ⊼ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊓ b = c := by simp [(· ⊼ ·)]
#align set.mem_infs Set.mem_infs

lemma inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t :=
  mem_image2_of_mem
#align set.inf_mem_infs Set.inf_mem_infs

lemma infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ :=
  image2_subset
#align set.infs_subset Set.infs_subset

lemma infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ :=
  image2_subset_left
#align set.infs_subset_left Set.infs_subset_left

lemma infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t :=
  image2_subset_right
#align set.infs_subset_right Set.infs_subset_right

lemma image_subset_infs_left : b ∈ t → (fun a => a ⊓ b) '' s ⊆ s ⊼ t :=
  image_subset_image2_left
#align set.image_subset_infs_left Set.image_subset_infs_left

lemma image_subset_infs_right : a ∈ s → (a ⊓ ·) '' t ⊆ s ⊼ t :=
  image_subset_image2_right
#align set.image_subset_infs_right Set.image_subset_infs_right

lemma forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊓ b) :=
  forall_image2_iff
#align set.forall_infs_iff Set.forall_infs_iff

@[simp]
lemma infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊓ b ∈ u :=
  image2_subset_iff
#align set.infs_subset_iff Set.infs_subset_iff

@[simp]
lemma infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.infs_nonempty Set.infs_nonempty

protected lemma Nonempty.infs : s.Nonempty → t.Nonempty → (s ⊼ t).Nonempty :=
  Nonempty.image2
#align set.nonempty.infs Set.Nonempty.infs

lemma Nonempty.of_infs_left : (s ⊼ t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_infs_left Set.Nonempty.of_infs_left

lemma Nonempty.of_infs_right : (s ⊼ t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_infs_right Set.Nonempty.of_infs_right

@[simp]
lemma empty_infs : ∅ ⊼ t = ∅ :=
  image2_empty_left
#align set.empty_infs Set.empty_infs

@[simp]
lemma infs_empty : s ⊼ ∅ = ∅ :=
  image2_empty_right
#align set.infs_empty Set.infs_empty

@[simp]
lemma infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.infs_eq_empty Set.infs_eq_empty

@[simp]
lemma singleton_infs : {a} ⊼ t = t.image fun b => a ⊓ b :=
  image2_singleton_left
#align set.singleton_infs Set.singleton_infs

@[simp]
lemma infs_singleton : s ⊼ {b} = s.image fun a => a ⊓ b :=
  image2_singleton_right
#align set.infs_singleton Set.infs_singleton

lemma singleton_infs_singleton : ({a} ⊼ {b} : Set α) = {a ⊓ b} :=
  image2_singleton
#align set.singleton_infs_singleton Set.singleton_infs_singleton

lemma infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t :=
  image2_union_left
#align set.infs_union_left Set.infs_union_left

lemma infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ :=
  image2_union_right
#align set.infs_union_right Set.infs_union_right

lemma infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t :=
  image2_inter_subset_left
#align set.infs_inter_subset_left Set.infs_inter_subset_left

lemma infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ :=
  image2_inter_subset_right
#align set.infs_inter_subset_right Set.infs_inter_subset_right

lemma image_infs (f : F) (s t : Set α) : f '' (s ⊼ t) = f '' s ⊼ f '' t :=
  image_image2_distrib <| map_inf f

lemma subset_infs_self : s ⊆ s ⊼ s := fun _a ha ↦ mem_infs.2 ⟨_, ha, _, ha, inf_idem _⟩
lemma infs_self_subset : s ⊼ s ⊆ s ↔ InfClosed s := infs_subset_iff

@[simp] lemma infs_self : s ⊼ s = s ↔ InfClosed s :=
  subset_infs_self.le.le_iff_eq.symm.trans infs_self_subset

lemma sep_infs_le (s t : Set α) (a : α) :
    {b ∈ s ⊼ t | a ≤ b} = {b ∈ s | a ≤ b} ⊼ {b ∈ t | a ≤ b} := by ext; aesop

variable (s t u)

lemma iUnion_image_inf_left : ⋃ a ∈ s, (a ⊓ ·) '' t = s ⊼ t :=
  iUnion_image_left _
#align set.Union_image_inf_left Set.iUnion_image_inf_left

lemma iUnion_image_inf_right : ⋃ b ∈ t, (· ⊓ b) '' s = s ⊼ t :=
  iUnion_image_right _
#align set.Union_image_inf_right Set.iUnion_image_inf_right

@[simp]
lemma image_inf_prod (s t : Set α) : Set.image2 (fun x x_1 => x ⊓ x_1) s t = s ⊼ t := by
  have : (s ×ˢ t).image (uncurry (· ⊓ ·)) = Set.image2 (fun x x_1 => x ⊓ x_1) s t := by
    simp only [@ge_iff_le, @Set.image_uncurry_prod]
  rw [← this]
  exact image_uncurry_prod _ _ _
#align set.image_inf_prod Set.image_inf_prod

lemma infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) := image2_assoc inf_assoc
#align set.infs_assoc Set.infs_assoc

lemma infs_comm : s ⊼ t = t ⊼ s := image2_comm inf_comm
#align set.infs_comm Set.infs_comm

lemma infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image2_left_comm inf_left_comm
#align set.infs_left_comm Set.infs_left_comm

lemma infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image2_right_comm inf_right_comm
#align set.infs_right_comm Set.infs_right_comm

lemma infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v) :=
  image2_image2_image2_comm inf_inf_inf_comm
#align set.infs_infs_infs_comm Set.infs_infs_infs_comm

end Infs

open SetFamily

section DistribLattice

variable [DistribLattice α] (s t u : Set α)

lemma sups_infs_subset_left : s ⊻ t ⊼ u ⊆ (s ⊻ t) ⊼ (s ⊻ u) :=
  image2_distrib_subset_left sup_inf_left
#align set.sups_infs_subset_left Set.sups_infs_subset_left

lemma sups_infs_subset_right : t ⊼ u ⊻ s ⊆ (t ⊻ s) ⊼ (u ⊻ s) :=
  image2_distrib_subset_right sup_inf_right
#align set.sups_infs_subset_right Set.sups_infs_subset_right

lemma infs_sups_subset_left : s ⊼ (t ⊻ u) ⊆ s ⊼ t ⊻ s ⊼ u :=
  image2_distrib_subset_left inf_sup_left
#align set.infs_sups_subset_left Set.infs_sups_subset_left

lemma infs_sups_subset_right : (t ⊻ u) ⊼ s ⊆ t ⊼ s ⊻ u ⊼ s :=
  image2_distrib_subset_right inf_sup_right
#align set.infs_sups_subset_right Set.infs_sups_subset_right

end DistribLattice

end Set

open SetFamily

@[simp]
lemma upperClosure_sups [SemilatticeSup α] (s t : Set α) :
    upperClosure (s ⊻ t) = upperClosure s ⊔ upperClosure t := by
  ext a
  simp only [SetLike.mem_coe, mem_upperClosure, Set.mem_sups, exists_and_left, exists_prop,
    UpperSet.coe_sup, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, le_sup_left.trans ha⟩, c, hc, le_sup_right.trans ha⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, sup_le hab hac⟩
#align upper_closure_sups upperClosure_sups

@[simp]
lemma lowerClosure_infs [SemilatticeInf α] (s t : Set α) :
    lowerClosure (s ⊼ t) = lowerClosure s ⊓ lowerClosure t := by
  ext a
  simp only [SetLike.mem_coe, mem_lowerClosure, Set.mem_infs, exists_and_left, exists_prop,
    LowerSet.coe_sup, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, ha.trans inf_le_left⟩, c, hc, ha.trans inf_le_right⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, le_inf hab hac⟩
#align lower_closure_infs lowerClosure_infs
