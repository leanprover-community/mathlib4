/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Set.Sups

/-!
# Set family operations

This file defines a few binary operations on `Finset α` for use in set family combinatorics.

## Main declarations

* `Finset.sups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `Finset.infs s t`: Finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
* `Finset.disjSups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a`
  and `b` are disjoint.
* `Finset.diffs`: Finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`.
* `Finset.compls`: Finset of elements of the form `aᶜ` where `a ∈ s`.

## Notation

We define the following notation in scope `FinsetFamily`:
* `s ⊻ t` for `Finset.sups`
* `s ⊼ t` for `Finset.infs`
* `s ○ t` for `Finset.disjSups s t`
* `s \\ t` for `Finset.diffs`
* `sᶜˢ` for `Finset.compls`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

open Function

open SetFamily

variable {F α β : Type*}

namespace Finset

section Sups
variable [DecidableEq α] [DecidableEq β]
variable [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Finset α)

/-- `s ⊻ t` is the finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
protected def hasSups : HasSups (Finset α) :=
  ⟨image₂ (· ⊔ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasSups

open FinsetFamily

variable {s t} {a b c : α}

@[simp]
theorem mem_sups : c ∈ s ⊻ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊔ b = c := by simp [(· ⊻ ·)]

variable (s t)

@[simp, norm_cast]
theorem coe_sups : (↑(s ⊻ t) : Set α) = ↑s ⊻ ↑t :=
  coe_image₂ _ _ _

theorem card_sups_le : #(s ⊻ t) ≤ #s * #t := card_image₂_le _ _ _

theorem card_sups_iff : #(s ⊻ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊔ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}

theorem sup_mem_sups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t :=
  mem_image₂_of_mem

theorem sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ :=
  image₂_subset

theorem sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ :=
  image₂_subset_left

theorem sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t :=
  image₂_subset_right

lemma image_subset_sups_left : b ∈ t → s.image (· ⊔ b) ⊆ s ⊻ t := image_subset_image₂_left

lemma image_subset_sups_right : a ∈ s → t.image (a ⊔ ·) ⊆ s ⊻ t := image_subset_image₂_right

theorem forall_sups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊔ b) :=
  forall_mem_image₂

@[simp]
theorem sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊔ b ∈ u :=
  image₂_subset_iff

@[simp]
theorem sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected theorem Nonempty.sups : s.Nonempty → t.Nonempty → (s ⊻ t).Nonempty :=
  Nonempty.image₂

theorem Nonempty.of_sups_left : (s ⊻ t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left

theorem Nonempty.of_sups_right : (s ⊻ t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
theorem empty_sups : ∅ ⊻ t = ∅ :=
  image₂_empty_left

@[simp]
theorem sups_empty : s ⊻ ∅ = ∅ :=
  image₂_empty_right

@[simp]
theorem sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[simp] lemma singleton_sups : {a} ⊻ t = t.image (a ⊔ ·) := image₂_singleton_left

@[simp] lemma sups_singleton : s ⊻ {b} = s.image (· ⊔ b) := image₂_singleton_right

theorem singleton_sups_singleton : ({a} ⊻ {b} : Finset α) = {a ⊔ b} :=
  image₂_singleton

theorem sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t :=
  image₂_union_left

theorem sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ :=
  image₂_union_right

theorem sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t :=
  image₂_inter_subset_left

theorem sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ :=
  image₂_inter_subset_right

theorem subset_sups {s t : Set α} :
    ↑u ⊆ s ⊻ t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊻ t' :=
  subset_set_image₂

lemma image_sups (f : F) (s t : Finset α) : image f (s ⊻ t) = image f s ⊻ image f t :=
  image_image₂_distrib <| map_sup f

lemma map_sups (f : F) (hf) (s t : Finset α) :
    map ⟨f, hf⟩ (s ⊻ t) = map ⟨f, hf⟩ s ⊻ map ⟨f, hf⟩ t := by
  simpa [map_eq_image] using image_sups f s t

lemma subset_sups_self : s ⊆ s ⊻ s := fun _a ha ↦ mem_sups.2 ⟨_, ha, _, ha, sup_idem _⟩
lemma sups_subset_self : s ⊻ s ⊆ s ↔ SupClosed (s : Set α) := sups_subset_iff
@[simp] lemma sups_eq_self : s ⊻ s = s ↔ SupClosed (s : Set α) := by simp [← coe_inj]

@[simp] lemma univ_sups_univ [Fintype α] : (univ : Finset α) ⊻ univ = univ := by simp

lemma filter_sups_le [DecidableLE α] (s t : Finset α) (a : α) :
    {b ∈ s ⊻ t | b ≤ a} = {b ∈ s | b ≤ a} ⊻ {b ∈ t | b ≤ a} := by
  simp only [← coe_inj, coe_filter, coe_sups, ← mem_coe, Set.sep_sups_le]

variable (s t u)

lemma biUnion_image_sup_left : s.biUnion (fun a ↦ t.image (a ⊔ ·)) = s ⊻ t := biUnion_image_left

lemma biUnion_image_sup_right : t.biUnion (fun b ↦ s.image (· ⊔ b)) = s ⊻ t := biUnion_image_right

theorem image_sup_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊔ ·)) = s ⊻ t :=
  image_uncurry_product _ _ _

theorem sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) := image₂_assoc sup_assoc

theorem sups_comm : s ⊻ t = t ⊻ s := image₂_comm sup_comm

theorem sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image₂_left_comm sup_left_comm

theorem sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image₂_right_comm sup_right_comm

theorem sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v) :=
  image₂_image₂_image₂_comm sup_sup_sup_comm

end Sups

section Infs
variable [DecidableEq α] [DecidableEq β]
variable [SemilatticeInf α] [SemilatticeInf β] [FunLike F α β] [InfHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Finset α)

/-- `s ⊼ t` is the finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
protected def hasInfs : HasInfs (Finset α) :=
  ⟨image₂ (· ⊓ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasInfs

open FinsetFamily

variable {s t} {a b c : α}

@[simp]
theorem mem_infs : c ∈ s ⊼ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊓ b = c := by simp [(· ⊼ ·)]

variable (s t)

@[simp, norm_cast]
theorem coe_infs : (↑(s ⊼ t) : Set α) = ↑s ⊼ ↑t :=
  coe_image₂ _ _ _

theorem card_infs_le : #(s ⊼ t) ≤ #s * #t := card_image₂_le _ _ _

theorem card_infs_iff : #(s ⊼ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊓ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}

theorem inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t :=
  mem_image₂_of_mem

theorem infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ :=
  image₂_subset

theorem infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ :=
  image₂_subset_left

theorem infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t :=
  image₂_subset_right

lemma image_subset_infs_left : b ∈ t → s.image (· ⊓ b) ⊆ s ⊼ t := image_subset_image₂_left

lemma image_subset_infs_right : a ∈ s → t.image (a ⊓ ·) ⊆ s ⊼ t := image_subset_image₂_right

theorem forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊓ b) :=
  forall_mem_image₂

@[simp]
theorem infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊓ b ∈ u :=
  image₂_subset_iff

@[simp]
theorem infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected theorem Nonempty.infs : s.Nonempty → t.Nonempty → (s ⊼ t).Nonempty :=
  Nonempty.image₂

theorem Nonempty.of_infs_left : (s ⊼ t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left

theorem Nonempty.of_infs_right : (s ⊼ t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
theorem empty_infs : ∅ ⊼ t = ∅ :=
  image₂_empty_left

@[simp]
theorem infs_empty : s ⊼ ∅ = ∅ :=
  image₂_empty_right

@[simp]
theorem infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[simp] lemma singleton_infs : {a} ⊼ t = t.image (a ⊓ ·) := image₂_singleton_left

@[simp] lemma infs_singleton : s ⊼ {b} = s.image (· ⊓ b) := image₂_singleton_right

theorem singleton_infs_singleton : ({a} ⊼ {b} : Finset α) = {a ⊓ b} :=
  image₂_singleton

theorem infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t :=
  image₂_union_left

theorem infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ :=
  image₂_union_right

theorem infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t :=
  image₂_inter_subset_left

theorem infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ :=
  image₂_inter_subset_right

theorem subset_infs {s t : Set α} :
    ↑u ⊆ s ⊼ t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊼ t' :=
  subset_set_image₂

lemma image_infs (f : F) (s t : Finset α) : image f (s ⊼ t) = image f s ⊼ image f t :=
  image_image₂_distrib <| map_inf f

lemma map_infs (f : F) (hf) (s t : Finset α) :
    map ⟨f, hf⟩ (s ⊼ t) = map ⟨f, hf⟩ s ⊼ map ⟨f, hf⟩ t := by
  simpa [map_eq_image] using image_infs f s t

lemma subset_infs_self : s ⊆ s ⊼ s := fun _a ha ↦ mem_infs.2 ⟨_, ha, _, ha, inf_idem _⟩
lemma infs_self_subset : s ⊼ s ⊆ s ↔ InfClosed (s : Set α) := infs_subset_iff
@[simp] lemma infs_self : s ⊼ s = s ↔ InfClosed (s : Set α) := by simp [← coe_inj]

@[simp] lemma univ_infs_univ [Fintype α] : (univ : Finset α) ⊼ univ = univ := by simp

lemma filter_infs_le [DecidableLE α] (s t : Finset α) (a : α) :
    {b ∈ s ⊼ t | a ≤ b} = {b ∈ s | a ≤ b} ⊼ {b ∈ t | a ≤ b} := by
  simp only [← coe_inj, coe_filter, coe_infs, ← mem_coe, Set.sep_infs_le]

variable (s t u)

lemma biUnion_image_inf_left : s.biUnion (fun a ↦ t.image (a ⊓ ·)) = s ⊼ t := biUnion_image_left

lemma biUnion_image_inf_right : t.biUnion (fun b ↦ s.image (· ⊓ b)) = s ⊼ t := biUnion_image_right

theorem image_inf_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊓ ·)) = s ⊼ t :=
  image_uncurry_product _ _ _

theorem infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) := image₂_assoc inf_assoc

theorem infs_comm : s ⊼ t = t ⊼ s := image₂_comm inf_comm

theorem infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image₂_left_comm inf_left_comm

theorem infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image₂_right_comm inf_right_comm

theorem infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v) :=
  image₂_image₂_image₂_comm inf_inf_inf_comm

end Infs

open FinsetFamily

section DistribLattice

variable [DecidableEq α]
variable [DistribLattice α] (s t u : Finset α)

theorem sups_infs_subset_left : s ⊻ t ⊼ u ⊆ (s ⊻ t) ⊼ (s ⊻ u) :=
  image₂_distrib_subset_left sup_inf_left

theorem sups_infs_subset_right : t ⊼ u ⊻ s ⊆ (t ⊻ s) ⊼ (u ⊻ s) :=
  image₂_distrib_subset_right sup_inf_right

theorem infs_sups_subset_left : s ⊼ (t ⊻ u) ⊆ s ⊼ t ⊻ s ⊼ u :=
  image₂_distrib_subset_left inf_sup_left

theorem infs_sups_subset_right : (t ⊻ u) ⊼ s ⊆ t ⊼ s ⊻ u ⊼ s :=
  image₂_distrib_subset_right inf_sup_right

end DistribLattice

section Finset
variable [DecidableEq α]
variable {𝒜 ℬ : Finset (Finset α)} {s t : Finset α}

@[simp] lemma powerset_union (s t : Finset α) : (s ∪ t).powerset = s.powerset ⊻ t.powerset := by
  ext u
  simp only [mem_sups, mem_powerset, sup_eq_union]
  refine ⟨fun h ↦ ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← union_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact union_subset_union hv hw

@[simp] lemma powerset_inter (s t : Finset α) : (s ∩ t).powerset = s.powerset ⊼ t.powerset := by
  ext u
  simp only [mem_infs, mem_powerset, inf_eq_inter]
  refine ⟨fun h ↦ ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← inter_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact inter_subset_inter hv hw

@[simp] lemma powerset_sups_powerset_self (s : Finset α) :
    s.powerset ⊻ s.powerset = s.powerset := by simp [← powerset_union]

@[simp] lemma powerset_infs_powerset_self (s : Finset α) :
    s.powerset ⊼ s.powerset = s.powerset := by simp [← powerset_inter]

lemma union_mem_sups : s ∈ 𝒜 → t ∈ ℬ → s ∪ t ∈ 𝒜 ⊻ ℬ := sup_mem_sups
lemma inter_mem_infs : s ∈ 𝒜 → t ∈ ℬ → s ∩ t ∈ 𝒜 ⊼ ℬ := inf_mem_infs

end Finset

section DisjSups

variable [DecidableEq α]
variable [SemilatticeSup α] [OrderBot α] [DecidableRel (α := α) Disjoint]
  (s s₁ s₂ t t₁ t₂ u : Finset α)

/-- The finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a` and `b` are disjoint.
-/
def disjSups : Finset α := {ab ∈ s ×ˢ t | Disjoint ab.1 ab.2}.image fun ab => ab.1 ⊔ ab.2

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " ○ " => Finset.disjSups

variable {s t u} {a b c : α}

@[simp]
theorem mem_disjSups : c ∈ s ○ t ↔ ∃ a ∈ s, ∃ b ∈ t, Disjoint a b ∧ a ⊔ b = c := by
  simp [disjSups, and_assoc]

theorem disjSups_subset_sups : s ○ t ⊆ s ⊻ t := by
  simp_rw [subset_iff, mem_sups, mem_disjSups]
  exact fun c ⟨a, b, ha, hb, _, hc⟩ => ⟨a, b, ha, hb, hc⟩

variable (s t)

theorem card_disjSups_le : #(s ○ t) ≤ #s * #t :=
  (card_le_card disjSups_subset_sups).trans <| card_sups_le _ _

variable {s s₁ s₂ t t₁ t₂}

theorem disjSups_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ○ t₁ ⊆ s₂ ○ t₂ :=
  image_subset_image <| filter_subset_filter _ <| product_subset_product hs ht

theorem disjSups_subset_left (ht : t₁ ⊆ t₂) : s ○ t₁ ⊆ s ○ t₂ :=
  disjSups_subset Subset.rfl ht

theorem disjSups_subset_right (hs : s₁ ⊆ s₂) : s₁ ○ t ⊆ s₂ ○ t :=
  disjSups_subset hs Subset.rfl

theorem forall_disjSups_iff {p : α → Prop} :
    (∀ c ∈ s ○ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, Disjoint a b → p (a ⊔ b) := by
  simp_rw [mem_disjSups]
  refine ⟨fun h a ha b hb hab => h _ ⟨_, ha, _, hb, hab, rfl⟩, ?_⟩
  rintro h _ ⟨a, ha, b, hb, hab, rfl⟩
  exact h _ ha _ hb hab

@[simp]
theorem disjSups_subset_iff : s ○ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, Disjoint a b → a ⊔ b ∈ u :=
  forall_disjSups_iff

theorem Nonempty.of_disjSups_left : (s ○ t).Nonempty → s.Nonempty := by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, a, ha, _⟩ => ⟨a, ha⟩

theorem Nonempty.of_disjSups_right : (s ○ t).Nonempty → t.Nonempty := by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, _, _, b, hb, _⟩ => ⟨b, hb⟩

@[simp]
theorem disjSups_empty_left : ∅ ○ t = ∅ := by simp [disjSups]

@[simp]
theorem disjSups_empty_right : s ○ ∅ = ∅ := by simp [disjSups]

theorem disjSups_singleton : ({a} ○ {b} : Finset α) = if Disjoint a b then {a ⊔ b} else ∅ := by
  split_ifs with h <;> simp [disjSups, filter_singleton, h]

theorem disjSups_union_left : (s₁ ∪ s₂) ○ t = s₁ ○ t ∪ s₂ ○ t := by
  simp [disjSups, filter_union, image_union]

theorem disjSups_union_right : s ○ (t₁ ∪ t₂) = s ○ t₁ ∪ s ○ t₂ := by
  simp [disjSups, filter_union, image_union]

theorem disjSups_inter_subset_left : (s₁ ∩ s₂) ○ t ⊆ s₁ ○ t ∩ s₂ ○ t := by
  simpa only [disjSups, inter_product, filter_inter_distrib] using image_inter_subset _ _ _

theorem disjSups_inter_subset_right : s ○ (t₁ ∩ t₂) ⊆ s ○ t₁ ∩ s ○ t₂ := by
  simpa only [disjSups, product_inter, filter_inter_distrib] using image_inter_subset _ _ _

variable (s t)

theorem disjSups_comm : s ○ t = t ○ s := by
  aesop (add simp disjoint_comm, simp sup_comm)

instance : @Std.Commutative (Finset α) (· ○ ·) := ⟨disjSups_comm⟩

end DisjSups

section DistribLattice

variable [DecidableEq α]
variable [DistribLattice α] [OrderBot α] [DecidableRel (α := α) Disjoint] (s t u v : Finset α)

theorem disjSups_assoc : ∀ s t u : Finset α, s ○ t ○ u = s ○ (t ○ u) := by
  refine (associative_of_commutative_of_le inferInstance ?_).assoc
  simp only [le_eq_subset, disjSups_subset_iff, mem_disjSups]
  rintro s t u _ ⟨a, ha, b, hb, hab, rfl⟩ c hc habc
  rw [disjoint_sup_left] at habc
  exact ⟨a, ha, _, ⟨b, hb, c, hc, habc.2, rfl⟩, hab.sup_right habc.1, (sup_assoc ..).symm⟩

instance : @Std.Associative (Finset α) (· ○ ·) := ⟨disjSups_assoc⟩

theorem disjSups_left_comm : s ○ (t ○ u) = t ○ (s ○ u) := by
  simp_rw [← disjSups_assoc, disjSups_comm s]

theorem disjSups_right_comm : s ○ t ○ u = s ○ u ○ t := by simp_rw [disjSups_assoc, disjSups_comm]

theorem disjSups_disjSups_disjSups_comm : s ○ t ○ (u ○ v) = s ○ u ○ (t ○ v) := by
  simp_rw [← disjSups_assoc, disjSups_right_comm]

end DistribLattice
section Diffs
variable [DecidableEq α]
variable [GeneralizedBooleanAlgebra α] (s s₁ s₂ t t₁ t₂ u : Finset α)

/-- `s \\ t` is the finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`. -/
def diffs : Finset α → Finset α → Finset α := image₂ (· \ ·)

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " \\\\ " => Finset.diffs
  -- This notation is meant to have higher precedence than `\` and `⊓`, but still within the
  -- realm of other binary notation

variable {s t} {a b c : α}

@[simp] lemma mem_diffs : c ∈ s \\ t ↔ ∃ a ∈ s, ∃ b ∈ t, a \ b = c := by simp [(· \\ ·)]

variable (s t)

@[simp, norm_cast] lemma coe_diffs : (↑(s \\ t) : Set α) = Set.image2 (· \ ·) s t :=
  coe_image₂ _ _ _

lemma card_diffs_le : #(s \\ t) ≤ #s * #t := card_image₂_le _ _ _

lemma card_diffs_iff : #(s \\ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x ↦ x.1 \ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}

lemma sdiff_mem_diffs : a ∈ s → b ∈ t → a \ b ∈ s \\ t := mem_image₂_of_mem

lemma diffs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ \\ t₁ ⊆ s₂ \\ t₂ := image₂_subset
lemma diffs_subset_left : t₁ ⊆ t₂ → s \\ t₁ ⊆ s \\ t₂ := image₂_subset_left
lemma diffs_subset_right : s₁ ⊆ s₂ → s₁ \\ t ⊆ s₂ \\ t := image₂_subset_right

lemma image_subset_diffs_left : b ∈ t → s.image (· \ b) ⊆ s \\ t := image_subset_image₂_left

lemma image_subset_diffs_right : a ∈ s → t.image (a \ ·) ⊆ s \\ t := image_subset_image₂_right

lemma forall_mem_diffs {p : α → Prop} : (∀ c ∈ s \\ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a \ b) :=
  forall_mem_image₂

@[simp] lemma diffs_subset_iff : s \\ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a \ b ∈ u := image₂_subset_iff

@[simp]
lemma diffs_nonempty : (s \\ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected lemma Nonempty.diffs : s.Nonempty → t.Nonempty → (s \\ t).Nonempty := Nonempty.image₂

lemma Nonempty.of_diffs_left : (s \\ t).Nonempty → s.Nonempty := Nonempty.of_image₂_left
lemma Nonempty.of_diffs_right : (s \\ t).Nonempty → t.Nonempty := Nonempty.of_image₂_right

@[simp] lemma empty_diffs : ∅ \\ t = ∅ := image₂_empty_left
@[simp] lemma diffs_empty : s \\ ∅ = ∅ := image₂_empty_right
@[simp] lemma diffs_eq_empty : s \\ t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[simp] lemma singleton_diffs : {a} \\ t = t.image (a \ ·) := image₂_singleton_left
@[simp] lemma diffs_singleton : s \\ {b} = s.image (· \ b) := image₂_singleton_right
lemma singleton_diffs_singleton : ({a} \\ {b} : Finset α) = {a \ b} := image₂_singleton

lemma diffs_union_left : (s₁ ∪ s₂) \\ t = s₁ \\ t ∪ s₂ \\ t := image₂_union_left
lemma diffs_union_right : s \\ (t₁ ∪ t₂) = s \\ t₁ ∪ s \\ t₂ := image₂_union_right

lemma diffs_inter_subset_left : (s₁ ∩ s₂) \\ t ⊆ s₁ \\ t ∩ s₂ \\ t := image₂_inter_subset_left
lemma diffs_inter_subset_right : s \\ (t₁ ∩ t₂) ⊆ s \\ t₁ ∩ s \\ t₂ := image₂_inter_subset_right

lemma subset_diffs {s t : Set α} :
    ↑u ⊆ Set.image2 (· \ ·) s t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' \\ t' :=
  subset_set_image₂

variable (s t u)

lemma biUnion_image_sdiff_left : s.biUnion (fun a ↦ t.image (a \ ·)) = s \\ t := biUnion_image_left
lemma biUnion_image_sdiff_right : t.biUnion (fun b ↦ s.image (· \ b)) = s \\ t :=
  biUnion_image_right

lemma image_sdiff_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· \ ·)) = s \\ t :=
  image_uncurry_product _ _ _

lemma diffs_right_comm : s \\ t \\ u = s \\ u \\ t := image₂_right_comm sdiff_right_comm

end Diffs

section Compls
variable [BooleanAlgebra α] (s s₁ s₂ t : Finset α)

/-- `sᶜˢ` is the finset of elements of the form `aᶜ` where `a ∈ s`. -/
def compls : Finset α → Finset α := map ⟨compl, compl_injective⟩

@[inherit_doc]
scoped[FinsetFamily] postfix:max "ᶜˢ" => Finset.compls

variable {s t} {a : α}

@[simp] lemma mem_compls : a ∈ sᶜˢ ↔ aᶜ ∈ s := by
  rw [Iff.comm, ← mem_map' ⟨compl, compl_injective⟩, Embedding.coeFn_mk, compl_compl, compls]

variable (s t)

@[simp] lemma image_compl [DecidableEq α] : s.image compl = sᶜˢ := by simp [compls, map_eq_image]

@[simp, norm_cast] lemma coe_compls : (↑sᶜˢ : Set α) = compl '' ↑s := coe_map _ _

@[simp] lemma card_compls : #sᶜˢ = #s := card_map _

variable {s s₁ s₂ t}

lemma compl_mem_compls : a ∈ s → aᶜ ∈ sᶜˢ := mem_map_of_mem _
@[simp] lemma compls_subset_compls : s₁ᶜˢ ⊆ s₂ᶜˢ ↔ s₁ ⊆ s₂ := map_subset_map
lemma forall_mem_compls {p : α → Prop} : (∀ a ∈ sᶜˢ, p a) ↔ ∀ a ∈ s, p aᶜ := forall_mem_map
lemma exists_compls_iff {p : α → Prop} : (∃ a ∈ sᶜˢ, p a) ↔ ∃ a ∈ s, p aᶜ := by aesop

@[simp] lemma compls_compls (s : Finset α) : sᶜˢᶜˢ = s := by ext; simp

lemma compls_subset_iff : sᶜˢ ⊆ t ↔ s ⊆ tᶜˢ := by rw [← compls_subset_compls, compls_compls]

@[simp]
lemma compls_nonempty : sᶜˢ.Nonempty ↔ s.Nonempty := map_nonempty

protected alias ⟨Nonempty.of_compls, Nonempty.compls⟩ := compls_nonempty
attribute [aesop safe apply (rule_sets := [finsetNonempty])] Nonempty.compls

@[simp] lemma compls_empty : (∅ : Finset α)ᶜˢ = ∅ := map_empty _
@[simp] lemma compls_eq_empty : sᶜˢ = ∅ ↔ s = ∅ := map_eq_empty
@[simp] lemma compls_singleton (a : α) : {a}ᶜˢ = {aᶜ} := map_singleton _ _
@[simp] lemma compls_univ [Fintype α] : (univ : Finset α)ᶜˢ = univ := by ext; simp

variable [DecidableEq α]

@[simp] lemma compls_union (s t : Finset α) : (s ∪ t)ᶜˢ = sᶜˢ ∪ tᶜˢ := map_union _ _
@[simp] lemma compls_inter (s t : Finset α) : (s ∩ t)ᶜˢ = sᶜˢ ∩ tᶜˢ := map_inter _ _

@[simp] lemma compls_infs (s t : Finset α) : (s ⊼ t)ᶜˢ = sᶜˢ ⊻ tᶜˢ := by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ ↦ compl_inf

@[simp] lemma compls_sups (s t : Finset α) : (s ⊻ t)ᶜˢ = sᶜˢ ⊼ tᶜˢ := by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ ↦ compl_sup

@[simp] lemma infs_compls_eq_diffs (s t : Finset α) : s ⊼ tᶜˢ = s \\ t := by
  ext; simp [sdiff_eq]; aesop

@[simp] lemma compls_infs_eq_diffs (s t : Finset α) : sᶜˢ ⊼ t = t \\ s := by
  rw [infs_comm, infs_compls_eq_diffs]

@[simp] lemma diffs_compls_eq_infs (s t : Finset α) : s \\ tᶜˢ = s ⊼ t := by
  rw [← infs_compls_eq_diffs, compls_compls]

variable {α : Type*} [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {n : ℕ}

protected lemma _root_.Set.Sized.compls (h𝒜 : (𝒜 : Set (Finset α)).Sized n) :
    (𝒜ᶜˢ : Set (Finset α)).Sized (Fintype.card α - n) :=
  Finset.forall_mem_compls.2 <| fun s hs ↦ by rw [Finset.card_compl, h𝒜 hs]

lemma sized_compls (hn : n ≤ Fintype.card α) :
    (𝒜ᶜˢ : Set (Finset α)).Sized n ↔ (𝒜 : Set (Finset α)).Sized (Fintype.card α - n) where
  mp h𝒜 := by simpa using h𝒜.compls
  mpr h𝒜 := by simpa only [Nat.sub_sub_self hn] using h𝒜.compls

end Compls
end Finset
