/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Option
import Mathlib.Data.Set.Lattice.Image

/-!
# Lattice operations on finsets

This file is concerned with how big lattice or set operations behave when indexed by a finset.

See also `Mathlib/Data/Finset/Lattice.lean`, which is concerned with folding binary lattice
operations over a finset.
-/

assert_not_exists OrderedCommMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

section Lattice

variable {ι' : Sort*} [CompleteLattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `iSup_eq_iSup_finset'` for a version
that works for `ι : Sort*`. -/
theorem iSup_eq_iSup_finset (s : ι → α) : ⨆ i, s i = ⨆ t : Finset ι, ⨆ i ∈ t, s i := by
  classical
  refine le_antisymm ?_ ?_
  · exact iSup_le fun b => le_iSup_of_le {b} <| le_iSup_of_le b <| le_iSup_of_le (by simp) <| le_rfl
  · exact iSup_le fun t => iSup_le fun b => iSup_le fun _ => le_iSup _ _

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `iSup_eq_iSup_finset` for a version
that assumes `ι : Type*` but has no `PLift`s. -/
theorem iSup_eq_iSup_finset' (s : ι' → α) :
    ⨆ i, s i = ⨆ t : Finset (PLift ι'), ⨆ i ∈ t, s (PLift.down i) := by
  rw [← iSup_eq_iSup_finset, ← Equiv.plift.surjective.iSup_comp]; rfl

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `iInf_eq_iInf_finset'` for a version
that works for `ι : Sort*`. -/
theorem iInf_eq_iInf_finset (s : ι → α) : ⨅ i, s i = ⨅ (t : Finset ι) (i ∈ t), s i :=
  @iSup_eq_iSup_finset αᵒᵈ _ _ _

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `iInf_eq_iInf_finset` for a version
that assumes `ι : Type*` but has no `PLift`s. -/
theorem iInf_eq_iInf_finset' (s : ι' → α) :
    ⨅ i, s i = ⨅ t : Finset (PLift ι'), ⨅ i ∈ t, s (PLift.down i) :=
  @iSup_eq_iSup_finset' αᵒᵈ _ _ _

end Lattice

namespace Set

variable {ι' : Sort*}

/-- Union of an indexed family of sets `s : ι → Set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `iUnion_eq_iUnion_finset'` for
a version that works for `ι : Sort*`. -/
theorem iUnion_eq_iUnion_finset (s : ι → Set α) : ⋃ i, s i = ⋃ t : Finset ι, ⋃ i ∈ t, s i :=
  iSup_eq_iSup_finset s

/-- Union of an indexed family of sets `s : ι → Set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `iUnion_eq_iUnion_finset` for
a version that assumes `ι : Type*` but avoids `PLift`s in the right-hand side. -/
theorem iUnion_eq_iUnion_finset' (s : ι' → Set α) :
    ⋃ i, s i = ⋃ t : Finset (PLift ι'), ⋃ i ∈ t, s (PLift.down i) :=
  iSup_eq_iSup_finset' s

/-- Intersection of an indexed family of sets `s : ι → Set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`iInter_eq_iInter_finset'` for a version that works for `ι : Sort*`. -/
theorem iInter_eq_iInter_finset (s : ι → Set α) : ⋂ i, s i = ⋂ t : Finset ι, ⋂ i ∈ t, s i :=
  iInf_eq_iInf_finset s

/-- Intersection of an indexed family of sets `s : ι → Set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`iInter_eq_iInter_finset` for a version that assumes `ι : Type*` but avoids `PLift`s in the
right-hand side. -/
theorem iInter_eq_iInter_finset' (s : ι' → Set α) :
    ⋂ i, s i = ⋂ t : Finset (PLift ι'), ⋂ i ∈ t, s (PLift.down i) :=
  iInf_eq_iInf_finset' s

end Set

namespace Finset

section minimal

variable [DecidableEq α] {P : Finset α → Prop} {s : Finset α}

theorem maximal_iff_forall_insert (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) :
    Maximal P s ↔ P s ∧ ∀ x ∉ s, ¬ P (insert x s) := by
  simp only [Maximal, and_congr_right_iff]
  exact fun _ ↦ ⟨fun h x hxs hx ↦ hxs <| h hx (subset_insert _ _) (mem_insert_self x s),
    fun h t ht hst x hxt ↦ by_contra fun hxs ↦ h x hxs (hP ht (insert_subset hxt hst))⟩

theorem minimal_iff_forall_diff_singleton (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) :
    Minimal P s ↔ P s ∧ ∀ x ∈ s, ¬ P (s.erase x) where
  mp h := ⟨h.prop, fun x hxs hx ↦ by simpa using h.le_of_le hx (erase_subset _ _) hxs⟩
  mpr h := ⟨h.1, fun t ht hts x hxs ↦ by_contra fun hxt ↦
    h.2 x hxs <| hP ht (subset_erase.2 ⟨hts, hxt⟩)⟩

end minimal

/-! ### Interaction with big lattice/set operations -/

section Lattice

theorem iSup_coe [SupSet β] (f : α → β) (s : Finset α) : ⨆ x ∈ (↑s : Set α), f x = ⨆ x ∈ s, f x :=
  rfl

theorem iInf_coe [InfSet β] (f : α → β) (s : Finset α) : ⨅ x ∈ (↑s : Set α), f x = ⨅ x ∈ s, f x :=
  rfl

variable [CompleteLattice β]

theorem iSup_singleton (a : α) (s : α → β) : ⨆ x ∈ ({a} : Finset α), s x = s a := by simp

theorem iInf_singleton (a : α) (s : α → β) : ⨅ x ∈ ({a} : Finset α), s x = s a := by simp

theorem iSup_option_toFinset (o : Option α) (f : α → β) : ⨆ x ∈ o.toFinset, f x = ⨆ x ∈ o, f x := by
  simp

theorem iInf_option_toFinset (o : Option α) (f : α → β) : ⨅ x ∈ o.toFinset, f x = ⨅ x ∈ o, f x :=
  @iSup_option_toFinset _ βᵒᵈ _ _ _

variable [DecidableEq α]

theorem iSup_union {f : α → β} {s t : Finset α} :
    ⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by simp [iSup_or, iSup_sup_eq]

theorem iInf_union {f : α → β} {s t : Finset α} :
    ⨅ x ∈ s ∪ t, f x = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @iSup_union α βᵒᵈ _ _ _ _ _

theorem iSup_insert (a : α) (s : Finset α) (t : α → β) :
    ⨆ x ∈ insert a s, t x = t a ⊔ ⨆ x ∈ s, t x := by
  rw [insert_eq]
  simp only [iSup_union, Finset.iSup_singleton]

theorem iInf_insert (a : α) (s : Finset α) (t : α → β) :
    ⨅ x ∈ insert a s, t x = t a ⊓ ⨅ x ∈ s, t x :=
  @iSup_insert α βᵒᵈ _ _ _ _ _

theorem iSup_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    ⨆ x ∈ s.image f, g x = ⨆ y ∈ s, g (f y) := by rw [← iSup_coe, coe_image, iSup_image, iSup_coe]

theorem iInf_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    ⨅ x ∈ s.image f, g x = ⨅ y ∈ s, g (f y) := by rw [← iInf_coe, coe_image, iInf_image, iInf_coe]

theorem iSup_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    ⨆ i ∈ insert x t, Function.update f x s i = s ⊔ ⨆ i ∈ t, f i := by
  simp only [Finset.iSup_insert, update_self]
  rcongr (i hi); apply update_of_ne; rintro rfl; exact hx hi

theorem iInf_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    ⨅ i ∈ insert x t, update f x s i = s ⊓ ⨅ i ∈ t, f i :=
  @iSup_insert_update α βᵒᵈ _ _ _ _ f _ hx

theorem iSup_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    ⨆ y ∈ s.biUnion t, f y = ⨆ (x ∈ s) (y ∈ t x), f y := by simp [@iSup_comm _ α, iSup_and]

theorem iInf_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    ⨅ y ∈ s.biUnion t, f y = ⨅ (x ∈ s) (y ∈ t x), f y :=
  @iSup_biUnion _ βᵒᵈ _ _ _ _ _ _

end Lattice

theorem set_biUnion_coe (s : Finset α) (t : α → Set β) : ⋃ x ∈ (↑s : Set α), t x = ⋃ x ∈ s, t x :=
  rfl

theorem set_biInter_coe (s : Finset α) (t : α → Set β) : ⋂ x ∈ (↑s : Set α), t x = ⋂ x ∈ s, t x :=
  rfl

theorem set_biUnion_singleton (a : α) (s : α → Set β) : ⋃ x ∈ ({a} : Finset α), s x = s a :=
  iSup_singleton a s

theorem set_biInter_singleton (a : α) (s : α → Set β) : ⋂ x ∈ ({a} : Finset α), s x = s a :=
  iInf_singleton a s

@[simp]
theorem set_biUnion_preimage_singleton (f : α → β) (s : Finset β) :
    ⋃ y ∈ s, f ⁻¹' {y} = f ⁻¹' s :=
  Set.biUnion_preimage_singleton f s

theorem set_biUnion_option_toFinset (o : Option α) (f : α → Set β) :
    ⋃ x ∈ o.toFinset, f x = ⋃ x ∈ o, f x :=
  iSup_option_toFinset o f

theorem set_biInter_option_toFinset (o : Option α) (f : α → Set β) :
    ⋂ x ∈ o.toFinset, f x = ⋂ x ∈ o, f x :=
  iInf_option_toFinset o f

theorem subset_set_biUnion_of_mem {s : Finset α} {f : α → Set β} {x : α} (h : x ∈ s) :
    f x ⊆ ⋃ y ∈ s, f y :=
  show f x ≤ ⨆ y ∈ s, f y from le_iSup_of_le x <| by simp only [h, iSup_pos, le_refl]

variable [DecidableEq α]

theorem set_biUnion_union (s t : Finset α) (u : α → Set β) :
    ⋃ x ∈ s ∪ t, u x = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  iSup_union

theorem set_biInter_inter (s t : Finset α) (u : α → Set β) :
    ⋂ x ∈ s ∪ t, u x = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  iInf_union

theorem set_biUnion_insert (a : α) (s : Finset α) (t : α → Set β) :
    ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x :=
  iSup_insert a s t

theorem set_biInter_insert (a : α) (s : Finset α) (t : α → Set β) :
    ⋂ x ∈ insert a s, t x = t a ∩ ⋂ x ∈ s, t x :=
  iInf_insert a s t

theorem set_biUnion_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    ⋃ x ∈ s.image f, g x = ⋃ y ∈ s, g (f y) :=
  iSup_finset_image

theorem set_biInter_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    ⋂ x ∈ s.image f, g x = ⋂ y ∈ s, g (f y) :=
  iInf_finset_image

theorem set_biUnion_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    ⋃ i ∈ insert x t, @update _ _ _ f x s i = s ∪ ⋃ i ∈ t, f i :=
  iSup_insert_update f hx

theorem set_biInter_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    ⋂ i ∈ insert x t, @update _ _ _ f x s i = s ∩ ⋂ i ∈ t, f i :=
  iInf_insert_update f hx

theorem set_biUnion_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    ⋃ y ∈ s.biUnion t, f y = ⋃ (x ∈ s) (y ∈ t x), f y :=
  iSup_biUnion s t f

theorem set_biInter_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    ⋂ y ∈ s.biUnion t, f y = ⋂ (x ∈ s) (y ∈ t x), f y :=
  iInf_biUnion s t f

end Finset
