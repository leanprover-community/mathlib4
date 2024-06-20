/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Patrick Massot
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.SProd

#align_import data.set.prod from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
# Sets in product and pi types

This file defines the product of sets in `α × β` and in `Π i, α i` along with the diagonal of a
type.

## Main declarations

* `Set.prod`: Binary product of sets. For `s : Set α`, `t : Set β`, we have
  `s.prod t : Set (α × β)`.
* `Set.diagonal`: Diagonal of a type. `Set.diagonal α = {(x, x) | x : α}`.
* `Set.offDiag`: Off-diagonal. `s ×ˢ s` without the diagonal.
* `Set.pi`: Arbitrary product of sets.
-/


open Function

namespace Set

/-! ### Cartesian binary product of sets -/


section Prod

variable {α β γ δ : Type*} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

theorem Subsingleton.prod (hs : s.Subsingleton) (ht : t.Subsingleton) :
    (s ×ˢ t).Subsingleton := fun _x hx _y hy ↦
  Prod.ext (hs hx.1 hy.1) (ht hx.2 hy.2)

noncomputable instance decidableMemProd [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ×ˢ t) := fun _ => And.decidable
#align set.decidable_mem_prod Set.decidableMemProd

@[gcongr]
theorem prod_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ :=
  fun _ ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩
#align set.prod_mono Set.prod_mono

@[gcongr]
theorem prod_mono_left (hs : s₁ ⊆ s₂) : s₁ ×ˢ t ⊆ s₂ ×ˢ t :=
  prod_mono hs Subset.rfl
#align set.prod_mono_left Set.prod_mono_left

@[gcongr]
theorem prod_mono_right (ht : t₁ ⊆ t₂) : s ×ˢ t₁ ⊆ s ×ˢ t₂ :=
  prod_mono Subset.rfl ht
#align set.prod_mono_right Set.prod_mono_right

@[simp]
theorem prod_self_subset_prod_self : s₁ ×ˢ s₁ ⊆ s₂ ×ˢ s₂ ↔ s₁ ⊆ s₂ :=
  ⟨fun h _ hx => (h (mk_mem_prod hx hx)).1, fun h _ hx => ⟨h hx.1, h hx.2⟩⟩
#align set.prod_self_subset_prod_self Set.prod_self_subset_prod_self

@[simp]
theorem prod_self_ssubset_prod_self : s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂ :=
  and_congr prod_self_subset_prod_self <| not_congr prod_self_subset_prod_self
#align set.prod_self_ssubset_prod_self Set.prod_self_ssubset_prod_self

theorem prod_subset_iff {P : Set (α × β)} : s ×ˢ t ⊆ P ↔ ∀ x ∈ s, ∀ y ∈ t, (x, y) ∈ P :=
  ⟨fun h _ hx _ hy => h (mk_mem_prod hx hy), fun h ⟨_, _⟩ hp => h _ hp.1 _ hp.2⟩
#align set.prod_subset_iff Set.prod_subset_iff

theorem forall_prod_set {p : α × β → Prop} : (∀ x ∈ s ×ˢ t, p x) ↔ ∀ x ∈ s, ∀ y ∈ t, p (x, y) :=
  prod_subset_iff
#align set.forall_prod_set Set.forall_prod_set

theorem exists_prod_set {p : α × β → Prop} : (∃ x ∈ s ×ˢ t, p x) ↔ ∃ x ∈ s, ∃ y ∈ t, p (x, y) := by
  simp [and_assoc]
#align set.exists_prod_set Set.exists_prod_set

@[simp]
theorem prod_empty : s ×ˢ (∅ : Set β) = ∅ := by
  ext
  exact and_false_iff _
#align set.prod_empty Set.prod_empty

@[simp]
theorem empty_prod : (∅ : Set α) ×ˢ t = ∅ := by
  ext
  exact false_and_iff _
#align set.empty_prod Set.empty_prod

@[simp, mfld_simps]
theorem univ_prod_univ : @univ α ×ˢ @univ β = univ := by
  ext
  exact true_and_iff _
#align set.univ_prod_univ Set.univ_prod_univ

theorem univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t := by simp [prod_eq]
#align set.univ_prod Set.univ_prod

theorem prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s := by simp [prod_eq]
#align set.prod_univ Set.prod_univ

@[simp] lemma prod_eq_univ [Nonempty α] [Nonempty β] : s ×ˢ t = univ ↔ s = univ ∧ t = univ := by
  simp [eq_univ_iff_forall, forall_and]

@[simp]
theorem singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
#align set.singleton_prod Set.singleton_prod

@[simp]
theorem prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
#align set.prod_singleton Set.prod_singleton

theorem singleton_prod_singleton : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := by simp
#align set.singleton_prod_singleton Set.singleton_prod_singleton

@[simp]
theorem union_prod : (s₁ ∪ s₂) ×ˢ t = s₁ ×ˢ t ∪ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp [or_and_right]
#align set.union_prod Set.union_prod

@[simp]
theorem prod_union : s ×ˢ (t₁ ∪ t₂) = s ×ˢ t₁ ∪ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp [and_or_left]
#align set.prod_union Set.prod_union

theorem inter_prod : (s₁ ∩ s₂) ×ˢ t = s₁ ×ˢ t ∩ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp only [← and_and_right, mem_inter_iff, mem_prod]
#align set.inter_prod Set.inter_prod

theorem prod_inter : s ×ˢ (t₁ ∩ t₂) = s ×ˢ t₁ ∩ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp only [← and_and_left, mem_inter_iff, mem_prod]
#align set.prod_inter Set.prod_inter

@[mfld_simps]
theorem prod_inter_prod : s₁ ×ˢ t₁ ∩ s₂ ×ˢ t₂ = (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]
#align set.prod_inter_prod Set.prod_inter_prod

lemma compl_prod_eq_union {α β : Type*} (s : Set α) (t : Set β) :
    (s ×ˢ t)ᶜ = (sᶜ ×ˢ univ) ∪ (univ ×ˢ tᶜ) := by
  ext p
  simp only [mem_compl_iff, mem_prod, not_and, mem_union, mem_univ, and_true, true_and]
  constructor <;> intro h
  · by_cases fst_in_s : p.fst ∈ s
    · exact Or.inr (h fst_in_s)
    · exact Or.inl fst_in_s
  · intro fst_in_s
    simpa only [fst_in_s, not_true, false_or] using h

@[simp]
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_left, mem_prod, not_and_or, Prod.forall, and_imp, ← @forall_or_right α, ←
    @forall_or_left β, ← @forall_or_right (_ ∈ s₁), ← @forall_or_left (_ ∈ t₁)]
#align set.disjoint_prod Set.disjoint_prod

theorem Disjoint.set_prod_left (hs : Disjoint s₁ s₂) (t₁ t₂ : Set β) :
    Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) :=
  disjoint_left.2 fun ⟨_a, _b⟩ ⟨ha₁, _⟩ ⟨ha₂, _⟩ => disjoint_left.1 hs ha₁ ha₂
#align set.disjoint.set_prod_left Set.Disjoint.set_prod_left

theorem Disjoint.set_prod_right (ht : Disjoint t₁ t₂) (s₁ s₂ : Set α) :
    Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) :=
  disjoint_left.2 fun ⟨_a, _b⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩ => disjoint_left.1 ht hb₁ hb₂
#align set.disjoint.set_prod_right Set.Disjoint.set_prod_right

theorem insert_prod : insert a s ×ˢ t = Prod.mk a '' t ∪ s ×ˢ t := by
  ext ⟨x, y⟩
  simp (config := { contextual := true }) [image, iff_def, or_imp]
#align set.insert_prod Set.insert_prod

theorem prod_insert : s ×ˢ insert b t = (fun a => (a, b)) '' s ∪ s ×ˢ t := by
  ext ⟨x, y⟩
  -- porting note (#10745):
  -- was `simp (config := { contextual := true }) [image, iff_def, or_imp, Imp.swap]`
  simp only [mem_prod, mem_insert_iff, image, mem_union, mem_setOf_eq, Prod.mk.injEq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hx, rfl|hy⟩ := h
    · exact Or.inl ⟨x, hx, rfl, rfl⟩
    · exact Or.inr ⟨hx, hy⟩
  · obtain ⟨x, hx, rfl, rfl⟩|⟨hx, hy⟩ := h
    · exact ⟨hx, Or.inl rfl⟩
    · exact ⟨hx, Or.inr hy⟩
#align set.prod_insert Set.prod_insert

theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
    (f ⁻¹' s) ×ˢ (g ⁻¹' t) = (fun p : γ × δ => (f p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl
#align set.prod_preimage_eq Set.prod_preimage_eq

theorem prod_preimage_left {f : γ → α} :
    (f ⁻¹' s) ×ˢ t = (fun p : γ × β => (f p.1, p.2)) ⁻¹' s ×ˢ t :=
  rfl
#align set.prod_preimage_left Set.prod_preimage_left

theorem prod_preimage_right {g : δ → β} :
    s ×ˢ (g ⁻¹' t) = (fun p : α × δ => (p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl
#align set.prod_preimage_right Set.prod_preimage_right

theorem preimage_prod_map_prod (f : α → β) (g : γ → δ) (s : Set β) (t : Set δ) :
    Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) :=
  rfl
#align set.preimage_prod_map_prod Set.preimage_prod_map_prod

theorem mk_preimage_prod (f : γ → α) (g : γ → β) :
    (fun x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl
#align set.mk_preimage_prod Set.mk_preimage_prod

@[simp]
theorem mk_preimage_prod_left (hb : b ∈ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = s := by
  ext a
  simp [hb]
#align set.mk_preimage_prod_left Set.mk_preimage_prod_left

@[simp]
theorem mk_preimage_prod_right (ha : a ∈ s) : Prod.mk a ⁻¹' s ×ˢ t = t := by
  ext b
  simp [ha]
#align set.mk_preimage_prod_right Set.mk_preimage_prod_right

@[simp]
theorem mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅ := by
  ext a
  simp [hb]
#align set.mk_preimage_prod_left_eq_empty Set.mk_preimage_prod_left_eq_empty

@[simp]
theorem mk_preimage_prod_right_eq_empty (ha : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅ := by
  ext b
  simp [ha]
#align set.mk_preimage_prod_right_eq_empty Set.mk_preimage_prod_right_eq_empty

theorem mk_preimage_prod_left_eq_if [DecidablePred (· ∈ t)] :
    (fun a => (a, b)) ⁻¹' s ×ˢ t = if b ∈ t then s else ∅ := by split_ifs with h <;> simp [h]
#align set.mk_preimage_prod_left_eq_if Set.mk_preimage_prod_left_eq_if

theorem mk_preimage_prod_right_eq_if [DecidablePred (· ∈ s)] :
    Prod.mk a ⁻¹' s ×ˢ t = if a ∈ s then t else ∅ := by split_ifs with h <;> simp [h]
#align set.mk_preimage_prod_right_eq_if Set.mk_preimage_prod_right_eq_if

theorem mk_preimage_prod_left_fn_eq_if [DecidablePred (· ∈ t)] (f : γ → α) :
    (fun a => (f a, b)) ⁻¹' s ×ˢ t = if b ∈ t then f ⁻¹' s else ∅ := by
  rw [← mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]
#align set.mk_preimage_prod_left_fn_eq_if Set.mk_preimage_prod_left_fn_eq_if

theorem mk_preimage_prod_right_fn_eq_if [DecidablePred (· ∈ s)] (g : δ → β) :
    (fun b => (a, g b)) ⁻¹' s ×ˢ t = if a ∈ s then g ⁻¹' t else ∅ := by
  rw [← mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]
#align set.mk_preimage_prod_right_fn_eq_if Set.mk_preimage_prod_right_fn_eq_if

@[simp]
theorem preimage_swap_prod (s : Set α) (t : Set β) : Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s := by
  ext ⟨x, y⟩
  simp [and_comm]
#align set.preimage_swap_prod Set.preimage_swap_prod

@[simp]
theorem image_swap_prod (s : Set α) (t : Set β) : Prod.swap '' s ×ˢ t = t ×ˢ s := by
  rw [image_swap_eq_preimage_swap, preimage_swap_prod]
#align set.image_swap_prod Set.image_swap_prod

theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
    (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t :=
  ext <| by
    simp [-exists_and_right, exists_and_right.symm, and_left_comm, and_assoc, and_comm]
#align set.prod_image_image_eq Set.prod_image_image_eq

theorem prod_range_range_eq {m₁ : α → γ} {m₂ : β → δ} :
    range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2) :=
  ext <| by simp [range]
#align set.prod_range_range_eq Set.prod_range_range_eq

@[simp, mfld_simps]
theorem range_prod_map {m₁ : α → γ} {m₂ : β → δ} : range (Prod.map m₁ m₂) = range m₁ ×ˢ range m₂ :=
  prod_range_range_eq.symm
#align set.range_prod_map Set.range_prod_map

theorem prod_range_univ_eq {m₁ : α → γ} :
    range m₁ ×ˢ (univ : Set β) = range fun p : α × β => (m₁ p.1, p.2) :=
  ext <| by simp [range]
#align set.prod_range_univ_eq Set.prod_range_univ_eq

theorem prod_univ_range_eq {m₂ : β → δ} :
    (univ : Set α) ×ˢ range m₂ = range fun p : α × β => (p.1, m₂ p.2) :=
  ext <| by simp [range]
#align set.prod_univ_range_eq Set.prod_univ_range_eq

theorem range_pair_subset (f : α → β) (g : α → γ) :
    (range fun x => (f x, g x)) ⊆ range f ×ˢ range g := by
  have : (fun x => (f x, g x)) = Prod.map f g ∘ fun x => (x, x) := funext fun x => rfl
  rw [this, ← range_prod_map]
  apply range_comp_subset_range
#align set.range_pair_subset Set.range_pair_subset

theorem Nonempty.prod : s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty := fun ⟨x, hx⟩ ⟨y, hy⟩ =>
  ⟨(x, y), ⟨hx, hy⟩⟩
#align set.nonempty.prod Set.Nonempty.prod

theorem Nonempty.fst : (s ×ˢ t).Nonempty → s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩
#align set.nonempty.fst Set.Nonempty.fst

theorem Nonempty.snd : (s ×ˢ t).Nonempty → t.Nonempty := fun ⟨x, hx⟩ => ⟨x.2, hx.2⟩
#align set.nonempty.snd Set.Nonempty.snd

@[simp]
theorem prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod h.2⟩
#align set.prod_nonempty_iff Set.prod_nonempty_iff

@[simp]
theorem prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_or]
#align set.prod_eq_empty_iff Set.prod_eq_empty_iff

theorem prod_sub_preimage_iff {W : Set γ} {f : α × β → γ} :
    s ×ˢ t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W := by simp [subset_def]
#align set.prod_sub_preimage_iff Set.prod_sub_preimage_iff

theorem image_prod_mk_subset_prod {f : α → β} {g : α → γ} {s : Set α} :
    (fun x => (f x, g x)) '' s ⊆ (f '' s) ×ˢ (g '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact mk_mem_prod (mem_image_of_mem f hx) (mem_image_of_mem g hx)
#align set.image_prod_mk_subset_prod Set.image_prod_mk_subset_prod

theorem image_prod_mk_subset_prod_left (hb : b ∈ t) : (fun a => (a, b)) '' s ⊆ s ×ˢ t := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨ha, hb⟩
#align set.image_prod_mk_subset_prod_left Set.image_prod_mk_subset_prod_left

theorem image_prod_mk_subset_prod_right (ha : a ∈ s) : Prod.mk a '' t ⊆ s ×ˢ t := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨ha, hb⟩
#align set.image_prod_mk_subset_prod_right Set.image_prod_mk_subset_prod_right

theorem prod_subset_preimage_fst (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.fst ⁻¹' s :=
  inter_subset_left
#align set.prod_subset_preimage_fst Set.prod_subset_preimage_fst

theorem fst_image_prod_subset (s : Set α) (t : Set β) : Prod.fst '' s ×ˢ t ⊆ s :=
  image_subset_iff.2 <| prod_subset_preimage_fst s t
#align set.fst_image_prod_subset Set.fst_image_prod_subset

theorem fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonempty) : Prod.fst '' s ×ˢ t = s :=
  (fst_image_prod_subset _ _).antisymm fun y hy =>
    let ⟨x, hx⟩ := ht
    ⟨(y, x), ⟨hy, hx⟩, rfl⟩
#align set.fst_image_prod Set.fst_image_prod

theorem prod_subset_preimage_snd (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.snd ⁻¹' t :=
  inter_subset_right
#align set.prod_subset_preimage_snd Set.prod_subset_preimage_snd

theorem snd_image_prod_subset (s : Set α) (t : Set β) : Prod.snd '' s ×ˢ t ⊆ t :=
  image_subset_iff.2 <| prod_subset_preimage_snd s t
#align set.snd_image_prod_subset Set.snd_image_prod_subset

theorem snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Set β) : Prod.snd '' s ×ˢ t = t :=
  (snd_image_prod_subset _ _).antisymm fun y y_in =>
    let ⟨x, x_in⟩ := hs
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩
#align set.snd_image_prod Set.snd_image_prod

theorem prod_diff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t := by
  ext x
  by_cases h₁ : x.1 ∈ s₁ <;> by_cases h₂ : x.2 ∈ t₁ <;> simp [*]
#align set.prod_diff_prod Set.prod_diff_prod

/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
theorem prod_subset_prod_iff : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  have st : s.Nonempty ∧ t.Nonempty := by rwa [prod_nonempty_iff] at h
  refine ⟨fun H => Or.inl ⟨?_, ?_⟩, ?_⟩
  · have := image_subset (Prod.fst : α × β → α) H
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H).snd] at this
  · have := image_subset (Prod.snd : α × β → β) H
    rwa [snd_image_prod st.1, snd_image_prod (h.mono H).fst] at this
  · intro H
    simp only [st.1.ne_empty, st.2.ne_empty, or_false_iff] at H
    exact prod_mono H.1 H.2
#align set.prod_subset_prod_iff Set.prod_subset_prod_iff

theorem prod_eq_prod_iff_of_nonempty (h : (s ×ˢ t).Nonempty) :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ := by
  constructor
  · intro heq
    have h₁ : (s₁ ×ˢ t₁ : Set _).Nonempty := by rwa [← heq]
    rw [prod_nonempty_iff] at h h₁
    rw [← fst_image_prod s h.2, ← fst_image_prod s₁ h₁.2, heq, eq_self_iff_true, true_and_iff, ←
      snd_image_prod h.1 t, ← snd_image_prod h₁.1 t₁, heq]
  · rintro ⟨rfl, rfl⟩
    rfl
#align set.prod_eq_prod_iff_of_nonempty Set.prod_eq_prod_iff_of_nonempty

theorem prod_eq_prod_iff :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) := by
  symm
  rcases eq_empty_or_nonempty (s ×ˢ t) with h | h
  · simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_and_iff,
      or_iff_right_iff_imp]
    rintro ⟨rfl, rfl⟩
    exact prod_eq_empty_iff.mp h
  rw [prod_eq_prod_iff_of_nonempty h]
  rw [nonempty_iff_ne_empty, Ne, prod_eq_empty_iff] at h
  simp_rw [h, false_and_iff, or_false_iff]
#align set.prod_eq_prod_iff Set.prod_eq_prod_iff

@[simp]
theorem prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ := by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, and_true_iff, or_iff_left_iff_imp,
    or_false_iff]
  rintro ⟨rfl, rfl⟩
  rfl
#align set.prod_eq_iff_eq Set.prod_eq_iff_eq

section Mono

variable [Preorder α] {f : α → Set β} {g : α → Set γ}

theorem _root_.Monotone.set_prod (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ×ˢ g x :=
  fun _ _ h => prod_mono (hf h) (hg h)
#align monotone.set_prod Monotone.set_prod

theorem _root_.Antitone.set_prod (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ×ˢ g x :=
  fun _ _ h => prod_mono (hf h) (hg h)
#align antitone.set_prod Antitone.set_prod

theorem _root_.MonotoneOn.set_prod (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x ×ˢ g x) s := fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)
#align monotone_on.set_prod MonotoneOn.set_prod

theorem _root_.AntitoneOn.set_prod (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x ×ˢ g x) s := fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)
#align antitone_on.set_prod AntitoneOn.set_prod

end Mono

end Prod

/-! ### Diagonal

In this section we prove some lemmas about the diagonal set `{p | p.1 = p.2}` and the diagonal map
`fun x ↦ (x, x)`.
-/


section Diagonal

variable {α : Type*} {s t : Set α}

lemma diagonal_nonempty [Nonempty α] : (diagonal α).Nonempty :=
  Nonempty.elim ‹_› fun x => ⟨_, mem_diagonal x⟩
#align set.diagonal_nonempty Set.diagonal_nonempty

instance decidableMemDiagonal [h : DecidableEq α] (x : α × α) : Decidable (x ∈ diagonal α) :=
  h x.1 x.2
#align set.decidable_mem_diagonal Set.decidableMemDiagonal

theorem preimage_coe_coe_diagonal (s : Set α) :
    Prod.map (fun x : s => (x : α)) (fun x : s => (x : α)) ⁻¹' diagonal α = diagonal s := by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [Set.diagonal]
#align set.preimage_coe_coe_diagonal Set.preimage_coe_coe_diagonal

@[simp]
theorem range_diag : (range fun x => (x, x)) = diagonal α := by
  ext ⟨x, y⟩
  simp [diagonal, eq_comm]
#align set.range_diag Set.range_diag

theorem diagonal_subset_iff {s} : diagonal α ⊆ s ↔ ∀ x, (x, x) ∈ s := by
  rw [← range_diag, range_subset_iff]
#align set.diagonal_subset_iff Set.diagonal_subset_iff

@[simp]
theorem prod_subset_compl_diagonal_iff_disjoint : s ×ˢ t ⊆ (diagonal α)ᶜ ↔ Disjoint s t :=
  prod_subset_iff.trans disjoint_iff_forall_ne.symm
#align set.prod_subset_compl_diagonal_iff_disjoint Set.prod_subset_compl_diagonal_iff_disjoint

@[simp]
theorem diag_preimage_prod (s t : Set α) : (fun x => (x, x)) ⁻¹' s ×ˢ t = s ∩ t :=
  rfl
#align set.diag_preimage_prod Set.diag_preimage_prod

theorem diag_preimage_prod_self (s : Set α) : (fun x => (x, x)) ⁻¹' s ×ˢ s = s :=
  inter_self s
#align set.diag_preimage_prod_self Set.diag_preimage_prod_self

theorem diag_image (s : Set α) : (fun x => (x, x)) '' s = diagonal α ∩ s ×ˢ s := by
  rw [← range_diag, ← image_preimage_eq_range_inter, diag_preimage_prod_self]
#align set.diag_image Set.diag_image

theorem diagonal_eq_univ_iff : diagonal α = univ ↔ Subsingleton α := by
  simp only [subsingleton_iff, eq_univ_iff_forall, Prod.forall, mem_diagonal_iff]

theorem diagonal_eq_univ [Subsingleton α] : diagonal α = univ := diagonal_eq_univ_iff.2 ‹_›

end Diagonal

/-- A function is `Function.const α a` for some `a` if and only if `∀ x y, f x = f y`. -/
theorem range_const_eq_diagonal {α β : Type*} [hβ : Nonempty β] :
    range (const α) = {f : α → β | ∀ x y, f x = f y} := by
  refine (range_eq_iff _ _).mpr ⟨fun _ _ _ ↦ rfl, fun f hf ↦ ?_⟩
  rcases isEmpty_or_nonempty α with h|⟨⟨a⟩⟩
  · exact hβ.elim fun b ↦ ⟨b, Subsingleton.elim _ _⟩
  · exact ⟨f a, funext fun x ↦ hf _ _⟩

end Set

section Pullback

open Set

variable {X Y Z}

/-- The fiber product $X \times_Y Z$. -/
abbrev Function.Pullback (f : X → Y) (g : Z → Y) := {p : X × Z // f p.1 = g p.2}

/-- The fiber product $X \times_Y X$. -/
abbrev Function.PullbackSelf (f : X → Y) := f.Pullback f

/-- The projection from the fiber product to the first factor. -/
def Function.Pullback.fst {f : X → Y} {g : Z → Y} (p : f.Pullback g) : X := p.val.1

/-- The projection from the fiber product to the second factor. -/
def Function.Pullback.snd {f : X → Y} {g : Z → Y} (p : f.Pullback g) : Z := p.val.2

open Function.Pullback in
lemma Function.pullback_comm_sq (f : X → Y) (g : Z → Y) :
    f ∘ @fst X Y Z f g = g ∘ @snd X Y Z f g := funext fun p ↦ p.2

/-- The diagonal map $\Delta: X \to X \times_Y X$. -/
def toPullbackDiag (f : X → Y) (x : X) : f.Pullback f := ⟨(x, x), rfl⟩

/-- The diagonal $\Delta(X) \subseteq X \times_Y X$. -/
def Function.pullbackDiagonal (f : X → Y) : Set (f.Pullback f) := {p | p.fst = p.snd}

/-- Three functions between the three pairs of spaces $X_i, Y_i, Z_i$ that are compatible
  induce a function $X_1 \times_{Y_1} Z_1 \to X_2 \times_{Y_2} Z_2$. -/
def Function.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
    {f₁ : X₁ → Y₁} {g₁ : Z₁ → Y₁} {f₂ : X₂ → Y₂} {g₂ : Z₂ → Y₂}
    (mapX : X₁ → X₂) (mapY : Y₁ → Y₂) (mapZ : Z₁ → Z₂)
    (commX : f₂ ∘ mapX = mapY ∘ f₁) (commZ : g₂ ∘ mapZ = mapY ∘ g₁)
    (p : f₁.Pullback g₁) : f₂.Pullback g₂ :=
  ⟨(mapX p.fst, mapZ p.snd),
    (congr_fun commX _).trans <| (congr_arg mapY p.2).trans <| congr_fun commZ.symm _⟩

open Function.Pullback in
/-- The projection $(X \times_Y Z) \times_Z (X \times_Y Z) \to X \times_Y X$. -/
def Function.PullbackSelf.map_fst {f : X → Y} {g : Z → Y} :
    (@snd X Y Z f g).PullbackSelf → f.PullbackSelf :=
  mapPullback fst g fst (pullback_comm_sq f g) (pullback_comm_sq f g)

open Function.Pullback in
/-- The projection $(X \times_Y Z) \times_X (X \times_Y Z) \to Z \times_Y Z$. -/
def Function.PullbackSelf.map_snd {f : X → Y} {g : Z → Y} :
    (@fst X Y Z f g).PullbackSelf → g.PullbackSelf :=
  mapPullback snd f snd (pullback_comm_sq f g).symm (pullback_comm_sq f g).symm

open Function.PullbackSelf Function.Pullback
theorem preimage_map_fst_pullbackDiagonal {f : X → Y} {g : Z → Y} :
    @map_fst X Y Z f g ⁻¹' pullbackDiagonal f = pullbackDiagonal (@snd X Y Z f g) := by
  ext ⟨⟨p₁, p₂⟩, he⟩
  simp_rw [pullbackDiagonal, mem_setOf, Subtype.ext_iff, Prod.ext_iff]
  exact (and_iff_left he).symm

theorem Function.Injective.preimage_pullbackDiagonal {f : X → Y} {g : Z → X} (inj : g.Injective) :
    mapPullback g id g (by rfl) (by rfl) ⁻¹' pullbackDiagonal f = pullbackDiagonal (f ∘ g) :=
  ext fun _ ↦ inj.eq_iff

theorem image_toPullbackDiag (f : X → Y) (s : Set X) :
    toPullbackDiag f '' s = pullbackDiagonal f ∩ Subtype.val ⁻¹' s ×ˢ s := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx, hx⟩
  · obtain ⟨⟨x, y⟩, h⟩ := x
    rintro ⟨rfl : x = y, h2x⟩
    exact mem_image_of_mem _ h2x.1

theorem range_toPullbackDiag (f : X → Y) : range (toPullbackDiag f) = pullbackDiagonal f := by
  rw [← image_univ, image_toPullbackDiag, univ_prod_univ, preimage_univ, inter_univ]

theorem injective_toPullbackDiag (f : X → Y) : (toPullbackDiag f).Injective :=
  fun _ _ h ↦ congr_arg Prod.fst (congr_arg Subtype.val h)

end Pullback

namespace Set

section OffDiag

variable {α : Type*} {s t : Set α} {x : α × α} {a : α}

theorem offDiag_mono : Monotone (offDiag : Set α → Set (α × α)) := fun _ _ h _ =>
  And.imp (@h _) <| And.imp_left <| @h _
#align set.off_diag_mono Set.offDiag_mono

@[simp]
theorem offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivial := by
  simp [offDiag, Set.Nonempty, Set.Nontrivial]
#align set.off_diag_nonempty Set.offDiag_nonempty

@[simp]
theorem offDiag_eq_empty : s.offDiag = ∅ ↔ s.Subsingleton := by
  rw [← not_nonempty_iff_eq_empty, ← not_nontrivial_iff, offDiag_nonempty.not]
#align set.off_diag_eq_empty Set.offDiag_eq_empty

alias ⟨_, Nontrivial.offDiag_nonempty⟩ := offDiag_nonempty
#align set.nontrivial.off_diag_nonempty Set.Nontrivial.offDiag_nonempty

alias ⟨_, Subsingleton.offDiag_eq_empty⟩ := offDiag_nonempty
#align set.subsingleton.off_diag_eq_empty Set.Subsingleton.offDiag_eq_empty

variable (s t)

theorem offDiag_subset_prod : s.offDiag ⊆ s ×ˢ s := fun _ hx => ⟨hx.1, hx.2.1⟩
#align set.off_diag_subset_prod Set.offDiag_subset_prod

theorem offDiag_eq_sep_prod : s.offDiag = { x ∈ s ×ˢ s | x.1 ≠ x.2 } :=
  ext fun _ => and_assoc.symm
#align set.off_diag_eq_sep_prod Set.offDiag_eq_sep_prod

@[simp]
theorem offDiag_empty : (∅ : Set α).offDiag = ∅ := by simp
#align set.off_diag_empty Set.offDiag_empty

@[simp]
theorem offDiag_singleton (a : α) : ({a} : Set α).offDiag = ∅ := by simp
#align set.off_diag_singleton Set.offDiag_singleton

@[simp]
theorem offDiag_univ : (univ : Set α).offDiag = (diagonal α)ᶜ :=
  ext <| by simp
#align set.off_diag_univ Set.offDiag_univ

@[simp]
theorem prod_sdiff_diagonal : s ×ˢ s \ diagonal α = s.offDiag :=
  ext fun _ => and_assoc
#align set.prod_sdiff_diagonal Set.prod_sdiff_diagonal

@[simp]
theorem disjoint_diagonal_offDiag : Disjoint (diagonal α) s.offDiag :=
  disjoint_left.mpr fun _ hd ho => ho.2.2 hd
#align set.disjoint_diagonal_off_diag Set.disjoint_diagonal_offDiag

theorem offDiag_inter : (s ∩ t).offDiag = s.offDiag ∩ t.offDiag :=
  ext fun x => by
    simp only [mem_offDiag, mem_inter_iff]
    tauto
#align set.off_diag_inter Set.offDiag_inter

variable {s t}

theorem offDiag_union (h : Disjoint s t) :
    (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s := by
  ext x
  simp only [mem_offDiag, mem_union, ne_eq, mem_prod]
  constructor
  · rintro ⟨h0|h0, h1|h1, h2⟩ <;> simp [h0, h1, h2]
  · rintro (((⟨h0, h1, h2⟩|⟨h0, h1, h2⟩)|⟨h0, h1⟩)|⟨h0, h1⟩) <;> simp [*]
    · rintro h3
      rw [h3] at h0
      exact Set.disjoint_left.mp h h0 h1
    · rintro h3
      rw [h3] at h0
      exact (Set.disjoint_right.mp h h0 h1).elim
#align set.off_diag_union Set.offDiag_union

theorem offDiag_insert (ha : a ∉ s) : (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  rw [insert_eq, union_comm, offDiag_union, offDiag_singleton, union_empty, union_right_comm]
  rw [disjoint_left]
  rintro b hb (rfl : b = a)
  exact ha hb
#align set.off_diag_insert Set.offDiag_insert

end OffDiag

/-! ### Cartesian set-indexed product of sets -/


section Pi

variable {ι : Type*} {α β : ι → Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)} {i : ι}

@[simp]
theorem empty_pi (s : ∀ i, Set (α i)) : pi ∅ s = univ := by
  ext
  simp [pi]
#align set.empty_pi Set.empty_pi

theorem subsingleton_univ_pi (ht : ∀ i, (t i).Subsingleton) :
    (univ.pi t).Subsingleton := fun _f hf _g hg ↦ funext fun i ↦
  (ht i) (hf _ <| mem_univ _) (hg _ <| mem_univ _)

@[simp]
theorem pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = univ :=
  eq_univ_of_forall fun _ _ _ => mem_univ _
#align set.pi_univ Set.pi_univ

@[simp]
theorem pi_univ_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by
  ext; simp_rw [Set.mem_pi]; apply forall_congr'; intro i; split_ifs with h <;> simp [h]

theorem pi_mono (h : ∀ i ∈ s, t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ := fun _ hx i hi => h i hi <| hx i hi
#align set.pi_mono Set.pi_mono

theorem pi_inter_distrib : (s.pi fun i => t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ :=
  ext fun x => by simp only [forall_and, mem_pi, mem_inter_iff]
#align set.pi_inter_distrib Set.pi_inter_distrib

theorem pi_congr (h : s₁ = s₂) (h' : ∀ i ∈ s₁, t₁ i = t₂ i) : s₁.pi t₁ = s₂.pi t₂ :=
  h ▸ ext fun _ => forall₂_congr fun i hi => h' i hi ▸ Iff.rfl
#align set.pi_congr Set.pi_congr

theorem pi_eq_empty (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ := by
  ext f
  simp only [mem_empty_iff_false, not_forall, iff_false_iff, mem_pi, Classical.not_imp]
  exact ⟨i, hs, by simp [ht]⟩
#align set.pi_eq_empty Set.pi_eq_empty

theorem univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht
#align set.univ_pi_eq_empty Set.univ_pi_eq_empty

theorem pi_nonempty_iff : (s.pi t).Nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i := by
  simp [Classical.skolem, Set.Nonempty]
#align set.pi_nonempty_iff Set.pi_nonempty_iff

theorem univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ ∀ i, (t i).Nonempty := by
  simp [Classical.skolem, Set.Nonempty]
#align set.univ_pi_nonempty_iff Set.univ_pi_nonempty_iff

theorem pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅ := by
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff]
  push_neg
  refine exists_congr fun i => ?_
  cases isEmpty_or_nonempty (α i) <;> simp [*, forall_and, eq_empty_iff_forall_not_mem]
#align set.pi_eq_empty_iff Set.pi_eq_empty_iff

@[simp]
theorem univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ := by
  simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]
#align set.univ_pi_eq_empty_iff Set.univ_pi_eq_empty_iff

@[simp]
theorem univ_pi_empty [h : Nonempty ι] : pi univ (fun _ => ∅ : ∀ i, Set (α i)) = ∅ :=
  univ_pi_eq_empty_iff.2 <| h.elim fun x => ⟨x, rfl⟩
#align set.univ_pi_empty Set.univ_pi_empty

@[simp]
theorem disjoint_univ_pi : Disjoint (pi univ t₁) (pi univ t₂) ↔ ∃ i, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, univ_pi_eq_empty_iff]
#align set.disjoint_univ_pi Set.disjoint_univ_pi

theorem Disjoint.set_pi (hi : i ∈ s) (ht : Disjoint (t₁ i) (t₂ i)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_left.2 fun _ h₁ h₂ => disjoint_left.1 ht (h₁ _ hi) (h₂ _ hi)
#align set.disjoint.set_pi Set.Disjoint.set_pi

theorem uniqueElim_preimage [Unique ι] (t : ∀ i, Set (α i)) :
    uniqueElim ⁻¹' pi univ t = t (default : ι) := by ext; simp [Unique.forall_iff]

section Nonempty

variable [∀ i, Nonempty (α i)]

theorem pi_eq_empty_iff' : s.pi t = ∅ ↔ ∃ i ∈ s, t i = ∅ := by simp [pi_eq_empty_iff]
#align set.pi_eq_empty_iff' Set.pi_eq_empty_iff'

@[simp]
theorem disjoint_pi : Disjoint (s.pi t₁) (s.pi t₂) ↔ ∃ i ∈ s, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, pi_eq_empty_iff']
#align set.disjoint_pi Set.disjoint_pi

end Nonempty

-- Porting note: Removing `simp` - LHS does not simplify
theorem range_dcomp (f : ∀ i, α i → β i) :
    (range fun g : ∀ i, α i => fun i => f i (g i)) = pi univ fun i => range (f i) := by
  refine Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨x, rfl⟩ i -
    exact ⟨x i, rfl⟩
  · choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩
#align set.range_dcomp Set.range_dcomp

@[simp]
theorem insert_pi (i : ι) (s : Set ι) (t : ∀ i, Set (α i)) :
    pi (insert i s) t = eval i ⁻¹' t i ∩ pi s t := by
  ext
  simp [pi, or_imp, forall_and]
#align set.insert_pi Set.insert_pi

@[simp]
theorem singleton_pi (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = eval i ⁻¹' t i := by
  ext
  simp [pi]
#align set.singleton_pi Set.singleton_pi

theorem singleton_pi' (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = { x | x i ∈ t i } :=
  singleton_pi i t
#align set.singleton_pi' Set.singleton_pi'

theorem univ_pi_singleton (f : ∀ i, α i) : (pi univ fun i => {f i}) = ({f} : Set (∀ i, α i)) :=
  ext fun g => by simp [funext_iff]
#align set.univ_pi_singleton Set.univ_pi_singleton

theorem preimage_pi (s : Set ι) (t : ∀ i, Set (β i)) (f : ∀ i, α i → β i) :
    (fun (g : ∀ i, α i) i => f _ (g i)) ⁻¹' s.pi t = s.pi fun i => f i ⁻¹' t i :=
  rfl
#align set.preimage_pi Set.preimage_pi

theorem pi_if {p : ι → Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : ∀ i, Set (α i)) :
    (pi s fun i => if p i then t₁ i else t₂ i) =
      pi ({ i ∈ s | p i }) t₁ ∩ pi ({ i ∈ s | ¬p i }) t₂ := by
  ext f
  refine ⟨fun h => ?_, ?_⟩
  · constructor <;>
      · rintro i ⟨his, hpi⟩
        simpa [*] using h i
  · rintro ⟨ht₁, ht₂⟩ i his
    by_cases p i <;> simp_all
#align set.pi_if Set.pi_if

theorem union_pi : (s₁ ∪ s₂).pi t = s₁.pi t ∩ s₂.pi t := by
  simp [pi, or_imp, forall_and, setOf_and]
#align set.union_pi Set.union_pi

theorem union_pi_inter
    (ht₁ : ∀ i ∉ s₁, t₁ i = univ) (ht₂ : ∀ i ∉ s₂, t₂ i = univ) :
    (s₁ ∪ s₂).pi (fun i ↦ t₁ i ∩ t₂ i) = s₁.pi t₁ ∩ s₂.pi t₂ := by
  ext x
  simp only [mem_pi, mem_union, mem_inter_iff]
  refine ⟨fun h ↦ ⟨fun i his₁ ↦ (h i (Or.inl his₁)).1, fun i his₂ ↦ (h i (Or.inr his₂)).2⟩,
    fun h i hi ↦ ?_⟩
  cases' hi with hi hi
  · by_cases hi2 : i ∈ s₂
    · exact ⟨h.1 i hi, h.2 i hi2⟩
    · refine ⟨h.1 i hi, ?_⟩
      rw [ht₂ i hi2]
      exact mem_univ _
  · by_cases hi1 : i ∈ s₁
    · exact ⟨h.1 i hi1, h.2 i hi⟩
    · refine ⟨?_, h.2 i hi⟩
      rw [ht₁ i hi1]
      exact mem_univ _

@[simp]
theorem pi_inter_compl (s : Set ι) : pi s t ∩ pi sᶜ t = pi univ t := by
  rw [← union_pi, union_compl_self]
#align set.pi_inter_compl Set.pi_inter_compl

theorem pi_update_of_not_mem [DecidableEq ι] (hi : i ∉ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) : (s.pi fun j => t j (update f i a j)) = s.pi fun j => t j (f j) :=
  (pi_congr rfl) fun j hj => by
    rw [update_noteq]
    exact fun h => hi (h ▸ hj)
#align set.pi_update_of_not_mem Set.pi_update_of_not_mem

theorem pi_update_of_mem [DecidableEq ι] (hi : i ∈ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (s.pi fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
  calc
    (s.pi fun j => t j (update f i a j)) = ({i} ∪ s \ {i}).pi fun j => t j (update f i a j) := by
        rw [union_diff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) := by
        rw [union_pi, singleton_pi', update_same, pi_update_of_not_mem]; simp
#align set.pi_update_of_mem Set.pi_update_of_mem

theorem univ_pi_update [DecidableEq ι] {β : ι → Type*} (i : ι) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (pi univ fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ pi {i}ᶜ fun j => t j (f j) := by
  rw [compl_eq_univ_diff, ← pi_update_of_mem (mem_univ _)]
#align set.univ_pi_update Set.univ_pi_update

theorem univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) :
    pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻¹' s := by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t, pi_univ, inter_univ, preimage]
#align set.univ_pi_update_univ Set.univ_pi_update_univ

theorem eval_image_pi_subset (hs : i ∈ s) : eval i '' s.pi t ⊆ t i :=
  image_subset_iff.2 fun _ hf => hf i hs
#align set.eval_image_pi_subset Set.eval_image_pi_subset

theorem eval_image_univ_pi_subset : eval i '' pi univ t ⊆ t i :=
  eval_image_pi_subset (mem_univ i)
#align set.eval_image_univ_pi_subset Set.eval_image_univ_pi_subset

theorem subset_eval_image_pi (ht : (s.pi t).Nonempty) (i : ι) : t i ⊆ eval i '' s.pi t := by
  classical
  obtain ⟨f, hf⟩ := ht
  refine fun y hy => ⟨update f i y, fun j hj => ?_, update_same _ _ _⟩
  obtain rfl | hji := eq_or_ne j i <;> simp [*, hf _ hj]
#align set.subset_eval_image_pi Set.subset_eval_image_pi

theorem eval_image_pi (hs : i ∈ s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = t i :=
  (eval_image_pi_subset hs).antisymm (subset_eval_image_pi ht i)
#align set.eval_image_pi Set.eval_image_pi

lemma eval_image_pi_of_not_mem [Decidable (s.pi t).Nonempty] (hi : i ∉ s) :
    eval i '' s.pi t = if (s.pi t).Nonempty then univ else ∅ := by
  classical
  ext xᵢ
  simp only [eval, mem_image, mem_pi, Set.Nonempty, mem_ite_empty_right, mem_univ, and_true]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨Function.update x i xᵢ, ?_⟩
    simpa (config := { contextual := true }) [(ne_of_mem_of_not_mem · hi)]

@[simp]
theorem eval_image_univ_pi (ht : (pi univ t).Nonempty) :
    (fun f : ∀ i, α i => f i) '' pi univ t = t i :=
  eval_image_pi (mem_univ i) ht
#align set.eval_image_univ_pi Set.eval_image_univ_pi

theorem pi_subset_pi_iff : pi s t₁ ⊆ pi s t₂ ↔ (∀ i ∈ s, t₁ i ⊆ t₂ i) ∨ pi s t₁ = ∅ := by
  refine
    ⟨fun h => or_iff_not_imp_right.2 ?_, fun h => h.elim pi_mono fun h' => h'.symm ▸ empty_subset _⟩
  rw [← Ne, ← nonempty_iff_ne_empty]
  intro hne i hi
  simpa only [eval_image_pi hi hne, eval_image_pi hi (hne.mono h)] using
    image_subset (fun f : ∀ i, α i => f i) h
#align set.pi_subset_pi_iff Set.pi_subset_pi_iff

theorem univ_pi_subset_univ_pi_iff :
    pi univ t₁ ⊆ pi univ t₂ ↔ (∀ i, t₁ i ⊆ t₂ i) ∨ ∃ i, t₁ i = ∅ := by simp [pi_subset_pi_iff]
#align set.univ_pi_subset_univ_pi_iff Set.univ_pi_subset_univ_pi_iff

theorem eval_preimage [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun i => univ) i s) := by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]
#align set.eval_preimage Set.eval_preimage

theorem eval_preimage' [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun i => univ) i s) := by
  ext
  simp
#align set.eval_preimage' Set.eval_preimage'

theorem update_preimage_pi [DecidableEq ι] {f : ∀ i, α i} (hi : i ∈ s)
    (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) : update f i ⁻¹' s.pi t = t i := by
  ext x
  refine ⟨fun h => ?_, fun hx j hj => ?_⟩
  · convert h i hi
    simp
  · obtain rfl | h := eq_or_ne j i
    · simpa
    · rw [update_noteq h]
      exact hf j hj h
#align set.update_preimage_pi Set.update_preimage_pi

theorem update_preimage_univ_pi [DecidableEq ι] {f : ∀ i, α i} (hf : ∀ j ≠ i, f j ∈ t j) :
    update f i ⁻¹' pi univ t = t i :=
  update_preimage_pi (mem_univ i) fun j _ => hf j
#align set.update_preimage_univ_pi Set.update_preimage_univ_pi

theorem subset_pi_eval_image (s : Set ι) (u : Set (∀ i, α i)) : u ⊆ pi s fun i => eval i '' u :=
  fun f hf _ _ => ⟨f, hf, rfl⟩
#align set.subset_pi_eval_image Set.subset_pi_eval_image

theorem univ_pi_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by
  ext
  simp_rw [mem_univ_pi]
  refine forall_congr' fun i => ?_
  split_ifs with h <;> simp [h]
#align set.univ_pi_ite Set.univ_pi_ite

end Pi

end Set

namespace Equiv

open Set
variable {ι ι' : Type*} {α : ι → Type*}

theorem piCongrLeft_symm_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : ∀ i, Set (α i)) :
    (f.piCongrLeft α).symm ⁻¹' s.pi (fun i' => t <| f i') = (f '' s).pi t := by
  ext; simp

theorem piCongrLeft_symm_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    (f.piCongrLeft α).symm ⁻¹' univ.pi (fun i' => t <| f i') = univ.pi t := by
  simpa [f.surjective.range_eq] using piCongrLeft_symm_preimage_pi f univ t

theorem piCongrLeft_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : ∀ i, Set (α i)) :
    f.piCongrLeft α ⁻¹' (f '' s).pi t = s.pi fun i => t (f i) := by
  apply Set.ext;
  rw [← (f.piCongrLeft α).symm.forall_congr_left]
  simp

theorem piCongrLeft_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    f.piCongrLeft α ⁻¹' univ.pi t = univ.pi fun i => t (f i) := by
  simpa [f.surjective.range_eq] using piCongrLeft_preimage_pi f univ t

theorem sumPiEquivProdPi_symm_preimage_univ_pi (π : ι ⊕ ι' → Type*) (t : ∀ i, Set (π i)) :
    (sumPiEquivProdPi π).symm ⁻¹' univ.pi t =
    univ.pi (fun i => t (.inl i)) ×ˢ univ.pi fun i => t (.inr i) := by
  ext
  simp_rw [mem_preimage, mem_prod, mem_univ_pi, sumPiEquivProdPi_symm_apply]
  constructor
  · intro h; constructor <;> intro i <;> apply h
  · rintro ⟨h₁, h₂⟩ (i|i) <;> simp <;> apply_assumption

end Equiv
