/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Patrick Massot
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.SProd

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

@[gcongr]
theorem prod_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ :=
  fun _ ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩

@[gcongr]
theorem prod_mono_left (hs : s₁ ⊆ s₂) : s₁ ×ˢ t ⊆ s₂ ×ˢ t :=
  prod_mono hs Subset.rfl

@[gcongr]
theorem prod_mono_right (ht : t₁ ⊆ t₂) : s ×ˢ t₁ ⊆ s ×ˢ t₂ :=
  prod_mono Subset.rfl ht

@[simp]
theorem prod_self_subset_prod_self : s₁ ×ˢ s₁ ⊆ s₂ ×ˢ s₂ ↔ s₁ ⊆ s₂ :=
  ⟨fun h _ hx => (h (mk_mem_prod hx hx)).1, fun h _ hx => ⟨h hx.1, h hx.2⟩⟩

@[simp]
theorem prod_self_ssubset_prod_self : s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂ :=
  and_congr prod_self_subset_prod_self <| not_congr prod_self_subset_prod_self

theorem prod_subset_iff {P : Set (α × β)} : s ×ˢ t ⊆ P ↔ ∀ x ∈ s, ∀ y ∈ t, (x, y) ∈ P :=
  ⟨fun h _ hx _ hy => h (mk_mem_prod hx hy), fun h ⟨_, _⟩ hp => h _ hp.1 _ hp.2⟩

theorem forall_prod_set {p : α × β → Prop} : (∀ x ∈ s ×ˢ t, p x) ↔ ∀ x ∈ s, ∀ y ∈ t, p (x, y) :=
  prod_subset_iff

theorem exists_prod_set {p : α × β → Prop} : (∃ x ∈ s ×ˢ t, p x) ↔ ∃ x ∈ s, ∃ y ∈ t, p (x, y) := by
  simp [and_assoc]

@[simp]
theorem prod_empty : s ×ˢ (∅ : Set β) = ∅ := by
  ext
  exact and_false_iff _

@[simp]
theorem empty_prod : (∅ : Set α) ×ˢ t = ∅ := by
  ext
  exact false_and_iff _

@[simp, mfld_simps]
theorem univ_prod_univ : @univ α ×ˢ @univ β = univ := by
  ext
  exact true_and_iff _

theorem univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t := by simp [prod_eq]

theorem prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s := by simp [prod_eq]

@[simp] lemma prod_eq_univ [Nonempty α] [Nonempty β] : s ×ˢ t = univ ↔ s = univ ∧ t = univ := by
  simp [eq_univ_iff_forall, forall_and]

@[simp]
theorem singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]
theorem prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

theorem singleton_prod_singleton : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := by simp

@[simp]
theorem union_prod : (s₁ ∪ s₂) ×ˢ t = s₁ ×ˢ t ∪ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp [or_and_right]

@[simp]
theorem prod_union : s ×ˢ (t₁ ∪ t₂) = s ×ˢ t₁ ∪ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp [and_or_left]

theorem inter_prod : (s₁ ∩ s₂) ×ˢ t = s₁ ×ˢ t ∩ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp only [← and_and_right, mem_inter_iff, mem_prod]

theorem prod_inter : s ×ˢ (t₁ ∩ t₂) = s ×ˢ t₁ ∩ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp only [← and_and_left, mem_inter_iff, mem_prod]

@[mfld_simps]
theorem prod_inter_prod : s₁ ×ˢ t₁ ∩ s₂ ×ˢ t₂ = (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

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

theorem Disjoint.set_prod_left (hs : Disjoint s₁ s₂) (t₁ t₂ : Set β) :
    Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) :=
  disjoint_left.2 fun ⟨_a, _b⟩ ⟨ha₁, _⟩ ⟨ha₂, _⟩ => disjoint_left.1 hs ha₁ ha₂

theorem Disjoint.set_prod_right (ht : Disjoint t₁ t₂) (s₁ s₂ : Set α) :
    Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) :=
  disjoint_left.2 fun ⟨_a, _b⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩ => disjoint_left.1 ht hb₁ hb₂

theorem insert_prod : insert a s ×ˢ t = Prod.mk a '' t ∪ s ×ˢ t := by
  ext ⟨x, y⟩
  simp (config := { contextual := true }) [image, iff_def, or_imp]

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

theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
    (f ⁻¹' s) ×ˢ (g ⁻¹' t) = (fun p : γ × δ => (f p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl

theorem prod_preimage_left {f : γ → α} :
    (f ⁻¹' s) ×ˢ t = (fun p : γ × β => (f p.1, p.2)) ⁻¹' s ×ˢ t :=
  rfl

theorem prod_preimage_right {g : δ → β} :
    s ×ˢ (g ⁻¹' t) = (fun p : α × δ => (p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl

theorem preimage_prod_map_prod (f : α → β) (g : γ → δ) (s : Set β) (t : Set δ) :
    Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) :=
  rfl

theorem mk_preimage_prod (f : γ → α) (g : γ → β) :
    (fun x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl

@[simp]
theorem mk_preimage_prod_left (hb : b ∈ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = s := by
  ext a
  simp [hb]

@[simp]
theorem mk_preimage_prod_right (ha : a ∈ s) : Prod.mk a ⁻¹' s ×ˢ t = t := by
  ext b
  simp [ha]

@[simp]
theorem mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅ := by
  ext a
  simp [hb]

@[simp]
theorem mk_preimage_prod_right_eq_empty (ha : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅ := by
  ext b
  simp [ha]

theorem mk_preimage_prod_left_eq_if [DecidablePred (· ∈ t)] :
    (fun a => (a, b)) ⁻¹' s ×ˢ t = if b ∈ t then s else ∅ := by split_ifs with h <;> simp [h]

theorem mk_preimage_prod_right_eq_if [DecidablePred (· ∈ s)] :
    Prod.mk a ⁻¹' s ×ˢ t = if a ∈ s then t else ∅ := by split_ifs with h <;> simp [h]

theorem mk_preimage_prod_left_fn_eq_if [DecidablePred (· ∈ t)] (f : γ → α) :
    (fun a => (f a, b)) ⁻¹' s ×ˢ t = if b ∈ t then f ⁻¹' s else ∅ := by
  rw [← mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]

theorem mk_preimage_prod_right_fn_eq_if [DecidablePred (· ∈ s)] (g : δ → β) :
    (fun b => (a, g b)) ⁻¹' s ×ˢ t = if a ∈ s then g ⁻¹' t else ∅ := by
  rw [← mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]

@[simp]
theorem preimage_swap_prod (s : Set α) (t : Set β) : Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s := by
  ext ⟨x, y⟩
  simp [and_comm]

@[simp]
theorem image_swap_prod (s : Set α) (t : Set β) : Prod.swap '' s ×ˢ t = t ×ˢ s := by
  rw [image_swap_eq_preimage_swap, preimage_swap_prod]

theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
    (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t :=
  ext <| by
    simp [-exists_and_right, exists_and_right.symm, and_left_comm, and_assoc, and_comm]

theorem prod_range_range_eq {m₁ : α → γ} {m₂ : β → δ} :
    range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2) :=
  ext <| by simp [range]

@[simp, mfld_simps]
theorem range_prod_map {m₁ : α → γ} {m₂ : β → δ} : range (Prod.map m₁ m₂) = range m₁ ×ˢ range m₂ :=
  prod_range_range_eq.symm

theorem prod_range_univ_eq {m₁ : α → γ} :
    range m₁ ×ˢ (univ : Set β) = range fun p : α × β => (m₁ p.1, p.2) :=
  ext <| by simp [range]

theorem prod_univ_range_eq {m₂ : β → δ} :
    (univ : Set α) ×ˢ range m₂ = range fun p : α × β => (p.1, m₂ p.2) :=
  ext <| by simp [range]

theorem range_pair_subset (f : α → β) (g : α → γ) :
    (range fun x => (f x, g x)) ⊆ range f ×ˢ range g := by
  have : (fun x => (f x, g x)) = Prod.map f g ∘ fun x => (x, x) := funext fun x => rfl
  rw [this, ← range_prod_map]
  apply range_comp_subset_range

theorem Nonempty.prod : s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty := fun ⟨x, hx⟩ ⟨y, hy⟩ =>
  ⟨(x, y), ⟨hx, hy⟩⟩

theorem Nonempty.fst : (s ×ˢ t).Nonempty → s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩

theorem Nonempty.snd : (s ×ˢ t).Nonempty → t.Nonempty := fun ⟨x, hx⟩ => ⟨x.2, hx.2⟩

@[simp]
theorem prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod h.2⟩

@[simp]
theorem prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_or]

theorem prod_sub_preimage_iff {W : Set γ} {f : α × β → γ} :
    s ×ˢ t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W := by simp [subset_def]

theorem image_prod_mk_subset_prod {f : α → β} {g : α → γ} {s : Set α} :
    (fun x => (f x, g x)) '' s ⊆ (f '' s) ×ˢ (g '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact mk_mem_prod (mem_image_of_mem f hx) (mem_image_of_mem g hx)

theorem image_prod_mk_subset_prod_left (hb : b ∈ t) : (fun a => (a, b)) '' s ⊆ s ×ˢ t := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨ha, hb⟩

theorem image_prod_mk_subset_prod_right (ha : a ∈ s) : Prod.mk a '' t ⊆ s ×ˢ t := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨ha, hb⟩

theorem prod_subset_preimage_fst (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.fst ⁻¹' s :=
  inter_subset_left

theorem fst_image_prod_subset (s : Set α) (t : Set β) : Prod.fst '' s ×ˢ t ⊆ s :=
  image_subset_iff.2 <| prod_subset_preimage_fst s t

theorem fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonempty) : Prod.fst '' s ×ˢ t = s :=
  (fst_image_prod_subset _ _).antisymm fun y hy =>
    let ⟨x, hx⟩ := ht
    ⟨(y, x), ⟨hy, hx⟩, rfl⟩

theorem prod_subset_preimage_snd (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.snd ⁻¹' t :=
  inter_subset_right

theorem snd_image_prod_subset (s : Set α) (t : Set β) : Prod.snd '' s ×ˢ t ⊆ t :=
  image_subset_iff.2 <| prod_subset_preimage_snd s t

theorem snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Set β) : Prod.snd '' s ×ˢ t = t :=
  (snd_image_prod_subset _ _).antisymm fun y y_in =>
    let ⟨x, x_in⟩ := hs
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

theorem prod_diff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t := by
  ext x
  by_cases h₁ : x.1 ∈ s₁ <;> by_cases h₂ : x.2 ∈ t₁ <;> simp [*]

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

@[simp]
theorem prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ := by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, and_true_iff, or_iff_left_iff_imp,
    or_false_iff]
  rintro ⟨rfl, rfl⟩
  rfl

section Mono

variable [Preorder α] {f : α → Set β} {g : α → Set γ}

theorem _root_.Monotone.set_prod (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ×ˢ g x :=
  fun _ _ h => prod_mono (hf h) (hg h)

theorem _root_.Antitone.set_prod (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ×ˢ g x :=
  fun _ _ h => prod_mono (hf h) (hg h)

theorem _root_.MonotoneOn.set_prod (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x ×ˢ g x) s := fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

theorem _root_.AntitoneOn.set_prod (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x ×ˢ g x) s := fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

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

instance decidableMemDiagonal [h : DecidableEq α] (x : α × α) : Decidable (x ∈ diagonal α) :=
  h x.1 x.2

theorem preimage_coe_coe_diagonal (s : Set α) :
    Prod.map (fun x : s => (x : α)) (fun x : s => (x : α)) ⁻¹' diagonal α = diagonal s := by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [Set.diagonal]

@[simp]
theorem range_diag : (range fun x => (x, x)) = diagonal α := by
  ext ⟨x, y⟩
  simp [diagonal, eq_comm]

theorem diagonal_subset_iff {s} : diagonal α ⊆ s ↔ ∀ x, (x, x) ∈ s := by
  rw [← range_diag, range_subset_iff]

@[simp]
theorem prod_subset_compl_diagonal_iff_disjoint : s ×ˢ t ⊆ (diagonal α)ᶜ ↔ Disjoint s t :=
  prod_subset_iff.trans disjoint_iff_forall_ne.symm

@[simp]
theorem diag_preimage_prod (s t : Set α) : (fun x => (x, x)) ⁻¹' s ×ˢ t = s ∩ t :=
  rfl

theorem diag_preimage_prod_self (s : Set α) : (fun x => (x, x)) ⁻¹' s ×ˢ s = s :=
  inter_self s

theorem diag_image (s : Set α) : (fun x => (x, x)) '' s = diagonal α ∩ s ×ˢ s := by
  rw [← range_diag, ← image_preimage_eq_range_inter, diag_preimage_prod_self]

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

@[simp]
theorem offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivial := by
  simp [offDiag, Set.Nonempty, Set.Nontrivial]

@[simp]
theorem offDiag_eq_empty : s.offDiag = ∅ ↔ s.Subsingleton := by
  rw [← not_nonempty_iff_eq_empty, ← not_nontrivial_iff, offDiag_nonempty.not]

alias ⟨_, Nontrivial.offDiag_nonempty⟩ := offDiag_nonempty

alias ⟨_, Subsingleton.offDiag_eq_empty⟩ := offDiag_nonempty

variable (s t)

theorem offDiag_subset_prod : s.offDiag ⊆ s ×ˢ s := fun _ hx => ⟨hx.1, hx.2.1⟩

theorem offDiag_eq_sep_prod : s.offDiag = { x ∈ s ×ˢ s | x.1 ≠ x.2 } :=
  ext fun _ => and_assoc.symm

@[simp]
theorem offDiag_empty : (∅ : Set α).offDiag = ∅ := by simp

@[simp]
theorem offDiag_singleton (a : α) : ({a} : Set α).offDiag = ∅ := by simp

@[simp]
theorem offDiag_univ : (univ : Set α).offDiag = (diagonal α)ᶜ :=
  ext <| by simp

@[simp]
theorem prod_sdiff_diagonal : s ×ˢ s \ diagonal α = s.offDiag :=
  ext fun _ => and_assoc

@[simp]
theorem disjoint_diagonal_offDiag : Disjoint (diagonal α) s.offDiag :=
  disjoint_left.mpr fun _ hd ho => ho.2.2 hd

theorem offDiag_inter : (s ∩ t).offDiag = s.offDiag ∩ t.offDiag :=
  ext fun x => by
    simp only [mem_offDiag, mem_inter_iff]
    tauto

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

theorem offDiag_insert (ha : a ∉ s) : (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  rw [insert_eq, union_comm, offDiag_union, offDiag_singleton, union_empty, union_right_comm]
  rw [disjoint_left]
  rintro b hb (rfl : b = a)
  exact ha hb

end OffDiag

/-! ### Cartesian set-indexed product of sets -/


section Pi

variable {ι : Type*} {α β : ι → Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)} {i : ι}

@[simp]
theorem empty_pi (s : ∀ i, Set (α i)) : pi ∅ s = univ := by
  ext
  simp [pi]

theorem subsingleton_univ_pi (ht : ∀ i, (t i).Subsingleton) :
    (univ.pi t).Subsingleton := fun _f hf _g hg ↦ funext fun i ↦
  (ht i) (hf _ <| mem_univ _) (hg _ <| mem_univ _)

@[simp]
theorem pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = univ :=
  eq_univ_of_forall fun _ _ _ => mem_univ _

@[simp]
theorem pi_univ_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by
  ext; simp_rw [Set.mem_pi]; apply forall_congr'; intro i; split_ifs with h <;> simp [h]

theorem pi_mono (h : ∀ i ∈ s, t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ := fun _ hx i hi => h i hi <| hx i hi

theorem pi_inter_distrib : (s.pi fun i => t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ :=
  ext fun x => by simp only [forall_and, mem_pi, mem_inter_iff]

theorem pi_congr (h : s₁ = s₂) (h' : ∀ i ∈ s₁, t₁ i = t₂ i) : s₁.pi t₁ = s₂.pi t₂ :=
  h ▸ ext fun _ => forall₂_congr fun i hi => h' i hi ▸ Iff.rfl

theorem pi_eq_empty (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ := by
  ext f
  simp only [mem_empty_iff_false, not_forall, iff_false_iff, mem_pi, Classical.not_imp]
  exact ⟨i, hs, by simp [ht]⟩

theorem univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht

theorem pi_nonempty_iff : (s.pi t).Nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i := by
  simp [Classical.skolem, Set.Nonempty]

theorem univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ ∀ i, (t i).Nonempty := by
  simp [Classical.skolem, Set.Nonempty]

theorem pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅ := by
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff]
  push_neg
  refine exists_congr fun i => ?_
  cases isEmpty_or_nonempty (α i) <;> simp [*, forall_and, eq_empty_iff_forall_not_mem]

@[simp]
theorem univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ := by
  simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

@[simp]
theorem univ_pi_empty [h : Nonempty ι] : pi univ (fun _ => ∅ : ∀ i, Set (α i)) = ∅ :=
  univ_pi_eq_empty_iff.2 <| h.elim fun x => ⟨x, rfl⟩

@[simp]
theorem disjoint_univ_pi : Disjoint (pi univ t₁) (pi univ t₂) ↔ ∃ i, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, univ_pi_eq_empty_iff]

theorem Disjoint.set_pi (hi : i ∈ s) (ht : Disjoint (t₁ i) (t₂ i)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_left.2 fun _ h₁ h₂ => disjoint_left.1 ht (h₁ _ hi) (h₂ _ hi)

theorem uniqueElim_preimage [Unique ι] (t : ∀ i, Set (α i)) :
    uniqueElim ⁻¹' pi univ t = t (default : ι) := by ext; simp [Unique.forall_iff]

section Nonempty

variable [∀ i, Nonempty (α i)]

theorem pi_eq_empty_iff' : s.pi t = ∅ ↔ ∃ i ∈ s, t i = ∅ := by simp [pi_eq_empty_iff]

@[simp]
theorem disjoint_pi : Disjoint (s.pi t₁) (s.pi t₂) ↔ ∃ i ∈ s, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, pi_eq_empty_iff']

end Nonempty

-- Porting note: Removing `simp` - LHS does not simplify
theorem range_dcomp (f : ∀ i, α i → β i) :
    (range fun g : ∀ i, α i => fun i => f i (g i)) = pi univ fun i => range (f i) := by
  refine Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨x, rfl⟩ i -
    exact ⟨x i, rfl⟩
  · choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩

@[simp]
theorem insert_pi (i : ι) (s : Set ι) (t : ∀ i, Set (α i)) :
    pi (insert i s) t = eval i ⁻¹' t i ∩ pi s t := by
  ext
  simp [pi, or_imp, forall_and]

@[simp]
theorem singleton_pi (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = eval i ⁻¹' t i := by
  ext
  simp [pi]

theorem singleton_pi' (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = { x | x i ∈ t i } :=
  singleton_pi i t

theorem univ_pi_singleton (f : ∀ i, α i) : (pi univ fun i => {f i}) = ({f} : Set (∀ i, α i)) :=
  ext fun g => by simp [funext_iff]

theorem preimage_pi (s : Set ι) (t : ∀ i, Set (β i)) (f : ∀ i, α i → β i) :
    (fun (g : ∀ i, α i) i => f _ (g i)) ⁻¹' s.pi t = s.pi fun i => f i ⁻¹' t i :=
  rfl

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

theorem union_pi : (s₁ ∪ s₂).pi t = s₁.pi t ∩ s₂.pi t := by
  simp [pi, or_imp, forall_and, setOf_and]

theorem union_pi_inter
    (ht₁ : ∀ i ∉ s₁, t₁ i = univ) (ht₂ : ∀ i ∉ s₂, t₂ i = univ) :
    (s₁ ∪ s₂).pi (fun i ↦ t₁ i ∩ t₂ i) = s₁.pi t₁ ∩ s₂.pi t₂ := by
  ext x
  simp only [mem_pi, mem_union, mem_inter_iff]
  refine ⟨fun h ↦ ⟨fun i his₁ ↦ (h i (Or.inl his₁)).1, fun i his₂ ↦ (h i (Or.inr his₂)).2⟩,
    fun h i hi ↦ ?_⟩
  rcases hi with hi | hi
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

theorem pi_update_of_not_mem [DecidableEq ι] (hi : i ∉ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) : (s.pi fun j => t j (update f i a j)) = s.pi fun j => t j (f j) :=
  (pi_congr rfl) fun j hj => by
    rw [update_noteq]
    exact fun h => hi (h ▸ hj)

theorem pi_update_of_mem [DecidableEq ι] (hi : i ∈ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (s.pi fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
  calc
    (s.pi fun j => t j (update f i a j)) = ({i} ∪ s \ {i}).pi fun j => t j (update f i a j) := by
        rw [union_diff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) := by
        rw [union_pi, singleton_pi', update_same, pi_update_of_not_mem]; simp

theorem univ_pi_update [DecidableEq ι] {β : ι → Type*} (i : ι) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (pi univ fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ pi {i}ᶜ fun j => t j (f j) := by
  rw [compl_eq_univ_diff, ← pi_update_of_mem (mem_univ _)]

theorem univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) :
    pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻¹' s := by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t, pi_univ, inter_univ, preimage]

theorem eval_image_pi_subset (hs : i ∈ s) : eval i '' s.pi t ⊆ t i :=
  image_subset_iff.2 fun _ hf => hf i hs

theorem eval_image_univ_pi_subset : eval i '' pi univ t ⊆ t i :=
  eval_image_pi_subset (mem_univ i)

theorem subset_eval_image_pi (ht : (s.pi t).Nonempty) (i : ι) : t i ⊆ eval i '' s.pi t := by
  classical
  obtain ⟨f, hf⟩ := ht
  refine fun y hy => ⟨update f i y, fun j hj => ?_, update_same _ _ _⟩
  obtain rfl | hji := eq_or_ne j i <;> simp [*, hf _ hj]

theorem eval_image_pi (hs : i ∈ s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = t i :=
  (eval_image_pi_subset hs).antisymm (subset_eval_image_pi ht i)

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

theorem dcomp_image_pi {f : ∀ i, α i → β i} (hf : ∀ i ∉ s, Surjective (f i)) (t : ∀ i, Set (α i)) :
    (f _ ∘' ·) '' s.pi t = s.pi fun i ↦ f i '' t i := by
  refine Subset.antisymm (image_subset_iff.2 fun a ha i hi ↦ mem_image_of_mem _ (ha _ hi)) ?_
  intro b hb
  have : ∀ i, ∃ a, f i a = b i ∧ (i ∈ s → a ∈ t i) := by
    intro i
    if hi : i ∈ s then
      exact (hb i hi).imp fun a ⟨hat, hab⟩ ↦ ⟨hab, fun _ ↦ hat⟩
    else
      exact (hf i hi (b i)).imp fun a ha ↦ ⟨ha, (absurd · hi)⟩
  choose a hab hat using this
  exact ⟨a, hat, funext hab⟩

theorem dcomp_image_univ_pi (f : ∀ i, α i → β i) (t : ∀ i, Set (α i)) :
    (f _ ∘' ·) '' univ.pi t = univ.pi fun i ↦ f i '' t i :=
  dcomp_image_pi (by simp) t

theorem pi_subset_pi_iff : pi s t₁ ⊆ pi s t₂ ↔ (∀ i ∈ s, t₁ i ⊆ t₂ i) ∨ pi s t₁ = ∅ := by
  refine
    ⟨fun h => or_iff_not_imp_right.2 ?_, fun h => h.elim pi_mono fun h' => h'.symm ▸ empty_subset _⟩
  rw [← Ne, ← nonempty_iff_ne_empty]
  intro hne i hi
  simpa only [eval_image_pi hi hne, eval_image_pi hi (hne.mono h)] using
    image_subset (fun f : ∀ i, α i => f i) h

theorem univ_pi_subset_univ_pi_iff :
    pi univ t₁ ⊆ pi univ t₂ ↔ (∀ i, t₁ i ⊆ t₂ i) ∨ ∃ i, t₁ i = ∅ := by simp [pi_subset_pi_iff]

theorem eval_preimage [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun i => univ) i s) := by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]

theorem eval_preimage' [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun i => univ) i s) := by
  ext
  simp

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

theorem update_image [DecidableEq ι] (x : (i : ι) → β i) (i : ι) (s : Set (β i)) :
    update x i '' s = Set.univ.pi (update (fun j ↦ {x j}) i s) := by
  ext y
  simp [update_eq_iff, and_left_comm (a := _ ∈ s), forall_update_iff, eq_comm (a := y _)]

theorem update_preimage_univ_pi [DecidableEq ι] {f : ∀ i, α i} (hf : ∀ j ≠ i, f j ∈ t j) :
    update f i ⁻¹' pi univ t = t i :=
  update_preimage_pi (mem_univ i) fun j _ => hf j

theorem subset_pi_eval_image (s : Set ι) (u : Set (∀ i, α i)) : u ⊆ pi s fun i => eval i '' u :=
  fun f hf _ _ => ⟨f, hf, rfl⟩

theorem univ_pi_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by
  ext
  simp_rw [mem_univ_pi]
  refine forall_congr' fun i => ?_
  split_ifs with h <;> simp [h]

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
  apply Set.ext
  rw [← (f.piCongrLeft α).symm.forall_congr_right]
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
