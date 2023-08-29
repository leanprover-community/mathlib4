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

/-- The cartesian product `Set.prod s t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
def prod (s : Set α) (t : Set β) : Set (α × β) :=
  { p | p.1 ∈ s ∧ p.2 ∈ t }
#align set.prod Set.prod

@[default_instance]
instance instSProd : SProd (Set α) (Set β) (Set (α × β)) where
  sprod := Set.prod

theorem prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t :=
  rfl
#align set.prod_eq Set.prod_eq

theorem mem_prod_eq {p : α × β} : (p ∈ s ×ˢ t) = (p.1 ∈ s ∧ p.2 ∈ t) :=
  rfl
#align set.mem_prod_eq Set.mem_prod_eq

@[simp, mfld_simps]
theorem mem_prod {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align set.mem_prod Set.mem_prod

-- Porting note: Removing `simp` as `simp` can prove it
@[mfld_simps]
theorem prod_mk_mem_set_prod_eq : ((a, b) ∈ s ×ˢ t) = (a ∈ s ∧ b ∈ t) :=
  rfl
#align set.prod_mk_mem_set_prod_eq Set.prod_mk_mem_set_prod_eq

theorem mk_mem_prod (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t :=
  ⟨ha, hb⟩
#align set.mk_mem_prod Set.mk_mem_prod

theorem Subsingleton.prod (hs : s.Subsingleton) (ht : t.Subsingleton) :
    (s ×ˢ t).Subsingleton := fun _x hx _y hy ↦
  Prod.ext (hs hx.1 hy.1) (ht hx.2 hy.2)

noncomputable instance decidableMemProd [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ×ˢ t) := fun _ => And.decidable
#align set.decidable_mem_prod Set.decidableMemProd

theorem prod_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ :=
  fun _ ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩
#align set.prod_mono Set.prod_mono

theorem prod_mono_left (hs : s₁ ⊆ s₂) : s₁ ×ˢ t ⊆ s₂ ×ˢ t :=
  prod_mono hs Subset.rfl
#align set.prod_mono_left Set.prod_mono_left

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
  -- 🎉 no goals
#align set.exists_prod_set Set.exists_prod_set

@[simp]
theorem prod_empty : s ×ˢ (∅ : Set β) = ∅ := by
  ext
  -- ⊢ x✝ ∈ s ×ˢ ∅ ↔ x✝ ∈ ∅
  exact and_false_iff _
  -- 🎉 no goals
#align set.prod_empty Set.prod_empty

@[simp]
theorem empty_prod : (∅ : Set α) ×ˢ t = ∅ := by
  ext
  -- ⊢ x✝ ∈ ∅ ×ˢ t ↔ x✝ ∈ ∅
  exact false_and_iff _
  -- 🎉 no goals
#align set.empty_prod Set.empty_prod

@[simp, mfld_simps]
theorem univ_prod_univ : @univ α ×ˢ @univ β = univ := by
  ext
  -- ⊢ x✝ ∈ univ ×ˢ univ ↔ x✝ ∈ univ
  exact true_and_iff _
  -- 🎉 no goals
#align set.univ_prod_univ Set.univ_prod_univ

theorem univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t := by simp [prod_eq]
                                                                           -- 🎉 no goals
#align set.univ_prod Set.univ_prod

theorem prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s := by simp [prod_eq]
                                                                           -- 🎉 no goals
#align set.prod_univ Set.prod_univ

@[simp]
theorem singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ {a} ×ˢ t ↔ (x, y) ∈ Prod.mk a '' t
  simp [and_left_comm, eq_comm]
  -- 🎉 no goals
#align set.singleton_prod Set.singleton_prod

@[simp]
theorem prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s ×ˢ {b} ↔ (x, y) ∈ (fun a => (a, b)) '' s
  simp [and_left_comm, eq_comm]
  -- 🎉 no goals
#align set.prod_singleton Set.prod_singleton

theorem singleton_prod_singleton : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := by simp
                                                                                   -- 🎉 no goals
#align set.singleton_prod_singleton Set.singleton_prod_singleton

@[simp]
theorem union_prod : (s₁ ∪ s₂) ×ˢ t = s₁ ×ˢ t ∪ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ (s₁ ∪ s₂) ×ˢ t ↔ (x, y) ∈ s₁ ×ˢ t ∪ s₂ ×ˢ t
  simp [or_and_right]
  -- 🎉 no goals
#align set.union_prod Set.union_prod

@[simp]
theorem prod_union : s ×ˢ (t₁ ∪ t₂) = s ×ˢ t₁ ∪ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s ×ˢ (t₁ ∪ t₂) ↔ (x, y) ∈ s ×ˢ t₁ ∪ s ×ˢ t₂
  simp [and_or_left]
  -- 🎉 no goals
#align set.prod_union Set.prod_union

theorem inter_prod : (s₁ ∩ s₂) ×ˢ t = s₁ ×ˢ t ∩ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ (s₁ ∩ s₂) ×ˢ t ↔ (x, y) ∈ s₁ ×ˢ t ∩ s₂ ×ˢ t
  simp only [← and_and_right, mem_inter_iff, mem_prod]
  -- 🎉 no goals
#align set.inter_prod Set.inter_prod

theorem prod_inter : s ×ˢ (t₁ ∩ t₂) = s ×ˢ t₁ ∩ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s ×ˢ (t₁ ∩ t₂) ↔ (x, y) ∈ s ×ˢ t₁ ∩ s ×ˢ t₂
  simp only [← and_and_left, mem_inter_iff, mem_prod]
  -- 🎉 no goals
#align set.prod_inter Set.prod_inter

@[mfld_simps]
theorem prod_inter_prod : s₁ ×ˢ t₁ ∩ s₂ ×ˢ t₂ = (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂) := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s₁ ×ˢ t₁ ∩ s₂ ×ˢ t₂ ↔ (x, y) ∈ (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂)
  simp [and_assoc, and_left_comm]
  -- 🎉 no goals
#align set.prod_inter_prod Set.prod_inter_prod

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
  -- ⊢ (x, y) ∈ insert a s ×ˢ t ↔ (x, y) ∈ Prod.mk a '' t ∪ s ×ˢ t
  simp (config := { contextual := true }) [image, iff_def, or_imp, Imp.swap]
  -- 🎉 no goals
#align set.insert_prod Set.insert_prod

theorem prod_insert : s ×ˢ insert b t = (fun a => (a, b)) '' s ∪ s ×ˢ t := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ s ×ˢ insert b t ↔ (x, y) ∈ (fun a => (a, b)) '' s ∪ s ×ˢ t
  -- Porting note: was `simp (config := { contextual := true }) [image, iff_def, or_imp, Imp.swap]`
  simp [image, or_imp]
  -- ⊢ x ∈ s ∧ (y = b ∨ y ∈ t) ↔ (∃ a, a ∈ s ∧ a = x ∧ b = y) ∨ x ∈ s ∧ y ∈ t
  refine ⟨fun h => ?_, fun h => ?_⟩
  -- ⊢ (∃ a, a ∈ s ∧ a = x ∧ b = y) ∨ x ∈ s ∧ y ∈ t
  · obtain ⟨hx, rfl|hy⟩ := h
    -- ⊢ (∃ a, a ∈ s ∧ a = x ∧ y = y) ∨ x ∈ s ∧ y ∈ t
    · exact Or.inl ⟨x, hx, rfl, rfl⟩
      -- 🎉 no goals
    · exact Or.inr ⟨hx, hy⟩
      -- 🎉 no goals
  · obtain ⟨x, hx, rfl, rfl⟩|⟨hx, hy⟩ := h
    -- ⊢ x ∈ s ∧ (b = b ∨ b ∈ t)
    · exact ⟨hx, Or.inl rfl⟩
      -- 🎉 no goals
    · exact ⟨hx, Or.inr hy⟩
      -- 🎉 no goals
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
  -- ⊢ a ∈ (fun a => (a, b)) ⁻¹' s ×ˢ t ↔ a ∈ s
  simp [hb]
  -- 🎉 no goals
#align set.mk_preimage_prod_left Set.mk_preimage_prod_left

@[simp]
theorem mk_preimage_prod_right (ha : a ∈ s) : Prod.mk a ⁻¹' s ×ˢ t = t := by
  ext b
  -- ⊢ b ∈ Prod.mk a ⁻¹' s ×ˢ t ↔ b ∈ t
  simp [ha]
  -- 🎉 no goals
#align set.mk_preimage_prod_right Set.mk_preimage_prod_right

@[simp]
theorem mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅ := by
  ext a
  -- ⊢ a ∈ (fun a => (a, b)) ⁻¹' s ×ˢ t ↔ a ∈ ∅
  simp [hb]
  -- 🎉 no goals
#align set.mk_preimage_prod_left_eq_empty Set.mk_preimage_prod_left_eq_empty

@[simp]
theorem mk_preimage_prod_right_eq_empty (ha : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅ := by
  ext b
  -- ⊢ b ∈ Prod.mk a ⁻¹' s ×ˢ t ↔ b ∈ ∅
  simp [ha]
  -- 🎉 no goals
#align set.mk_preimage_prod_right_eq_empty Set.mk_preimage_prod_right_eq_empty

theorem mk_preimage_prod_left_eq_if [DecidablePred (· ∈ t)] :
    (fun a => (a, b)) ⁻¹' s ×ˢ t = if b ∈ t then s else ∅ := by split_ifs with h <;> simp [h]
                                                                -- ⊢ (fun a => (a, b)) ⁻¹' s ×ˢ t = s
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
#align set.mk_preimage_prod_left_eq_if Set.mk_preimage_prod_left_eq_if

theorem mk_preimage_prod_right_eq_if [DecidablePred (· ∈ s)] :
    Prod.mk a ⁻¹' s ×ˢ t = if a ∈ s then t else ∅ := by split_ifs with h <;> simp [h]
                                                        -- ⊢ Prod.mk a ⁻¹' s ×ˢ t = t
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
#align set.mk_preimage_prod_right_eq_if Set.mk_preimage_prod_right_eq_if

theorem mk_preimage_prod_left_fn_eq_if [DecidablePred (· ∈ t)] (f : γ → α) :
    (fun a => (f a, b)) ⁻¹' s ×ˢ t = if b ∈ t then f ⁻¹' s else ∅ := by
  rw [← mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]
  -- 🎉 no goals
#align set.mk_preimage_prod_left_fn_eq_if Set.mk_preimage_prod_left_fn_eq_if

theorem mk_preimage_prod_right_fn_eq_if [DecidablePred (· ∈ s)] (g : δ → β) :
    (fun b => (a, g b)) ⁻¹' s ×ˢ t = if a ∈ s then g ⁻¹' t else ∅ := by
  rw [← mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]
  -- 🎉 no goals
#align set.mk_preimage_prod_right_fn_eq_if Set.mk_preimage_prod_right_fn_eq_if

@[simp]
theorem preimage_swap_prod (s : Set α) (t : Set β) : Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ Prod.swap ⁻¹' s ×ˢ t ↔ (x, y) ∈ t ×ˢ s
  simp [and_comm]
  -- 🎉 no goals
#align set.preimage_swap_prod Set.preimage_swap_prod

@[simp]
theorem image_swap_prod (s : Set α) (t : Set β) : Prod.swap '' s ×ˢ t = t ×ˢ s := by
  rw [image_swap_eq_preimage_swap, preimage_swap_prod]
  -- 🎉 no goals
#align set.image_swap_prod Set.image_swap_prod

theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
    (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t :=
  ext <| by
    simp [-exists_and_right, exists_and_right.symm, and_left_comm, and_assoc, and_comm]
    -- 🎉 no goals
#align set.prod_image_image_eq Set.prod_image_image_eq

theorem prod_range_range_eq {m₁ : α → γ} {m₂ : β → δ} :
    range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2) :=
  ext <| by simp [range]
            -- 🎉 no goals
#align set.prod_range_range_eq Set.prod_range_range_eq

@[simp, mfld_simps]
theorem range_prod_map {m₁ : α → γ} {m₂ : β → δ} : range (Prod.map m₁ m₂) = range m₁ ×ˢ range m₂ :=
  prod_range_range_eq.symm
#align set.range_prod_map Set.range_prod_map

theorem prod_range_univ_eq {m₁ : α → γ} :
    range m₁ ×ˢ (univ : Set β) = range fun p : α × β => (m₁ p.1, p.2) :=
  ext <| by simp [range]
            -- 🎉 no goals
#align set.prod_range_univ_eq Set.prod_range_univ_eq

theorem prod_univ_range_eq {m₂ : β → δ} :
    (univ : Set α) ×ˢ range m₂ = range fun p : α × β => (p.1, m₂ p.2) :=
  ext <| by simp [range]
            -- 🎉 no goals
#align set.prod_univ_range_eq Set.prod_univ_range_eq

theorem range_pair_subset (f : α → β) (g : α → γ) :
    (range fun x => (f x, g x)) ⊆ range f ×ˢ range g := by
  have : (fun x => (f x, g x)) = Prod.map f g ∘ fun x => (x, x) := funext fun x => rfl
  -- ⊢ (range fun x => (f x, g x)) ⊆ range f ×ˢ range g
  rw [this, ← range_prod_map]
  -- ⊢ range (Prod.map f g ∘ fun x => (x, x)) ⊆ range (Prod.map f g)
  apply range_comp_subset_range
  -- 🎉 no goals
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
  -- 🎉 no goals
#align set.prod_eq_empty_iff Set.prod_eq_empty_iff

theorem prod_sub_preimage_iff {W : Set γ} {f : α × β → γ} :
    s ×ˢ t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W := by simp [subset_def]
                                                                 -- 🎉 no goals
#align set.prod_sub_preimage_iff Set.prod_sub_preimage_iff

theorem image_prod_mk_subset_prod {f : α → β} {g : α → γ} {s : Set α} :
    (fun x => (f x, g x)) '' s ⊆ (f '' s) ×ˢ (g '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  -- ⊢ (fun x => (f x, g x)) x ∈ (f '' s) ×ˢ (g '' s)
  exact mk_mem_prod (mem_image_of_mem f hx) (mem_image_of_mem g hx)
  -- 🎉 no goals
#align set.image_prod_mk_subset_prod Set.image_prod_mk_subset_prod

theorem image_prod_mk_subset_prod_left (hb : b ∈ t) : (fun a => (a, b)) '' s ⊆ s ×ˢ t := by
  rintro _ ⟨a, ha, rfl⟩
  -- ⊢ (fun a => (a, b)) a ∈ s ×ˢ t
  exact ⟨ha, hb⟩
  -- 🎉 no goals
#align set.image_prod_mk_subset_prod_left Set.image_prod_mk_subset_prod_left

theorem image_prod_mk_subset_prod_right (ha : a ∈ s) : Prod.mk a '' t ⊆ s ×ˢ t := by
  rintro _ ⟨b, hb, rfl⟩
  -- ⊢ (a, b) ∈ s ×ˢ t
  exact ⟨ha, hb⟩
  -- 🎉 no goals
#align set.image_prod_mk_subset_prod_right Set.image_prod_mk_subset_prod_right

theorem prod_subset_preimage_fst (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.fst ⁻¹' s :=
  inter_subset_left _ _
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
  inter_subset_right _ _
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
  -- ⊢ x ∈ s ×ˢ t \ s₁ ×ˢ t₁ ↔ x ∈ s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t
  by_cases h₁ : x.1 ∈ s₁ <;> by_cases h₂ : x.2 ∈ t₁ <;> simp [*]
  -- ⊢ x ∈ s ×ˢ t \ s₁ ×ˢ t₁ ↔ x ∈ s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t
                             -- ⊢ x ∈ s ×ˢ t \ s₁ ×ˢ t₁ ↔ x ∈ s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t
                             -- ⊢ x ∈ s ×ˢ t \ s₁ ×ˢ t₁ ↔ x ∈ s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align set.prod_diff_prod Set.prod_diff_prod

/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
theorem prod_subset_prod_iff : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  cases' (s ×ˢ t).eq_empty_or_nonempty with h h
  -- ⊢ s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅
  · simp [h, prod_eq_empty_iff.1 h]
    -- 🎉 no goals
  have st : s.Nonempty ∧ t.Nonempty := by rwa [prod_nonempty_iff] at h
  -- ⊢ s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅
  refine' ⟨fun H => Or.inl ⟨_, _⟩, _⟩
  · have := image_subset (Prod.fst : α × β → α) H
    -- ⊢ s ⊆ s₁
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H).snd] at this
    -- 🎉 no goals
  · have := image_subset (Prod.snd : α × β → β) H
    -- ⊢ t ⊆ t₁
    rwa [snd_image_prod st.1, snd_image_prod (h.mono H).fst] at this
    -- 🎉 no goals
  · intro H
    -- ⊢ s ×ˢ t ⊆ s₁ ×ˢ t₁
    simp only [st.1.ne_empty, st.2.ne_empty, or_false_iff] at H
    -- ⊢ s ×ˢ t ⊆ s₁ ×ˢ t₁
    exact prod_mono H.1 H.2
    -- 🎉 no goals
#align set.prod_subset_prod_iff Set.prod_subset_prod_iff

theorem prod_eq_prod_iff_of_nonempty (h : (s ×ˢ t).Nonempty) :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ := by
  constructor
  -- ⊢ s ×ˢ t = s₁ ×ˢ t₁ → s = s₁ ∧ t = t₁
  · intro heq
    -- ⊢ s = s₁ ∧ t = t₁
    have h₁ : (s₁ ×ˢ t₁ : Set _).Nonempty := by rwa [← heq]
    -- ⊢ s = s₁ ∧ t = t₁
    rw [prod_nonempty_iff] at h h₁
    -- ⊢ s = s₁ ∧ t = t₁
    rw [← fst_image_prod s h.2, ← fst_image_prod s₁ h₁.2, heq, eq_self_iff_true, true_and_iff, ←
      snd_image_prod h.1 t, ← snd_image_prod h₁.1 t₁, heq]
  · rintro ⟨rfl, rfl⟩
    -- ⊢ s ×ˢ t = s ×ˢ t
    rfl
    -- 🎉 no goals
#align set.prod_eq_prod_iff_of_nonempty Set.prod_eq_prod_iff_of_nonempty

theorem prod_eq_prod_iff :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) := by
  symm
  -- ⊢ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) ↔ s ×ˢ t = s₁ ×ˢ t₁
  cases' eq_empty_or_nonempty (s ×ˢ t) with h h
  -- ⊢ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) ↔ s ×ˢ t = s₁ ×ˢ t₁
  · simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_and_iff,
      or_iff_right_iff_imp]
    rintro ⟨rfl, rfl⟩
    -- ⊢ s = ∅ ∨ t = ∅
    exact prod_eq_empty_iff.mp h
    -- 🎉 no goals
  rw [prod_eq_prod_iff_of_nonempty h]
  -- ⊢ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) ↔ s = s₁ ∧ t = t₁
  rw [nonempty_iff_ne_empty, Ne.def, prod_eq_empty_iff] at h
  -- ⊢ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) ↔ s = s₁ ∧ t = t₁
  simp_rw [h, false_and_iff, or_false_iff]
  -- 🎉 no goals
#align set.prod_eq_prod_iff Set.prod_eq_prod_iff

@[simp]
theorem prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ := by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, and_true_iff, or_iff_left_iff_imp,
    or_false_iff]
  rintro ⟨rfl, rfl⟩
  -- ⊢ ∅ = ∅
  rfl
  -- 🎉 no goals
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

/-- `diagonal α` is the set of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type*) : Set (α × α) :=
  { p | p.1 = p.2 }
#align set.diagonal Set.diagonal

theorem mem_diagonal (x : α) : (x, x) ∈ diagonal α := by simp [diagonal]
                                                         -- 🎉 no goals
#align set.mem_diagonal Set.mem_diagonal

@[simp]
theorem mem_diagonal_iff {x : α × α} : x ∈ diagonal α ↔ x.1 = x.2 :=
  Iff.rfl
#align set.mem_diagonal_iff Set.mem_diagonal_iff

lemma diagonal_nonempty [Nonempty α] : (diagonal α).Nonempty :=
  Nonempty.elim ‹_› <| fun x => ⟨_, mem_diagonal x⟩
#align set.diagonal_nonempty Set.diagonal_nonempty

instance decidableMemDiagonal [h : DecidableEq α] (x : α × α) : Decidable (x ∈ diagonal α) :=
  h x.1 x.2
#align set.decidable_mem_diagonal Set.decidableMemDiagonal

theorem preimage_coe_coe_diagonal (s : Set α) :
    Prod.map (fun x : s => (x : α)) (fun x : s => (x : α)) ⁻¹' diagonal α = diagonal s := by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  -- ⊢ ({ val := x, property := hx }, { val := y, property := hy }) ∈ (Prod.map (fu …
  simp [Set.diagonal]
  -- 🎉 no goals
#align set.preimage_coe_coe_diagonal Set.preimage_coe_coe_diagonal

@[simp]
theorem range_diag : (range fun x => (x, x)) = diagonal α := by
  ext ⟨x, y⟩
  -- ⊢ ((x, y) ∈ range fun x => (x, x)) ↔ (x, y) ∈ diagonal α
  simp [diagonal, eq_comm]
  -- 🎉 no goals
#align set.range_diag Set.range_diag

theorem diagonal_subset_iff {s} : diagonal α ⊆ s ↔ ∀ x, (x, x) ∈ s := by
  rw [← range_diag, range_subset_iff]
  -- 🎉 no goals
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
  ext x
  -- ⊢ x ∈ (fun x => (x, x)) '' s ↔ x ∈ diagonal α ∩ s ×ˢ s
  constructor
  -- ⊢ x ∈ (fun x => (x, x)) '' s → x ∈ diagonal α ∩ s ×ˢ s
  · rintro ⟨x, hx, rfl⟩
    -- ⊢ (fun x => (x, x)) x ∈ diagonal α ∩ s ×ˢ s
    exact ⟨rfl, hx, hx⟩
    -- 🎉 no goals
  · obtain ⟨x, y⟩ := x
    -- ⊢ (x, y) ∈ diagonal α ∩ s ×ˢ s → (x, y) ∈ (fun x => (x, x)) '' s
    rintro ⟨rfl : x = y, h2x⟩
    -- ⊢ (x, x) ∈ (fun x => (x, x)) '' s
    exact mem_image_of_mem _ h2x.1
    -- 🎉 no goals
#align set.diag_image Set.diag_image

end Diagonal

section OffDiag

variable {α : Type*} {s t : Set α} {x : α × α} {a : α}

/-- The off-diagonal of a set `s` is the set of pairs `(a, b)` with `a, b ∈ s` and `a ≠ b`. -/
def offDiag (s : Set α) : Set (α × α) :=
  { x | x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 }
#align set.off_diag Set.offDiag

@[simp]
theorem mem_offDiag : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
  Iff.rfl
#align set.mem_off_diag Set.mem_offDiag

theorem offDiag_mono : Monotone (offDiag : Set α → Set (α × α)) := fun _ _ h _ =>
  And.imp (@h _) <| And.imp_left <| @h _
#align set.off_diag_mono Set.offDiag_mono

@[simp]
theorem offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivial := by
  simp [offDiag, Set.Nonempty, Set.Nontrivial]
  -- 🎉 no goals
#align set.off_diag_nonempty Set.offDiag_nonempty

@[simp]
theorem offDiag_eq_empty : s.offDiag = ∅ ↔ s.Subsingleton := by
  rw [← not_nonempty_iff_eq_empty, ← not_nontrivial_iff, offDiag_nonempty.not]
  -- 🎉 no goals
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
                                                      -- 🎉 no goals
#align set.off_diag_empty Set.offDiag_empty

@[simp]
theorem offDiag_singleton (a : α) : ({a} : Set α).offDiag = ∅ := by simp
                                                                    -- 🎉 no goals
#align set.off_diag_singleton Set.offDiag_singleton

@[simp]
theorem offDiag_univ : (univ : Set α).offDiag = (diagonal α)ᶜ :=
  ext <| by simp
            -- 🎉 no goals
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
    -- ⊢ (x.fst ∈ s ∧ x.fst ∈ t) ∧ (x.snd ∈ s ∧ x.snd ∈ t) ∧ x.fst ≠ x.snd ↔ (x.fst ∈ …
    tauto
    -- 🎉 no goals
#align set.off_diag_inter Set.offDiag_inter

variable {s t}

theorem offDiag_union (h : Disjoint s t) :
    (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s := by
  ext x
  -- ⊢ x ∈ offDiag (s ∪ t) ↔ x ∈ offDiag s ∪ offDiag t ∪ s ×ˢ t ∪ t ×ˢ s
  simp only [mem_offDiag, mem_union, ne_eq, mem_prod]
  -- ⊢ (x.fst ∈ s ∨ x.fst ∈ t) ∧ (x.snd ∈ s ∨ x.snd ∈ t) ∧ ¬x.fst = x.snd ↔ ((x.fst …
  constructor
  -- ⊢ (x.fst ∈ s ∨ x.fst ∈ t) ∧ (x.snd ∈ s ∨ x.snd ∈ t) ∧ ¬x.fst = x.snd → ((x.fst …
  · rintro ⟨h0|h0, h1|h1, h2⟩ <;> simp [h0, h1, h2]
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
  · rintro (((⟨h0, h1, h2⟩|⟨h0, h1, h2⟩)|⟨h0, h1⟩)|⟨h0, h1⟩) <;> simp [*]
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- ⊢ ¬x.fst = x.snd
                                                                 -- ⊢ ¬x.fst = x.snd
    · rintro h3
      -- ⊢ False
      rw [h3] at h0
      -- ⊢ False
      exact (Set.disjoint_left.mp h h0 h1)
      -- 🎉 no goals
    · rintro h3
      -- ⊢ False
      rw [h3] at h0
      -- ⊢ False
      exact (Set.disjoint_right.mp h h0 h1).elim
      -- 🎉 no goals
#align set.off_diag_union Set.offDiag_union

theorem offDiag_insert (ha : a ∉ s) : (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  rw [insert_eq, union_comm, offDiag_union, offDiag_singleton, union_empty, union_right_comm]
  -- ⊢ Disjoint s {a}
  rw [disjoint_left]
  -- ⊢ ∀ ⦃a_1 : α⦄, a_1 ∈ s → ¬a_1 ∈ {a}
  rintro b hb (rfl : b = a)
  -- ⊢ False
  exact ha hb
  -- 🎉 no goals
#align set.off_diag_insert Set.offDiag_insert

end OffDiag

/-! ### Cartesian set-indexed product of sets -/


section Pi

variable {ι : Type*} {α β : ι → Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)} {i : ι}

/-- Given an index set `ι` and a family of sets `t : Π i, Set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `t a`
whenever `a ∈ s`. -/
def pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) :=
  { f | ∀ i ∈ s, f i ∈ t i }
#align set.pi Set.pi

@[simp]
theorem mem_pi {f : ∀ i, α i} : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i :=
  Iff.rfl
#align set.mem_pi Set.mem_pi

-- Porting note: Removing `simp` as `simp` can prove it
theorem mem_univ_pi {f : ∀ i, α i} : f ∈ pi univ t ↔ ∀ i, f i ∈ t i := by simp
                                                                          -- 🎉 no goals
#align set.mem_univ_pi Set.mem_univ_pi

@[simp]
theorem empty_pi (s : ∀ i, Set (α i)) : pi ∅ s = univ := by
  ext
  -- ⊢ x✝ ∈ pi ∅ s ↔ x✝ ∈ univ
  simp [pi]
  -- 🎉 no goals
#align set.empty_pi Set.empty_pi

theorem subsingleton_univ_pi (ht : ∀ i, (t i).Subsingleton) :
    (univ.pi t).Subsingleton := fun _f hf _g hg ↦ funext fun i ↦
  (ht i) (hf _ <| mem_univ _) (hg _ <| mem_univ _)

@[simp]
theorem pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = univ :=
  eq_univ_of_forall fun _ _ _ => mem_univ _
#align set.pi_univ Set.pi_univ

theorem pi_mono (h : ∀ i ∈ s, t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ := fun _ hx i hi => h i hi <| hx i hi
#align set.pi_mono Set.pi_mono

theorem pi_inter_distrib : (s.pi fun i => t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ :=
  ext fun x => by simp only [forall_and, mem_pi, mem_inter_iff]
                  -- 🎉 no goals
#align set.pi_inter_distrib Set.pi_inter_distrib

theorem pi_congr (h : s₁ = s₂) (h' : ∀ i ∈ s₁, t₁ i = t₂ i) : s₁.pi t₁ = s₂.pi t₂ :=
  h ▸ ext fun _ => forall₂_congr fun i hi => h' i hi ▸ Iff.rfl
#align set.pi_congr Set.pi_congr

theorem pi_eq_empty (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ := by
  ext f
  -- ⊢ f ∈ pi s t ↔ f ∈ ∅
  simp only [mem_empty_iff_false, not_forall, iff_false_iff, mem_pi, not_imp]
  -- ⊢ ∃ x, x ∈ s ∧ ¬f x ∈ t x
  exact ⟨i, hs, by simp [ht]⟩
  -- 🎉 no goals
#align set.pi_eq_empty Set.pi_eq_empty

theorem univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht
#align set.univ_pi_eq_empty Set.univ_pi_eq_empty

theorem pi_nonempty_iff : (s.pi t).Nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i := by
  simp [Classical.skolem, Set.Nonempty]
  -- 🎉 no goals
#align set.pi_nonempty_iff Set.pi_nonempty_iff

theorem univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ ∀ i, (t i).Nonempty := by
  simp [Classical.skolem, Set.Nonempty]
  -- 🎉 no goals
#align set.univ_pi_nonempty_iff Set.univ_pi_nonempty_iff

theorem pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅ := by
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff]
  -- ⊢ (¬∀ (i : ι), ∃ x, i ∈ s → x ∈ t i) ↔ ∃ i, IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅
  push_neg
  -- ⊢ (∃ i, ∀ (x : α i), i ∈ s ∧ ¬x ∈ t i) ↔ ∃ i, IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅
  refine' exists_congr fun i => _
  -- ⊢ (∀ (x : α i), i ∈ s ∧ ¬x ∈ t i) ↔ IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅
  cases isEmpty_or_nonempty (α i) <;> simp [*, forall_and, eq_empty_iff_forall_not_mem]
  -- ⊢ (∀ (x : α i), i ∈ s ∧ ¬x ∈ t i) ↔ IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅
                                      -- 🎉 no goals
                                      -- 🎉 no goals
#align set.pi_eq_empty_iff Set.pi_eq_empty_iff

@[simp]
theorem univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ := by
  simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]
  -- 🎉 no goals
#align set.univ_pi_eq_empty_iff Set.univ_pi_eq_empty_iff

@[simp]
theorem univ_pi_empty [h : Nonempty ι] : pi univ (fun _ => ∅ : ∀ i, Set (α i)) = ∅ :=
  univ_pi_eq_empty_iff.2 <| h.elim fun x => ⟨x, rfl⟩
#align set.univ_pi_empty Set.univ_pi_empty

@[simp]
theorem disjoint_univ_pi : Disjoint (pi univ t₁) (pi univ t₂) ↔ ∃ i, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, univ_pi_eq_empty_iff]
  -- 🎉 no goals
#align set.disjoint_univ_pi Set.disjoint_univ_pi

theorem Disjoint.set_pi (hi : i ∈ s) (ht : Disjoint (t₁ i) (t₂ i)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_left.2 fun _ h₁ h₂ => disjoint_left.1 ht (h₁ _ hi) (h₂ _ hi)
#align set.disjoint.set_pi Set.Disjoint.set_pi

section Nonempty

variable [∀ i, Nonempty (α i)]

theorem pi_eq_empty_iff' : s.pi t = ∅ ↔ ∃ i ∈ s, t i = ∅ := by simp [pi_eq_empty_iff]
                                                               -- 🎉 no goals
#align set.pi_eq_empty_iff' Set.pi_eq_empty_iff'

@[simp]
theorem disjoint_pi : Disjoint (s.pi t₁) (s.pi t₂) ↔ ∃ i ∈ s, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, pi_eq_empty_iff']
  -- 🎉 no goals
#align set.disjoint_pi Set.disjoint_pi

end Nonempty

-- Porting note: Removing `simp` - LHS does not simplify
theorem range_dcomp (f : ∀ i, α i → β i) :
    (range fun g : ∀ i, α i => fun i => f i (g i)) = pi univ fun i => range (f i) := by
  refine Subset.antisymm ?_ fun x hx => ?_
  -- ⊢ (range fun g i => f i (g i)) ⊆ pi univ fun i => range (f i)
  · rintro _ ⟨x, rfl⟩ i -
    -- ⊢ (fun g i => f i (g i)) x i ∈ (fun i => range (f i)) i
    exact ⟨x i, rfl⟩
    -- 🎉 no goals
  · choose y hy using hx
    -- ⊢ x ∈ range fun g i => f i (g i)
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩
    -- 🎉 no goals
#align set.range_dcomp Set.range_dcomp

@[simp]
theorem insert_pi (i : ι) (s : Set ι) (t : ∀ i, Set (α i)) :
    pi (insert i s) t = eval i ⁻¹' t i ∩ pi s t := by
  ext
  -- ⊢ x✝ ∈ pi (insert i s) t ↔ x✝ ∈ eval i ⁻¹' t i ∩ pi s t
  simp [pi, or_imp, forall_and]
  -- 🎉 no goals
#align set.insert_pi Set.insert_pi

@[simp]
theorem singleton_pi (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = eval i ⁻¹' t i := by
  ext
  -- ⊢ x✝ ∈ pi {i} t ↔ x✝ ∈ eval i ⁻¹' t i
  simp [pi]
  -- 🎉 no goals
#align set.singleton_pi Set.singleton_pi

theorem singleton_pi' (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = { x | x i ∈ t i } :=
  singleton_pi i t
#align set.singleton_pi' Set.singleton_pi'

theorem univ_pi_singleton (f : ∀ i, α i) : (pi univ fun i => {f i}) = ({f} : Set (∀ i, α i)) :=
  ext fun g => by simp [funext_iff]
                  -- 🎉 no goals
#align set.univ_pi_singleton Set.univ_pi_singleton

theorem preimage_pi (s : Set ι) (t : ∀ i, Set (β i)) (f : ∀ i, α i → β i) :
    (fun (g : ∀ i, α i) i => f _ (g i)) ⁻¹' s.pi t = s.pi fun i => f i ⁻¹' t i :=
  rfl
#align set.preimage_pi Set.preimage_pi

theorem pi_if {p : ι → Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : ∀ i, Set (α i)) :
    (pi s fun i => if p i then t₁ i else t₂ i) =
      pi ({ i ∈ s | p i }) t₁ ∩ pi ({ i ∈ s | ¬p i }) t₂ := by
  ext f
  -- ⊢ (f ∈ pi s fun i => if p i then t₁ i else t₂ i) ↔ f ∈ pi {i | i ∈ s ∧ p i} t₁ …
  refine' ⟨fun h => _, _⟩
  -- ⊢ f ∈ pi {i | i ∈ s ∧ p i} t₁ ∩ pi {i | i ∈ s ∧ ¬p i} t₂
  · constructor <;>
    -- ⊢ f ∈ pi {i | i ∈ s ∧ p i} t₁
      · rintro i ⟨his, hpi⟩
        -- ⊢ f i ∈ t₁ i
        -- ⊢ f i ∈ t₂ i
        -- 🎉 no goals
        simpa [*] using h i
        -- 🎉 no goals
  · rintro ⟨ht₁, ht₂⟩ i his
    -- ⊢ f i ∈ (fun i => if p i then t₁ i else t₂ i) i
    by_cases p i <;> simp_all
    -- ⊢ f i ∈ (fun i => if p i then t₁ i else t₂ i) i
    -- ⊢ f i ∈ (fun i => if p i then t₁ i else t₂ i) i
                     -- 🎉 no goals
                     -- 🎉 no goals
#align set.pi_if Set.pi_if

theorem union_pi : (s₁ ∪ s₂).pi t = s₁.pi t ∩ s₂.pi t := by
  simp [pi, or_imp, forall_and, setOf_and]
  -- 🎉 no goals
#align set.union_pi Set.union_pi

@[simp]
theorem pi_inter_compl (s : Set ι) : pi s t ∩ pi sᶜ t = pi univ t := by
  rw [← union_pi, union_compl_self]
  -- 🎉 no goals
#align set.pi_inter_compl Set.pi_inter_compl

theorem pi_update_of_not_mem [DecidableEq ι] (hi : i ∉ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) : (s.pi fun j => t j (update f i a j)) = s.pi fun j => t j (f j) :=
  (pi_congr rfl) fun j hj => by
    rw [update_noteq]
    -- ⊢ j ≠ i
    exact fun h => hi (h ▸ hj)
    -- 🎉 no goals
#align set.pi_update_of_not_mem Set.pi_update_of_not_mem

theorem pi_update_of_mem [DecidableEq ι] (hi : i ∈ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (s.pi fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
  calc
    (s.pi fun j => t j (update f i a j)) = ({i} ∪ s \ {i}).pi fun j => t j (update f i a j) :=
        by rw [union_diff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
           -- 🎉 no goals
    _ = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
        by rw [union_pi, singleton_pi', update_same, pi_update_of_not_mem]; simp
           -- ⊢ ¬i ∈ s \ {i}
                                                                            -- 🎉 no goals
#align set.pi_update_of_mem Set.pi_update_of_mem

theorem univ_pi_update [DecidableEq ι] {β : ∀ _, Type*} (i : ι) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (pi univ fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ pi {i}ᶜ fun j => t j (f j) :=
  by rw [compl_eq_univ_diff, ← pi_update_of_mem (mem_univ _)]
     -- 🎉 no goals
#align set.univ_pi_update Set.univ_pi_update

theorem univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) :
    pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻¹' s := by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t, pi_univ, inter_univ, preimage]
  -- 🎉 no goals
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
  refine' fun y hy => ⟨update f i y, fun j hj => _, update_same _ _ _⟩
  obtain rfl | hji := eq_or_ne j i <;> simp [*, hf _ hj]
#align set.subset_eval_image_pi Set.subset_eval_image_pi

theorem eval_image_pi (hs : i ∈ s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = t i :=
  (eval_image_pi_subset hs).antisymm (subset_eval_image_pi ht i)
#align set.eval_image_pi Set.eval_image_pi

@[simp]
theorem eval_image_univ_pi (ht : (pi univ t).Nonempty) :
    (fun f : ∀ i, α i => f i) '' pi univ t = t i :=
  eval_image_pi (mem_univ i) ht
#align set.eval_image_univ_pi Set.eval_image_univ_pi

theorem pi_subset_pi_iff : pi s t₁ ⊆ pi s t₂ ↔ (∀ i ∈ s, t₁ i ⊆ t₂ i) ∨ pi s t₁ = ∅ := by
  refine'
    ⟨fun h => or_iff_not_imp_right.2 _, fun h => h.elim pi_mono fun h' => h'.symm ▸ empty_subset _⟩
  rw [← Ne.def, ← nonempty_iff_ne_empty]
  -- ⊢ Set.Nonempty (pi s t₁) → ∀ (i : ι), i ∈ s → t₁ i ⊆ t₂ i
  intro hne i hi
  -- ⊢ t₁ i ⊆ t₂ i
  simpa only [eval_image_pi hi hne, eval_image_pi hi (hne.mono h)] using
    image_subset (fun f : ∀ i, α i => f i) h
#align set.pi_subset_pi_iff Set.pi_subset_pi_iff

theorem univ_pi_subset_univ_pi_iff : pi univ t₁ ⊆ pi univ t₂ ↔ (∀ i, t₁ i ⊆ t₂ i) ∨ ∃ i, t₁ i = ∅ :=
  by simp [pi_subset_pi_iff]
     -- 🎉 no goals
#align set.univ_pi_subset_univ_pi_iff Set.univ_pi_subset_univ_pi_iff

theorem eval_preimage [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun i => univ) i s) := by
  ext x
  -- ⊢ x ∈ eval i ⁻¹' s ↔ x ∈ pi univ (update (fun i => univ) i s)
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]
  -- 🎉 no goals
#align set.eval_preimage Set.eval_preimage

theorem eval_preimage' [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun i => univ) i s) := by
  ext
  -- ⊢ x✝ ∈ eval i ⁻¹' s ↔ x✝ ∈ pi {i} (update (fun i => univ) i s)
  simp
  -- 🎉 no goals
#align set.eval_preimage' Set.eval_preimage'

theorem update_preimage_pi [DecidableEq ι] {f : ∀ i, α i} (hi : i ∈ s)
    (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) : update f i ⁻¹' s.pi t = t i := by
  ext x
  -- ⊢ x ∈ update f i ⁻¹' pi s t ↔ x ∈ t i
  refine' ⟨fun h => _, fun hx j hj => _⟩
  -- ⊢ x ∈ t i
  · convert h i hi
    -- ⊢ x = update f i x i
    simp
    -- 🎉 no goals
  · obtain rfl | h := eq_or_ne j i
    -- ⊢ update f j x j ∈ t j
    · simpa
      -- 🎉 no goals
    · rw [update_noteq h]
      -- ⊢ f j ∈ t j
      exact hf j hj h
      -- 🎉 no goals
#align set.update_preimage_pi Set.update_preimage_pi

theorem update_preimage_univ_pi [DecidableEq ι] {f : ∀ i, α i} (hf : ∀ (j) (_ : j ≠ i), f j ∈ t j) :
    update f i ⁻¹' pi univ t = t i :=
  update_preimage_pi (mem_univ i) fun j _ => hf j
#align set.update_preimage_univ_pi Set.update_preimage_univ_pi

theorem subset_pi_eval_image (s : Set ι) (u : Set (∀ i, α i)) : u ⊆ pi s fun i => eval i '' u :=
  fun f hf _ _ => ⟨f, hf, rfl⟩
#align set.subset_pi_eval_image Set.subset_pi_eval_image

theorem univ_pi_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by
  ext
  -- ⊢ (x✝ ∈ pi univ fun i => if i ∈ s then t i else univ) ↔ x✝ ∈ pi s t
  simp_rw [mem_univ_pi]
  -- ⊢ (∀ (i : ι), x✝ i ∈ if i ∈ s then t i else univ) ↔ x✝ ∈ pi s t
  refine' forall_congr' fun i => _
  -- ⊢ (x✝ i ∈ if i ∈ s then t i else univ) ↔ i ∈ s → x✝ i ∈ t i
  split_ifs with h <;> simp [h]
  -- ⊢ x✝ i ∈ t i ↔ i ∈ s → x✝ i ∈ t i
                       -- 🎉 no goals
                       -- 🎉 no goals
#align set.univ_pi_ite Set.univ_pi_ite

end Pi

end Set
