/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Set.Basic

/-!
# Images and preimages of sets

## Main definitions

* `preimage f t : set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `range f : set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

## Notation

* `f ⁻¹' t` for `set.preimage f t`

* `f ~~ s` for `set.image f s`

## Tags

set, sets, image, preimage, pre-image, range

-/


universe u v

open Function

namespace Set

variable {α β γ : Type _} {ι : Sort _}

/-! ### Inverse image -/


/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage {α : Type u} {β : Type v} (f : α → β) (s : Set β) : Set α :=
  { x | f x ∈ s }
#align set.preimage Set.preimage

-- mathport name: «expr ⁻¹' »
infixl:80 " ⁻¹' " => preimage

section Preimage

variable {f : α → β} {g : β → γ}

@[simp]
theorem preimage_empty : f ⁻¹' ∅ = ∅ :=
  rfl
#align set.preimage_empty Set.preimage_empty

@[simp]
theorem mem_preimage {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s :=
  Iff.rfl
#align set.mem_preimage Set.mem_preimage

theorem preimage_congr {f g : α → β} {s : Set β} (h : ∀ x : α, f x = g x) : f ⁻¹' s = g ⁻¹' s := by
  congr with x
  simp [h]
#align set.preimage_congr Set.preimage_congr

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t := fun x hx => h hx
#align set.preimage_mono Set.preimage_mono

@[simp]
theorem preimage_univ : f ⁻¹' univ = univ :=
  rfl
#align set.preimage_univ Set.preimage_univ

theorem subset_preimage_univ {s : Set α} : s ⊆ f ⁻¹' univ :=
  subset_univ _
#align set.subset_preimage_univ Set.subset_preimage_univ

@[simp]
theorem preimage_inter {s t : Set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  rfl
#align set.preimage_inter Set.preimage_inter

@[simp]
theorem preimage_union {s t : Set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
  rfl
#align set.preimage_union Set.preimage_union

@[simp]
theorem preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ :=
  rfl
#align set.preimage_compl Set.preimage_compl

@[simp]
theorem preimage_diff (f : α → β) (s t : Set β) : f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t :=
  rfl
#align set.preimage_diff Set.preimage_diff

@[simp]
theorem preimage_ite (f : α → β) (s t₁ t₂ : Set β) :
    f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
  rfl
#align set.preimage_ite Set.preimage_ite

@[simp]
theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' { a | p a } = { a | p (f a) } :=
  rfl
#align set.preimage_set_of_eq Set.preimage_set_of_eq

@[simp]
theorem preimage_id_eq : preimage (id : α → α) = id :=
  rfl
#align set.preimage_id_eq Set.preimage_id_eq

theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  rfl
#align set.preimage_id Set.preimage_id

@[simp]
theorem preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s :=
  rfl
#align set.preimage_id' Set.preimage_id'

@[simp]
theorem preimage_const_of_mem {b : β} {s : Set β} (h : b ∈ s) : (fun x : α => b) ⁻¹' s = univ :=
  eq_univ_of_forall fun x => h
#align set.preimage_const_of_mem Set.preimage_const_of_mem

@[simp]
theorem preimage_const_of_not_mem {b : β} {s : Set β} (h : b ∉ s) : (fun x : α => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty fun x hx => h hx
#align set.preimage_const_of_not_mem Set.preimage_const_of_not_mem

theorem preimage_const (b : β) (s : Set β) [Decidable (b ∈ s)] :
    (fun x : α => b) ⁻¹' s = if b ∈ s then univ else ∅ := by
  split_ifs with hb hb
  exacts[preimage_const_of_mem hb, preimage_const_of_not_mem hb]
#align set.preimage_const Set.preimage_const

theorem preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' (g ⁻¹' s) :=
  rfl
#align set.preimage_comp Set.preimage_comp

theorem preimage_comp_eq : preimage (g ∘ f) = preimage f ∘ preimage g :=
  rfl
#align set.preimage_comp_eq Set.preimage_comp_eq

@[simp]
theorem preimage_iterate_eq {f : α → α} {n : ℕ} : Set.preimage (f^[n]) = Set.preimage f^[n] := by
  induction' n with n ih; · simp
  rw [iterate_succ, iterate_succ', Set.preimage_comp_eq, ih]
#align set.preimage_iterate_eq Set.preimage_iterate_eq

theorem preimage_preimage {g : β → γ} {f : α → β} {s : Set γ} :
    f ⁻¹' (g ⁻¹' s) = (fun x => g (f x)) ⁻¹' s :=
  preimage_comp.symm
#align set.preimage_preimage Set.preimage_preimage

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : Set (Subtype p)} {t : Set α} :
    s = Subtype.val ⁻¹' t ↔ ∀ (x) (h : p x), (⟨x, h⟩ : Subtype p) ∈ s ↔ x ∈ t :=
  ⟨fun s_eq x h => by
    rw [s_eq]
    simp, fun h => ext fun ⟨x, hx⟩ => by simp [h]⟩
#align set.eq_preimage_subtype_val_iff Set.eq_preimage_subtype_val_iff

theorem nonempty_of_nonempty_preimage {s : Set β} {f : α → β} (hf : (f ⁻¹' s).Nonempty) :
    s.Nonempty :=
  let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩
#align set.nonempty_of_nonempty_preimage Set.nonempty_of_nonempty_preimage

theorem preimage_subtype_coe_eq_compl {α : Type _} {s u v : Set α} (hsuv : s ⊆ u ∪ v)
    (H : s ∩ (u ∩ v) = ∅) : (Subtype.val (p := s)) ⁻¹' u = ((Subtype.val (p := s)) ⁻¹' v)ᶜ := by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_not_mem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
  · intro hx
    exact Or.elim (hsuv x_in_s) id fun hx' => hx.elim hx'
#align set.preimage_subtype_coe_eq_compl Set.preimage_subtype_coe_eq_compl

end Preimage

/-! ### Image of a set under a function -/


section Image

variable {f : α → β} {s t : Set α}

/-- The image of `s : set α` by `f : α → β`, written `f ~~ s`,
  is the set of `y : β` such that `f x = y` for some `x ∈ s`. -/
def image2 (f : α → β) (s : Set α) : Set β :=
  { y | ∃ x, x ∈ s ∧ f x = y }
#align set.image Set.image2

-- mathport name: «expr ~~ »
infixl:80 " ~~ " => image

theorem mem_image_iff_bex {f : α → β} {s : Set α} {y : β} :
    y ∈ f ~~ s ↔ ∃ (x : _)(_ : x ∈ s), f x = y :=
  bex_def.symm
#align set.mem_image_iff_bex Set.mem_image_iff_bex

@[simp]
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f ~~ s ↔ ∃ x, x ∈ s ∧ f x = y :=
  Iff.rfl
#align set.mem_image Set.mem_image

theorem image_eta (f : α → β) : f ~~ s = (fun x => f x) ~~ s :=
  rfl
#align set.image_eta Set.image_eta

theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f ~~ a :=
  ⟨_, h, rfl⟩
#align set.mem_image_of_mem Set.mem_image_of_mem

theorem _root_.Function.Injective.mem_set_image {f : α → β} (hf : Injective f) {s : Set α} {a : α} :
    f a ∈ f ~~ s ↔ a ∈ s :=
  ⟨fun ⟨_, hb, Eq⟩ => hf Eq ▸ hb, mem_image_of_mem f⟩
#align function.injective.mem_set_image Function.Injective.mem_set_image

theorem ball_image_iff {f : α → β} {s : Set α} {p : β → Prop} :
    (∀ y ∈ f ~~ s, p y) ↔ ∀ x ∈ s, p (f x) := by simp
#align set.ball_image_iff Set.ball_image_iff

theorem ball_image_of_ball {f : α → β} {s : Set α} {p : β → Prop} (h : ∀ x ∈ s, p (f x)) :
    ∀ y ∈ f ~~ s, p y :=
  ball_image_iff.2 h
#align set.ball_image_of_ball Set.ball_image_of_ball

theorem bex_image_iff {f : α → β} {s : Set α} {p : β → Prop} :
    (∃ y ∈ f ~~ s, p y) ↔ ∃ x ∈ s, p (f x) := by simp
#align set.bex_image_iff Set.bex_image_iff

theorem mem_image_elim {f : α → β} {s : Set α} {C : β → Prop} (h : ∀ x : α, x ∈ s → C (f x)) :
    ∀ {y : β}, y ∈ f ~~ s → C y
  | _, ⟨a, a_in, rfl⟩ => h a a_in
#align set.mem_image_elim Set.mem_image_elim

theorem mem_image_elim_on {f : α → β} {s : Set α} {C : β → Prop} {y : β} (h_y : y ∈ f ~~ s)
    (h : ∀ x : α, x ∈ s → C (f x)) : C y :=
  mem_image_elim h h_y
#align set.mem_image_elim_on Set.mem_image_elim_on

-- Porting note: used to be `safe`
@[congr]
theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a ∈ s, f a = g a) : f ~~ s = g ~~ s := by
  ext x
  rw [mem_image, mem_image]
  exact {
    mp := by
      rintro ⟨a, ha1, ha2⟩
      exact ⟨a, ⟨ha1, (h a ha1) ▸ ha2⟩⟩,
    mpr := by
      rintro ⟨a, ha1, ha2⟩
      exact ⟨a, ⟨ha1, (h a ha1) ▸ ha2⟩⟩
  }
  -- safe [ext_iff, iff_def]
#align set.image_congr Set.image_congr

/-- A common special case of `image_congr` -/
theorem image_congr' {f g : α → β} {s : Set α} (h : ∀ x : α, f x = g x) : f ~~ s = g ~~ s :=
  image_congr fun x _ => h x
#align set.image_congr' Set.image_congr'

theorem image_comp (f : β → γ) (g : α → β) (a : Set α) : f ∘ g ~~ a = f ~~ (g ~~ a) :=
  Subset.antisymm (ball_image_of_ball fun _ ha => mem_image_of_mem _ <| mem_image_of_mem _ ha)
    (ball_image_of_ball <| ball_image_of_ball fun _ ha => mem_image_of_mem _ ha)
#align set.image_comp Set.image_comp

/-- A variant of `image_comp`, useful for rewriting -/
theorem image_image (g : β → γ) (f : α → β) (s : Set α) : g ~~ (f ~~ s) = (fun x => g (f x)) ~~ s :=
  (image_comp g f s).symm
#align set.image_image Set.image_image

theorem image_comm {β'} {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.image g).image f = (s.image f').image g' := by
  simp_rw [image_image, h_comm]
#align set.image_comm Set.image_comm

theorem _root_.Function.Semiconj.set_image {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun s =>
  image_comm h
#align function.semiconj.set_image Function.Semiconj.set_image

theorem _root_.Function.Commute.set_image {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  Function.Semiconj.set_image h
#align function.commute.set_image Function.Commute.set_image

/-- Image is monotone with respect to `⊆`. See `set.monotone_image` for the statement in
terms of `≤`. -/
theorem image_subset {a b : Set α} (f : α → β) (h : a ⊆ b) : f ~~ a ⊆ f ~~ b := by
  simp only [subset_def, mem_image]
  exact fun x => fun ⟨w, h1, h2⟩ => ⟨w, h h1, h2⟩
#align set.image_subset Set.image_subset

theorem image_union (f : α → β) (s t : Set α) : f ~~ (s ∪ t) = f ~~ s ∪ f ~~ t :=
  ext fun x =>
    ⟨by rintro ⟨a, h | h, rfl⟩ <;> [left, right] <;> exact ⟨_, h, rfl⟩, by
      rintro (⟨a, h, rfl⟩ | ⟨a, h, rfl⟩) <;> refine' ⟨_, _, rfl⟩ <;> [left, right] <;> exact h⟩
#align set.image_union Set.image_union

@[simp]
theorem image_empty (f : α → β) : f ~~ ∅ = ∅ := by
  ext
  simp
#align set.image_empty Set.image_empty

theorem image_inter_subset (f : α → β) (s t : Set α) : f ~~ (s ∩ t) ⊆ f ~~ s ∩ f ~~ t :=
  subset_inter (image_subset _ <| inter_subset_left _ _) (image_subset _ <| inter_subset_right _ _)
#align set.image_inter_subset Set.image_inter_subset

theorem image_inter_on {f : α → β} {s t : Set α} (h : ∀ x ∈ t, ∀ y ∈ s, f x = f y → x = y) :
    f ~~ s ∩ f ~~ t = f ~~ (s ∩ t) :=
  Subset.antisymm
    (fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ =>
      have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
    (image_inter_subset _ _ _)
#align set.image_inter_on Set.image_inter_on

theorem image_inter {f : α → β} {s t : Set α} (H : Injective f) : f ~~ s ∩ f ~~ t = f ~~ (s ∩ t) :=
  image_inter_on fun x _ y _ h => H h
#align set.image_inter Set.image_inter

theorem image_univ_of_surjective {ι : Type _} {f : ι → β} (H : Surjective f) : f ~~ univ = univ :=
  eq_univ_of_forall <| by simpa [image]
#align set.image_univ_of_surjective Set.image_univ_of_surjective

@[simp]
theorem image_singleton {f : α → β} {a : α} : f ~~ {a} = {f a} := by
  ext
  simp [image, eq_comm]
#align set.image_singleton Set.image_singleton

@[simp]
theorem Nonempty.image_const {s : Set α} (hs : s.Nonempty) (a : β) : (fun _ => a) ~~ s = {a} :=
  ext fun x =>
    ⟨fun ⟨y, _, h⟩ => h ▸ mem_singleton _, fun h =>
      (eq_of_mem_singleton h).symm ▸ hs.imp fun y hy => ⟨hy, rfl⟩⟩
#align set.nonempty.image_const Set.Nonempty.image_const

@[simp]
theorem image_eq_empty {α β} {f : α → β} {s : Set α} : f ~~ s = ∅ ↔ s = ∅ := by
  simp only [eq_empty_iff_forall_not_mem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩
#align set.image_eq_empty Set.image_eq_empty

-- Porting note: `compl` is already defined in `Init.Set`
theorem preimage_compl_eq_image_compl [BooleanAlgebra α] (S : Set α) : HasCompl.compl ⁻¹' S = HasCompl.compl ~~ S :=
  Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h =>
      Exists.elim h fun y hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩
#align set.preimage_compl_eq_image_compl Set.preimage_compl_eq_image_compl

theorem mem_compl_image [BooleanAlgebra α] (t : α) (S : Set α) : t ∈ HasCompl.compl ~~ S ↔ tᶜ ∈ S := by
  simp [← preimage_compl_eq_image_compl]
#align set.mem_compl_image Set.mem_compl_image

/-- A variant of `image_id` -/
@[simp]
theorem image_id' (s : Set α) : (fun x => x) ~~ s = s := by
  ext
  simp
#align set.image_id' Set.image_id'

theorem image_id (s : Set α) : id ~~ s = s := by simp
#align set.image_id Set.image_id

theorem compl_compl_image [BooleanAlgebra α] (S : Set α) : HasCompl.compl ~~ (HasCompl.compl ~~ S) = S := by
  rw [← image_comp, compl_comp_compl, image_id]
#align set.compl_compl_image Set.compl_compl_image

theorem image_insert_eq {f : α → β} {a : α} {s : Set α} : f ~~ insert a s = insert (f a) (f ~~ s) :=
  by
  ext
  simp [and_or_left, exists_or, eq_comm, or_comm, and_comm]
#align set.image_insert_eq Set.image_insert_eq

theorem image_pair (f : α → β) (a b : α) : f ~~ {a, b} = {f a, f b} := by
  simp only [image_insert_eq, image_singleton]
#align set.image_pair Set.image_pair

theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set α) :
    f ~~ s ⊆ g ⁻¹' s := fun b ⟨a, h, e⟩ => e ▸ ((I a).symm ▸ h : g (f a) ∈ s)
#align set.image_subset_preimage_of_inverse Set.image_subset_preimage_of_inverse

theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set β) :
    f ⁻¹' s ⊆ g ~~ s := fun b h => ⟨f b, h, I b⟩
#align set.preimage_subset_image_of_inverse Set.preimage_subset_image_of_inverse

theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : image f = preimage g :=
  funext fun s =>
    Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)
#align set.image_eq_preimage_of_inverse Set.image_eq_preimage_of_inverse

theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : b ∈ f ~~ s ↔ g b ∈ s := by
  rw [image_eq_preimage_of_inverse h₁ h₂] <;> rfl
#align set.mem_image_iff_of_inverse Set.mem_image_iff_of_inverse

theorem image_compl_subset {f : α → β} {s : Set α} (H : Injective f) : f ~~ sᶜ ⊆ (f ~~ s)ᶜ :=
  Disjoint.subset_compl_left <| by simp [disjoint_iff_inf_le, image_inter H]
#align set.image_compl_subset Set.image_compl_subset

theorem subset_image_compl {f : α → β} {s : Set α} (H : Surjective f) : (f ~~ s)ᶜ ⊆ f ~~ sᶜ :=
  compl_subset_iff_union.2 <| by
    rw [← image_union]
    simp [image_univ_of_surjective H]
#align set.subset_image_compl Set.subset_image_compl

theorem image_compl_eq {f : α → β} {s : Set α} (H : Bijective f) : f ~~ sᶜ = (f ~~ s)ᶜ :=
  Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)
#align set.image_compl_eq Set.image_compl_eq

theorem subset_image_diff (f : α → β) (s t : Set α) : f ~~ s \ f ~~ t ⊆ f ~~ (s \ t) := by
  rw [diff_subset_iff, ← image_union, union_diff_self]
  exact image_subset f (subset_union_right t s)
#align set.subset_image_diff Set.subset_image_diff

theorem subset_image_symm_diff : (f ~~ s) ∆ (f ~~ t) ⊆ f ~~ s ∆ t :=
  (union_subset_union (subset_image_diff _ _ _) <| subset_image_diff _ _ _).trans
    (superset_of_eq (image_union _ _ _))
#align set.subset_image_symm_diff Set.subset_image_symm_diff

theorem image_diff {f : α → β} (hf : Injective f) (s t : Set α) : f ~~ (s \ t) = f ~~ s \ f ~~ t :=
  Subset.antisymm
    (Subset.trans (image_inter_subset _ _ _) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_diff f s t)
#align set.image_diff Set.image_diff

theorem image_symm_diff (hf : Injective f) (s t : Set α) : f ~~ s ∆ t = (f ~~ s) ∆ (f ~~ t) := by
  simp_rw [Set.symmDiff_def, image_union, image_diff hf]
#align set.image_symm_diff Set.image_symm_diff

theorem Nonempty.image (f : α → β) {s : Set α} : s.Nonempty → (f ~~ s).Nonempty
  | ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩
#align set.nonempty.image Set.Nonempty.image

theorem Nonempty.of_image {f : α → β} {s : Set α} : (f ~~ s).Nonempty → s.Nonempty
  | ⟨y, x, hx, _⟩ => ⟨x, hx⟩
#align set.nonempty.of_image Set.Nonempty.of_image

@[simp]
theorem nonempty_image_iff {f : α → β} {s : Set α} : (f ~~ s).Nonempty ↔ s.Nonempty :=
  ⟨Nonempty.of_image, fun h => h.image f⟩
#align set.nonempty_image_iff Set.nonempty_image_iff

theorem Nonempty.preimage {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : Surjective f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, mem_preimage.2 <| hx.symm ▸ hy⟩
#align set.nonempty.preimage Set.Nonempty.preimage

instance (f : α → β) (s : Set α) [Nonempty s] : Nonempty (f ~~ s) :=
  (Set.Nonempty.image f nonempty_of_nonempty_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp]
theorem image_subset_iff {s : Set α} {t : Set β} {f : α → β} : f ~~ s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  ball_image_iff
#align set.image_subset_iff Set.image_subset_iff

theorem image_preimage_subset (f : α → β) (s : Set β) : f ~~ (f ⁻¹' s) ⊆ s :=
  image_subset_iff.2 Subset.rfl
#align set.image_preimage_subset Set.image_preimage_subset

theorem subset_preimage_image (f : α → β) (s : Set α) : s ⊆ f ⁻¹' (f ~~ s) := fun x =>
  mem_image_of_mem f
#align set.subset_preimage_image Set.subset_preimage_image

theorem preimage_image_eq {f : α → β} (s : Set α) (h : Injective f) : f ⁻¹' (f ~~ s) = s :=
  Subset.antisymm (fun x ⟨y, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)
#align set.preimage_image_eq Set.preimage_image_eq

theorem image_preimage_eq {f : α → β} (s : Set β) (h : Surjective f) : f ~~ (f ⁻¹' s) = s :=
  Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩
#align set.image_preimage_eq Set.image_preimage_eq

theorem preimage_eq_preimage {f : β → α} (hf : Surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  Iff.intro
    fun eq => by rw [← image_preimage_eq s hf, ← image_preimage_eq t hf, eq]
    fun eq => eq ▸ rfl
#align set.preimage_eq_preimage Set.preimage_eq_preimage

theorem image_inter_preimage (f : α → β) (s : Set α) (t : Set β) :
    f ~~ (s ∩ f ⁻¹' t) = f ~~ s ∩ t := by
  apply Subset.antisymm
  ·
    calc
      f ~~ (s ∩ f ⁻¹' t) ⊆ f ~~ s ∩ f ~~ (f ⁻¹' t) := image_inter_subset _ _ _
      _ ⊆ f ~~ s ∩ t := inter_subset_inter_right _ (image_preimage_subset f t)

  · rintro _ ⟨⟨x, h', rfl⟩, h⟩
    exact ⟨x, ⟨h', h⟩, rfl⟩
#align set.image_inter_preimage Set.image_inter_preimage

theorem image_preimage_inter (f : α → β) (s : Set α) (t : Set β) :
    f ~~ (f ⁻¹' t ∩ s) = t ∩ f ~~ s := by simp only [inter_comm, image_inter_preimage]
#align set.image_preimage_inter Set.image_preimage_inter

@[simp]
theorem image_inter_nonempty_iff {f : α → β} {s : Set α} {t : Set β} :
    (f ~~ s ∩ t).Nonempty ↔ (s ∩ f ⁻¹' t).Nonempty := by
  rw [← image_inter_preimage, nonempty_image_iff]
#align set.image_inter_nonempty_iff Set.image_inter_nonempty_iff

theorem image_diff_preimage {f : α → β} {s : Set α} {t : Set β} : f ~~ (s \ f ⁻¹' t) = f ~~ s \ t :=
  by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]
#align set.image_diff_preimage Set.image_diff_preimage

theorem compl_image : image (compl : Set α → Set α) = preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl
#align set.compl_image Set.compl_image

theorem compl_image_set_of {p : Set α → Prop} : compl ~~ { s | p s } = { s | p (sᶜ) } :=
  congr_fun compl_image p
#align set.compl_image_set_of Set.compl_image_set_of

theorem inter_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∩ f ⁻¹' t ⊆ f ⁻¹' (f ~~ s ∩ t) := fun x h => ⟨mem_image_of_mem _ h.left, h.right⟩
#align set.inter_preimage_subset Set.inter_preimage_subset

theorem union_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∪ f ⁻¹' t ⊆ f ⁻¹' (f ~~ s ∪ t) := fun x h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r
#align set.union_preimage_subset Set.union_preimage_subset

theorem subset_image_union (f : α → β) (s : Set α) (t : Set β) : f ~~ (s ∪ f ⁻¹' t) ⊆ f ~~ s ∪ t :=
  image_subset_iff.2 (union_preimage_subset _ _ _)
#align set.subset_image_union Set.subset_image_union

theorem preimage_subset_iff {A : Set α} {B : Set β} {f : α → β} :
    f ⁻¹' B ⊆ A ↔ ∀ a : α, f a ∈ B → a ∈ A :=
  Iff.rfl
#align set.preimage_subset_iff Set.preimage_subset_iff

theorem image_eq_image {f : α → β} (hf : Injective f) : f ~~ s = f ~~ t ↔ s = t :=
  Iff.symm <|
    (Iff.intro fun eq => eq ▸ rfl) fun eq => by
      rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, eq]
#align set.image_eq_image Set.image_eq_image

theorem image_subset_image_iff {f : α → β} (hf : Injective f) : f ~~ s ⊆ f ~~ t ↔ s ⊆ t := by
  refine' Iff.symm <| (Iff.intro (image_subset f)) fun h => _
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf]
  exact preimage_mono h
#align set.image_subset_image_iff Set.image_subset_image_iff

theorem prod_quotient_preimage_eq_image [s : Setoid α] (g : Quotient s → β) {h : α → β}
    (Hh : h = g ∘ Quotient.mk'') (r : Set (β × β)) :
    { x : Quotient s × Quotient s | (g x.1, g x.2) ∈ r } =
      (fun a : α × α => (⟦a.1⟧, ⟦a.2⟧)) ~~ ((fun a : α × α => (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quot.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) ∈ r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩
#align set.prod_quotient_preimage_eq_image Set.prod_quotient_preimage_eq_image

theorem exists_image_iff (f : α → β) (x : Set α) (P : β → Prop) :
    (∃ a : f ~~ x, P a) ↔ ∃ a : x, P (f a) :=
  ⟨fun ⟨a, h⟩ => ⟨⟨_, a.prop.choose_spec.1⟩, a.prop.choose_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨⟨_, _, a.prop, rfl⟩, h⟩⟩
#align set.exists_image_iff Set.exists_image_iff

/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f ~~ s`. -/
def imageFactorization (f : α → β) (s : Set α) : s → f ~~ s := fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩
#align set.image_factorization Set.imageFactorization

theorem image_factorization_eq {f : α → β} {s : Set α} :
    Subtype.val ∘ imageFactorization f s = f ∘ Subtype.val :=
  funext fun p => rfl
#align set.image_factorization_eq Set.image_factorization_eq

theorem surjective_onto_image {f : α → β} {s : Set α} : Surjective (imageFactorization f s) :=
  fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩
#align set.surjective_onto_image Set.surjective_onto_image

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a ≠ a } ⊆ s) : σ ~~ s = s := by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine' ⟨_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
  · refine' iff_of_true ⟨σ.symm i, hs fun h => hi _, σ.apply_symm_apply _⟩ (hs hi)
    convert congr_arg σ h <;> exact (σ.apply_symm_apply _).symm
#align set.image_perm Set.image_perm

end Image

/-! ### Lemmas about range of a function. -/


section Range

variable {f : ι → α} {s t : Set α}

/-- Range of a function.

This function is more flexible than `f ~~ univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : Set α :=
  { x | ∃ y, f y = x }
#align set.range Set.range

@[simp]
theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl
#align set.mem_range Set.mem_range

@[simp]
theorem mem_range_self (i : ι) : f i ∈ range f :=
  ⟨i, rfl⟩
#align set.mem_range_self Set.mem_range_self

theorem forall_range_iff {p : α → Prop} : (∀ a ∈ range f, p a) ↔ ∀ i, p (f i) := by simp
#align set.forall_range_iff Set.forall_range_iff

theorem forall_subtype_range_iff {p : range f → Prop} :
    (∀ a : range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun H i => H _, fun H ⟨y, i, hi⟩ => by
    subst hi
    apply H⟩
#align set.forall_subtype_range_iff Set.forall_subtype_range_iff

theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ ∃ i, p (f i) := by simp
#align set.exists_range_iff Set.exists_range_iff

theorem exists_range_iff' {p : α → Prop} : (∃ a, a ∈ range f ∧ p a) ↔ ∃ i, p (f i) := by
  simpa only [exists_prop] using exists_range_iff
#align set.exists_range_iff' Set.exists_range_iff'

theorem exists_subtype_range_iff {p : range f → Prop} :
    (∃ a : range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun ⟨⟨a, i, hi⟩, ha⟩ => by
    subst a
    exact ⟨i, ha⟩, fun ⟨i, hi⟩ => ⟨_, hi⟩⟩
#align set.exists_subtype_range_iff Set.exists_subtype_range_iff

theorem range_iff_surjective : range f = univ ↔ Surjective f :=
  eq_univ_iff_forall
#align set.range_iff_surjective Set.range_iff_surjective

-- Porting note: Lean4 unfolds `Surjective` here, ruining dot notation
alias range_iff_surjective ↔ _ _root_.Function.Surjective.range_eq

@[simp]
theorem image_univ {f : α → β} : f ~~ univ = range f := by
  ext
  simp [image, range]
#align set.image_univ Set.image_univ

theorem image_subset_range (f : α → β) (s) : f ~~ s ⊆ range f := by
  rw [← image_univ] <;> exact image_subset _ (subset_univ _)
#align set.image_subset_range Set.image_subset_range

theorem mem_range_of_mem_image (f : α → β) (s) {x : β} (h : x ∈ f ~~ s) : x ∈ range f :=
  image_subset_range f s h
#align set.mem_range_of_mem_image Set.mem_range_of_mem_image

theorem _root_.Nat.mem_range_succ (i : ℕ) : i ∈ range Nat.succ ↔ 0 < i :=
  ⟨by
    rintro ⟨n, rfl⟩
    exact Nat.succ_pos n, fun h => ⟨_, Nat.succ_pred_eq_of_pos h⟩⟩
#align nat.mem_range_succ Nat.mem_range_succ

theorem Nonempty.preimage' {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : s ⊆ Set.range f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, Set.mem_preimage.2 <| hx.symm ▸ hy⟩
#align set.nonempty.preimage' Set.Nonempty.preimage'

theorem range_comp (g : α → β) (f : ι → α) : range (g ∘ f) = g ~~ range f :=
  Subset.antisymm (forall_range_iff.mpr fun i => mem_image_of_mem g (mem_range_self _))
    (ball_image_iff.mpr <| forall_range_iff.mpr mem_range_self)
#align set.range_comp Set.range_comp

theorem range_subset_iff : range f ⊆ s ↔ ∀ y, f y ∈ s :=
  forall_range_iff
#align set.range_subset_iff Set.range_subset_iff

theorem range_eq_iff (f : α → β) (s : Set β) :
    range f = s ↔ (∀ a, f a ∈ s) ∧ ∀ b ∈ s, ∃ a, f a = b := by
  rw [← range_subset_iff]
  exact le_antisymm_iff
#align set.range_eq_iff Set.range_eq_iff

theorem range_comp_subset_range (f : α → β) (g : β → γ) : range (g ∘ f) ⊆ range g := by
  rw [range_comp] <;> apply image_subset_range
#align set.range_comp_subset_range Set.range_comp_subset_range

theorem range_nonempty_iff_nonempty : (range f).Nonempty ↔ Nonempty ι :=
  ⟨fun ⟨y, x, hxy⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩
#align set.range_nonempty_iff_nonempty Set.range_nonempty_iff_nonempty

theorem range_nonempty [h : Nonempty ι] (f : ι → α) : (range f).Nonempty :=
  range_nonempty_iff_nonempty.2 h
#align set.range_nonempty Set.range_nonempty

@[simp]
theorem range_eq_empty_iff {f : ι → α} : range f = ∅ ↔ IsEmpty ι := by
  rw [← not_nonempty_iff, ← range_nonempty_iff_nonempty, not_nonempty_iff_eq_empty]
#align set.range_eq_empty_iff Set.range_eq_empty_iff

theorem range_eq_empty [IsEmpty ι] (f : ι → α) : range f = ∅ :=
  range_eq_empty_iff.2 ‹_›
#align set.range_eq_empty Set.range_eq_empty

instance [Nonempty ι] (f : ι → α) : Nonempty (range f) :=
  (range_nonempty f).to_subtype

@[simp]
theorem image_union_image_compl_eq_range (f : α → β) : f ~~ s ∪ f ~~ sᶜ = range f := by
  rw [← image_union, ← image_univ, ← union_compl_self]
#align set.image_union_image_compl_eq_range Set.image_union_image_compl_eq_range

theorem insert_image_compl_eq_range (f : α → β) (x : α) : insert (f x) (f ~~ {x}ᶜ) = range f := by
  ext y; rw [mem_range, mem_insert_iff, mem_image]
  constructor
  · rintro (h | ⟨x', hx', h⟩)
    · exact ⟨x, h.symm⟩
    · exact ⟨x', h⟩
  · rintro ⟨x', h⟩
    by_cases hx : x' = x
    · left
      rw [← h, hx]
    · right
      refine' ⟨_, _, h⟩
      rw [mem_compl_singleton_iff]
      exact hx
#align set.insert_image_compl_eq_range Set.insert_image_compl_eq_range

theorem image_preimage_eq_inter_range {f : α → β} {t : Set β} : f ~~ (f ⁻¹' t) = t ∩ range f :=
  ext fun x =>
    ⟨fun ⟨x, hx, HEq⟩ => HEq ▸ ⟨hx, mem_range_self _⟩, fun ⟨hx, ⟨y, h_eq⟩⟩ =>
      h_eq ▸ mem_image_of_mem f <| show y ∈ f ⁻¹' t by rw [preimage, mem_set_of, h_eq]; exact hx⟩
#align set.image_preimage_eq_inter_range Set.image_preimage_eq_inter_range

theorem image_preimage_eq_of_subset {f : α → β} {s : Set β} (hs : s ⊆ range f) :
    f ~~ (f ⁻¹' s) = s := by rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]
#align set.image_preimage_eq_of_subset Set.image_preimage_eq_of_subset

theorem image_preimage_eq_iff {f : α → β} {s : Set β} : f ~~ (f ⁻¹' s) = s ↔ s ⊆ range f :=
  ⟨by
    intro h
    rw [← h]
    apply image_subset_range, image_preimage_eq_of_subset⟩
#align set.image_preimage_eq_iff Set.image_preimage_eq_iff

theorem subset_range_iff_exists_image_eq {f : α → β} {s : Set β} : s ⊆ range f ↔ ∃ t, f ~~ t = s :=
  ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨t, ht⟩ => ht ▸ image_subset_range _ _⟩
#align set.subset_range_iff_exists_image_eq Set.subset_range_iff_exists_image_eq

@[simp]
theorem exists_subset_range_and_iff {f : α → β} {p : Set β → Prop} :
    (∃ s, s ⊆ range f ∧ p s) ↔ ∃ s, p (f ~~ s) :=
  ⟨fun ⟨s, hsf, hps⟩ => ⟨f ⁻¹' s, (image_preimage_eq_of_subset hsf).symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨f ~~ s, image_subset_range _ _, hs⟩⟩
#align set.exists_subset_range_and_iff Set.exists_subset_range_and_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (s «expr ⊆ » range[set.range] f) -/
theorem exists_subset_range_iff {f : α → β} {p : Set β → Prop} :
    (∃ (s : _) (_ : s ⊆ range f), p s) ↔ ∃ s, p (f ~~ s) := by simp
#align set.exists_subset_range_iff Set.exists_subset_range_iff

theorem range_image (f : α → β) : range (image f) = 𝒫 range f :=
  ext fun s => subset_range_iff_exists_image_eq.symm
#align set.range_image Set.range_image

theorem preimage_subset_preimage_iff {s t : Set α} {f : β → α} (hs : s ⊆ range f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
  intro h x; apply h
#align set.preimage_subset_preimage_iff Set.preimage_subset_preimage_iff

theorem preimage_eq_preimage' {s t : Set α} {f : β → α} (hs : s ⊆ range f) (ht : t ⊆ range f) :
    f ⁻¹' s = f ⁻¹' t ↔ s = t := by
  constructor
  · intro h
    apply Subset.antisymm
    rw [← preimage_subset_preimage_iff hs, h]
    rw [← preimage_subset_preimage_iff ht, h]
  rintro rfl; rfl
#align set.preimage_eq_preimage' Set.preimage_eq_preimage'

@[simp]
theorem preimage_inter_range {f : α → β} {s : Set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
  Set.ext fun x => and_iff_left ⟨x, rfl⟩
#align set.preimage_inter_range Set.preimage_inter_range

@[simp]
theorem preimage_range_inter {f : α → β} {s : Set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s := by
  rw [inter_comm, preimage_inter_range]
#align set.preimage_range_inter Set.preimage_range_inter

theorem preimage_image_preimage {f : α → β} {s : Set β} : f ⁻¹' (f ~~ (f ⁻¹' s)) = f ⁻¹' s := by
  rw [image_preimage_eq_inter_range, preimage_inter_range]
#align set.preimage_image_preimage Set.preimage_image_preimage

@[simp]
theorem range_id : range (@id α) = univ :=
  range_iff_surjective.2 surjective_id
#align set.range_id Set.range_id

@[simp]
theorem range_id' : (range fun x : α => x) = univ :=
  range_id
#align set.range_id' Set.range_id'

@[simp]
theorem _root_.Prod.range_fst [Nonempty β] : range (Prod.fst : α × β → α) = univ :=
  Function.Surjective.range_eq Prod.fst_surjective
  -- Porting note: should be `Prod.fst_surjective.range_eq` if dot notation works
#align prod.range_fst Prod.range_fst

@[simp]
theorem _root_.Prod.range_snd [Nonempty α] : range (Prod.snd : α × β → β) = univ :=
  Function.Surjective.range_eq Prod.snd_surjective
  -- Porting note: should be `Prod.snd_surjective.range_eq` if dot notation works
#align prod.range_snd Prod.range_snd

@[simp]
theorem range_eval {ι : Type _} {α : ι → Sort _} [∀ i, Nonempty (α i)] (i : ι) :
    range (eval i : (∀ i, α i) → α i) = univ :=
  Function.Surjective.range_eq (surjective_eval i)
  -- Porting note: should be `(surjective_eval i).range_eq` if dot notation works
#align set.range_eval Set.range_eval

theorem is_compl_range_inl_range_inr : IsCompl (range <| @Sum.inl α β) (range Sum.inr) :=
  IsCompl.of_le
    (by
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, _⟩⟩
      cc)
    (by rintro (x | y) - <;> [left, right] <;> exact mem_range_self _)
#align set.is_compl_range_inl_range_inr Set.is_compl_range_inl_range_inr

@[simp]
theorem range_inl_union_range_inr : range (Sum.inl : α → Sum α β) ∪ range Sum.inr = univ :=
  is_compl_range_inl_range_inr.sup_eq_top
#align set.range_inl_union_range_inr Set.range_inl_union_range_inr

@[simp]
theorem range_inl_inter_range_inr : range (Sum.inl : α → Sum α β) ∩ range Sum.inr = ∅ :=
  is_compl_range_inl_range_inr.inf_eq_bot
#align set.range_inl_inter_range_inr Set.range_inl_inter_range_inr

@[simp]
theorem range_inr_union_range_inl : range (Sum.inr : β → Sum α β) ∪ range Sum.inl = univ :=
  is_compl_range_inl_range_inr.symm.sup_eq_top
#align set.range_inr_union_range_inl Set.range_inr_union_range_inl

@[simp]
theorem range_inr_inter_range_inl : range (Sum.inr : β → Sum α β) ∩ range Sum.inl = ∅ :=
  is_compl_range_inl_range_inr.symm.inf_eq_bot
#align set.range_inr_inter_range_inl Set.range_inr_inter_range_inl

@[simp]
theorem preimage_inl_image_inr (s : Set β) : Sum.inl ⁻¹' (@Sum.inr α β ~~ s) = ∅ := by
  ext
  simp
#align set.preimage_inl_image_inr Set.preimage_inl_image_inr

@[simp]
theorem preimage_inr_image_inl (s : Set α) : Sum.inr ⁻¹' (@Sum.inl α β ~~ s) = ∅ := by
  ext
  simp
#align set.preimage_inr_image_inl Set.preimage_inr_image_inl

@[simp]
theorem preimage_inl_range_inr : Sum.inl ⁻¹' range (Sum.inr : β → Sum α β) = ∅ := by
  rw [← image_univ, preimage_inl_image_inr]
#align set.preimage_inl_range_inr Set.preimage_inl_range_inr

@[simp]
theorem preimage_inr_range_inl : Sum.inr ⁻¹' range (Sum.inl : α → Sum α β) = ∅ := by
  rw [← image_univ, preimage_inr_image_inl]
#align set.preimage_inr_range_inl Set.preimage_inr_range_inl

@[simp]
theorem compl_range_inl : range (Sum.inl : α → Sum α β)ᶜ = range (Sum.inr : β → Sum α β) :=
  IsCompl.compl_eq is_compl_range_inl_range_inr
#align set.compl_range_inl Set.compl_range_inl

@[simp]
theorem compl_range_inr : range (Sum.inr : β → Sum α β)ᶜ = range (Sum.inl : α → Sum α β) :=
  IsCompl.compl_eq is_compl_range_inl_range_inr.symm
#align set.compl_range_inr Set.compl_range_inr

theorem image_preimage_inl_union_image_preimage_inr (s : Set (Sum α β)) :
    Sum.inl ~~ (Sum.inl ⁻¹' s) ∪ Sum.inr ~~ (Sum.inr ⁻¹' s) = s := by
  rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, ← inter_distrib_left,
    range_inl_union_range_inr, inter_univ]
#align
  set.image_preimage_inl_union_image_preimage_inr Set.image_preimage_inl_union_image_preimage_inr

@[simp]
theorem range_quot_mk (r : α → α → Prop) : range (Quot.mk r) = univ :=
  (surjective_quot_mk r).range_eq
#align set.range_quot_mk Set.range_quot_mk

@[simp]
theorem range_quot_lift {r : ι → ι → Prop} (hf : ∀ x y, r x y → f x = f y) :
    range (Quot.lift f hf) = range f :=
  ext fun y => (surjective_quot_mk _).exists
#align set.range_quot_lift Set.range_quot_lift

@[simp]
theorem range_quotient_mk [Setoid α] : (range fun x : α => ⟦x⟧) = univ :=
  range_quot_mk _
#align set.range_quotient_mk Set.range_quotient_mk

@[simp]
theorem range_quotient_lift [s : Setoid ι] (hf) :
    range (Quotient.lift f hf : Quotient s → α) = range f :=
  range_quot_lift _
#align set.range_quotient_lift Set.range_quotient_lift

@[simp]
theorem range_quotient_mk' {s : Setoid α} : range (Quotient.mk' : α → Quotient s) = univ :=
  range_quot_mk _
#align set.range_quotient_mk' Set.range_quotient_mk'

@[simp]
theorem range_quotient_lift_on' {s : Setoid ι} (hf) :
    (range fun x : Quotient s => Quotient.liftOn' x f hf) = range f :=
  range_quot_lift _
#align set.range_quotient_lift_on' Set.range_quotient_lift_on'

instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Set α) (Set β) ((· ~~ ·) c) fun s =>
      ∀ x ∈ s,
        p
          x where prf s hs :=
    subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)
#align set.can_lift Set.canLift

theorem range_const_subset {c : α} : (range fun x : ι => c) ⊆ {c} :=
  range_subset_iff.2 fun x => rfl
#align set.range_const_subset Set.range_const_subset

@[simp]
theorem range_const : ∀ [Nonempty ι] {c : α}, (range fun x : ι => c) = {c}
  | ⟨x⟩, c =>
    (Subset.antisymm range_const_subset) fun y hy =>
      (mem_singleton_iff.1 hy).symm ▸ mem_range_self x
#align set.range_const Set.range_const

theorem range_subtype_map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ x, p x → q (f x)) :
    range (Subtype.map f h) = coe ⁻¹' (f ~~ { x | p x }) := by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map, Subtype.coe_mk,
    mem_set_of, exists_prop]
#align set.range_subtype_map Set.range_subtype_map

theorem image_swap_eq_preimage_swap : image (@Prod.swap α β) = preimage Prod.swap :=
  image_eq_preimage_of_inverse Prod.swap_leftInverse Prod.swap_rightInverse
#align set.image_swap_eq_preimage_swap Set.image_swap_eq_preimage_swap

theorem preimage_singleton_nonempty {f : α → β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y ∈ range f :=
  Iff.rfl
#align set.preimage_singleton_nonempty Set.preimage_singleton_nonempty

theorem preimage_singleton_eq_empty {f : α → β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
  not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.Not
#align set.preimage_singleton_eq_empty Set.preimage_singleton_eq_empty

theorem range_subset_singleton {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = const ι x := by
  simp [range_subset_iff, funext_iff, mem_singleton]
#align set.range_subset_singleton Set.range_subset_singleton

theorem image_compl_preimage {f : α → β} {s : Set β} : f ~~ (f ⁻¹' s)ᶜ = range f \ s := by
  rw [compl_eq_univ_diff, image_diff_preimage, image_univ]
#align set.image_compl_preimage Set.image_compl_preimage

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def rangeFactorization (f : ι → β) : ι → range f := fun i => ⟨f i, mem_range_self i⟩
#align set.range_factorization Set.rangeFactorization

theorem range_factorization_eq {f : ι → β} : Subtype.val ∘ rangeFactorization f = f :=
  funext fun i => rfl
#align set.range_factorization_eq Set.range_factorization_eq

@[simp]
theorem range_factorization_coe (f : ι → β) (a : ι) : (rangeFactorization f a : β) = f a :=
  rfl
#align set.range_factorization_coe Set.range_factorization_coe

@[simp]
theorem coe_comp_range_factorization (f : ι → β) : coe ∘ rangeFactorization f = f :=
  rfl
#align set.coe_comp_range_factorization Set.coe_comp_range_factorization

theorem surjective_onto_range : Surjective (rangeFactorization f) := fun ⟨_, ⟨i, rfl⟩⟩ => ⟨i, rfl⟩
#align set.surjective_onto_range Set.surjective_onto_range

theorem image_eq_range (f : α → β) (s : Set α) : f ~~ s = range fun x : s => f x := by
  ext
  constructor
  rintro ⟨x, h1, h2⟩
  exact ⟨⟨x, h1⟩, h2⟩
  rintro ⟨⟨x, h1⟩, h2⟩
  exact ⟨x, h1, h2⟩
#align set.image_eq_range Set.image_eq_range

theorem Sum.range_eq (f : Sum α β → γ) : range f = range (f ∘ Sum.inl) ∪ range (f ∘ Sum.inr) :=
  ext fun x => Sum.exists
#align sum.range_eq Sum.range_eq

@[simp]
theorem Sum.elim_range (f : α → γ) (g : β → γ) : range (Sum.elim f g) = range f ∪ range g :=
  Sum.range_eq _
#align set.sum.elim_range Set.Sum.elim_range

theorem range_ite_subset' {p : Prop} [Decidable p] {f g : α → β} :
    range (if p then f else g) ⊆ range f ∪ range g := by
  by_cases h : p;
  · rw [if_pos h]
    exact subset_union_left _ _
  · rw [if_neg h]
    exact subset_union_right _ _
#align set.range_ite_subset' Set.range_ite_subset'

theorem range_ite_subset {p : α → Prop} [DecidablePred p] {f g : α → β} :
    (range fun x => if p x then f x else g x) ⊆ range f ∪ range g := by
  rw [range_subset_iff]; intro x; by_cases h : p x
  simp [if_pos h, mem_union, mem_range_self]
  simp [if_neg h, mem_union, mem_range_self]
#align set.range_ite_subset Set.range_ite_subset

@[simp]
theorem preimage_range (f : α → β) : f ⁻¹' range f = univ :=
  eq_univ_of_forall mem_range_self
#align set.preimage_range Set.preimage_range

/-- The range of a function from a `unique` type contains just the
function applied to its single value. -/
theorem range_unique [h : Unique ι] : range f = {f default} := by
  ext x
  rw [mem_range]
  constructor
  · rintro ⟨i, hi⟩
    rw [h.uniq i] at hi
    exact hi ▸ mem_singleton _
  · exact fun h => ⟨default, h.symm⟩
#align set.range_unique Set.range_unique

theorem range_diff_image_subset (f : α → β) (s : Set α) : range f \ f ~~ s ⊆ f ~~ sᶜ :=
  fun y ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩
#align set.range_diff_image_subset Set.range_diff_image_subset

theorem range_diff_image {f : α → β} (H : Injective f) (s : Set α) : range f \ f ~~ s = f ~~ sᶜ :=
  (Subset.antisymm (range_diff_image_subset f s)) fun y ⟨x, hx, hy⟩ =>
    hy ▸ ⟨mem_range_self _, fun ⟨x', hx', Eq⟩ => hx <| H Eq ▸ hx'⟩
#align set.range_diff_image Set.range_diff_image

@[simp]
theorem range_inclusion (h : s ⊆ t) : range (inclusion h) = { x : t | (x : α) ∈ s } := by
  ext ⟨x, hx⟩
  simp [inclusion]
#align set.range_inclusion Set.range_inclusion

/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
noncomputable def rangeSplitting (f : α → β) : range f → α := fun x => x.2.some
#align set.range_splitting Set.rangeSplitting

-- This can not be a `@[simp]` lemma because the head of the left hand side is a variable.
theorem apply_range_splitting (f : α → β) (x : range f) : f (rangeSplitting f x) = x :=
  x.2.some_spec
#align set.apply_range_splitting Set.apply_range_splitting

@[simp]
theorem comp_range_splitting (f : α → β) : f ∘ rangeSplitting f = coe := by
  ext
  simp only [Function.comp_apply]
  apply apply_range_splitting
#align set.comp_range_splitting Set.comp_range_splitting

-- When `f` is injective, see also `equiv.of_injective`.
theorem left_inverse_range_splitting (f : α → β) :
    LeftInverse (rangeFactorization f) (rangeSplitting f) := fun x => by
  ext
  simp only [range_factorization_coe]
  apply apply_range_splitting
#align set.left_inverse_range_splitting Set.left_inverse_range_splitting

theorem range_splitting_injective (f : α → β) : Injective (rangeSplitting f) :=
  (left_inverse_range_splitting f).Injective
#align set.range_splitting_injective Set.range_splitting_injective

theorem right_inverse_range_splitting {f : α → β} (h : Injective f) :
    RightInverse (rangeFactorization f) (rangeSplitting f) :=
  (left_inverse_range_splitting f).right_inverse_of_injective fun x y hxy =>
    h <| Subtype.ext_iff.1 hxy
#align set.right_inverse_range_splitting Set.right_inverse_range_splitting

theorem preimage_range_splitting {f : α → β} (hf : Injective f) :
    preimage (rangeSplitting f) = image (rangeFactorization f) :=
  (image_eq_preimage_of_inverse (right_inverse_range_splitting hf)
      (left_inverse_range_splitting f)).symm
#align set.preimage_range_splitting Set.preimage_range_splitting

theorem is_compl_range_some_none (α : Type _) : IsCompl (range (some : α → Option α)) {none} :=
  IsCompl.of_le (fun x ⟨⟨a, ha⟩, (hn : x = none)⟩ => Option.some_ne_none _ (ha.trans hn))
    fun x hx => Option.casesOn x (Or.inr rfl) fun x => Or.inl <| mem_range_self _
#align set.is_compl_range_some_none Set.is_compl_range_some_none

@[simp]
theorem compl_range_some (α : Type _) : range (some : α → Option α)ᶜ = {none} :=
  (is_compl_range_some_none α).compl_eq
#align set.compl_range_some Set.compl_range_some

@[simp]
theorem range_some_inter_none (α : Type _) : range (some : α → Option α) ∩ {none} = ∅ :=
  (is_compl_range_some_none α).inf_eq_bot
#align set.range_some_inter_none Set.range_some_inter_none

@[simp]
theorem range_some_union_none (α : Type _) : range (some : α → Option α) ∪ {none} = univ :=
  (is_compl_range_some_none α).sup_eq_top
#align set.range_some_union_none Set.range_some_union_none

@[simp]
theorem insert_none_range_some (α : Type _) : insert none (range (some : α → Option α)) = univ :=
  (is_compl_range_some_none α).symm.sup_eq_top
#align set.insert_none_range_some Set.insert_none_range_some

end Range

section Subsingleton

variable {s : Set α}

/-- The image of a subsingleton is a subsingleton. -/
theorem Subsingleton.image (hs : s.Subsingleton) (f : α → β) : (f ~~ s).Subsingleton :=
  fun _ ⟨x, hx, Hx⟩ _ ⟨y, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)
#align set.subsingleton.image Set.Subsingleton.image

/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
theorem Subsingleton.preimage {s : Set β} (hs : s.Subsingleton) {f : α → β}
    (hf : Function.Injective f) : (f ⁻¹' s).Subsingleton := fun a ha b hb => hf <| hs ha hb
#align set.subsingleton.preimage Set.Subsingleton.preimage

/-- If the image of a set under an injective map is a subsingleton, the set is a subsingleton. -/
theorem subsingleton_of_image {α β : Type _} {f : α → β} (hf : Function.Injective f) (s : Set α)
    (hs : (f ~~ s).Subsingleton) : s.Subsingleton :=
  (hs.Preimage hf).anti <| subset_preimage_image _ _
#align set.subsingleton_of_image Set.subsingleton_of_image

/-- If the preimage of a set under an surjective map is a subsingleton,
the set is a subsingleton. -/
theorem subsingleton_of_preimage {α β : Type _} {f : α → β} (hf : Function.Surjective f) (s : Set β)
    (hs : (f ⁻¹' s).Subsingleton) : s.Subsingleton := fun fx hx fy hy => by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)
#align set.subsingleton_of_preimage Set.subsingleton_of_preimage

theorem subsingleton_range {α : Sort _} [Subsingleton α] (f : α → β) : (range f).Subsingleton :=
  forall_range_iff.2 fun x => forall_range_iff.2 fun y => congr_arg f (Subsingleton.elim x y)
#align set.subsingleton_range Set.subsingleton_range

/-- The preimage of a nontrivial set under a surjective map is nontrivial. -/
theorem Nontrivial.preimage {s : Set β} (hs : s.Nontrivial) {f : α → β}
    (hf : Function.Surjective f) : (f ⁻¹' s).Nontrivial := by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩
#align set.nontrivial.preimage Set.Nontrivial.preimage

/-- The image of a nontrivial set under an injective map is nontrivial. -/
theorem Nontrivial.image (hs : s.Nontrivial) {f : α → β} (hf : Function.Injective f) :
    (f ~~ s).Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.Ne hxy⟩
#align set.nontrivial.image Set.Nontrivial.image

/-- If the image of a set is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_image (f : α → β) (s : Set α) (hs : (f ~~ s).Nontrivial) : s.Nontrivial :=
  let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩
#align set.nontrivial_of_image Set.nontrivial_of_image

/-- If the preimage of a set under an injective map is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_preimage {f : α → β} (hf : Function.Injective f) (s : Set β)
    (hs : (f ⁻¹' s).Nontrivial) : s.Nontrivial :=
  (hs.image hf).mono <| image_preimage_subset _ _
#align set.nontrivial_of_preimage Set.nontrivial_of_preimage

end Subsingleton

end Set

namespace Function

variable {ι : Sort _} {α : Type _} {β : Type _} {f : α → β}

open Set

theorem Surjective.preimage_injective (hf : Surjective f) : Injective (preimage f) := fun s t =>
  (preimage_eq_preimage hf).1
#align function.surjective.preimage_injective Function.Surjective.preimage_injective

theorem Injective.preimage_image (hf : Injective f) (s : Set α) : f ⁻¹' (f ~~ s) = s :=
  preimage_image_eq s hf
#align function.injective.preimage_image Function.Injective.preimage_image

theorem Injective.preimage_surjective (hf : Injective f) : Surjective (preimage f) := by
  intro s
  use f ~~ s
  rw [hf.preimage_image]
#align function.injective.preimage_surjective Function.Injective.preimage_surjective

theorem Injective.subsingleton_image_iff (hf : Injective f) {s : Set α} :
    (f ~~ s).Subsingleton ↔ s.Subsingleton :=
  ⟨subsingleton_of_image hf s, fun h => h.image f⟩
#align function.injective.subsingleton_image_iff Function.Injective.subsingleton_image_iff

theorem Surjective.image_preimage (hf : Surjective f) (s : Set β) : f ~~ (f ⁻¹' s) = s :=
  image_preimage_eq s hf
#align function.surjective.image_preimage Function.Surjective.image_preimage

theorem Surjective.image_surjective (hf : Surjective f) : Surjective (image f) := by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]
#align function.surjective.image_surjective Function.Surjective.image_surjective

theorem Surjective.nonempty_preimage (hf : Surjective f) {s : Set β} :
    (f ⁻¹' s).Nonempty ↔ s.Nonempty := by rw [← nonempty_image_iff, hf.image_preimage]
#align function.surjective.nonempty_preimage Function.Surjective.nonempty_preimage

theorem Injective.image_injective (hf : Injective f) : Injective (image f) := by
  intro s t h
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, h]
#align function.injective.image_injective Function.Injective.image_injective

theorem Surjective.preimage_subset_preimage_iff {s t : Set β} (hf : Surjective f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  apply preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ
#align
  function.surjective.preimage_subset_preimage_iff Function.Surjective.preimage_subset_preimage_iff

theorem Surjective.range_comp {ι' : Sort _} {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    range (g ∘ f) = range g :=
  ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm
#align function.surjective.range_comp Function.Surjective.range_comp

theorem Injective.mem_range_iff_exists_unique (hf : Injective f) {b : β} :
    b ∈ range f ↔ ∃! a, f a = b :=
  ⟨fun ⟨a, h⟩ => ⟨a, h, fun a' ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩
#align function.injective.mem_range_iff_exists_unique Function.Injective.mem_range_iff_exists_unique

theorem Injective.exists_unique_of_mem_range (hf : Injective f) {b : β} (hb : b ∈ range f) :
    ∃! a, f a = b :=
  hf.mem_range_iff_exists_unique.mp hb
#align function.injective.exists_unique_of_mem_range Function.Injective.exists_unique_of_mem_range

theorem Injective.compl_image_eq (hf : Injective f) (s : Set α) : (f ~~ s)ᶜ = f ~~ sᶜ ∪ range fᶜ :=
  by
  ext y
  rcases em (y ∈ range f) with (⟨x, rfl⟩ | hx)
  · simp [hf.eq_iff]
  · rw [mem_range, not_exists] at hx
    simp [hx]
#align function.injective.compl_image_eq Function.Injective.compl_image_eq

theorem LeftInverse.image_image {g : β → α} (h : LeftInverse g f) (s : Set α) : g ~~ (f ~~ s) = s :=
  by rw [← image_comp, h.comp_eq_id, image_id]
#align function.left_inverse.image_image Function.LeftInverse.image_image

theorem LeftInverse.preimage_preimage {g : β → α} (h : LeftInverse g f) (s : Set α) :
    f ⁻¹' (g ⁻¹' s) = s := by rw [← preimage_comp, h.comp_eq_id, preimage_id]
#align function.left_inverse.preimage_preimage Function.LeftInverse.preimage_preimage

end Function

/-! ### Image and preimage on subtypes -/


namespace Subtype

open Set

variable {α : Type _}

theorem coe_image {p : α → Prop} {s : Set (Subtype p)} :
    coe ~~ s = { x | ∃ h : p x, (⟨x, h⟩ : Subtype p) ∈ s } :=
  Set.ext fun a =>
    ⟨fun ⟨⟨a', ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩
#align subtype.coe_image Subtype.coe_image

@[simp]
theorem coe_image_of_subset {s t : Set α} (h : t ⊆ s) : coe ~~ { x : ↥s | ↑x ∈ t } = t := by
  ext x
  rw [Set.mem_image]
  exact ⟨fun ⟨x', hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩
#align subtype.coe_image_of_subset Subtype.coe_image_of_subset

theorem range_coe {s : Set α} : range (coe : s → α) = s := by
  rw [← Set.image_univ]
  simp [-Set.image_univ, coe_image]
#align subtype.range_coe Subtype.range_coe

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
theorem range_val {s : Set α} : range (Subtype.val : s → α) = s :=
  range_coe
#align subtype.range_val Subtype.range_val

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : set α` the function `coe : s → α`, then the inferred implicit arguments of `coe` are
  `coe α (λ x, x ∈ s)`. -/
@[simp]
theorem range_coe_subtype {p : α → Prop} : range (coe : Subtype p → α) = { x | p x } :=
  range_coe
#align subtype.range_coe_subtype Subtype.range_coe_subtype

@[simp]
theorem coe_preimage_self (s : Set α) : (coe : s → α) ⁻¹' s = univ := by
  rw [← preimage_range (coe : s → α), range_coe]
#align subtype.coe_preimage_self Subtype.coe_preimage_self

theorem range_val_subtype {p : α → Prop} : range (Subtype.val : Subtype p → α) = { x | p x } :=
  range_coe
#align subtype.range_val_subtype Subtype.range_val_subtype

theorem coe_image_subset (s : Set α) (t : Set s) : coe ~~ t ⊆ s := fun x ⟨y, yt, yvaleq⟩ => by
  rw [← yvaleq] <;> exact y.property
#align subtype.coe_image_subset Subtype.coe_image_subset

theorem coe_image_univ (s : Set α) : (coe : s → α) ~~ Set.univ = s :=
  image_univ.trans range_coe
#align subtype.coe_image_univ Subtype.coe_image_univ

@[simp]
theorem image_preimage_coe (s t : Set α) : (coe : s → α) ~~ (coe ⁻¹' t) = t ∩ s :=
  image_preimage_eq_inter_range.trans <| congr_arg _ range_coe
#align subtype.image_preimage_coe Subtype.image_preimage_coe

theorem image_preimage_val (s t : Set α) : (Subtype.val : s → α) ~~ (Subtype.val ⁻¹' t) = t ∩ s :=
  image_preimage_coe s t
#align subtype.image_preimage_val Subtype.image_preimage_val

theorem preimage_coe_eq_preimage_coe_iff {s t u : Set α} :
    (coe : s → α) ⁻¹' t = coe ⁻¹' u ↔ t ∩ s = u ∩ s := by
  rw [← image_preimage_coe, ← image_preimage_coe, coe_injective.image_injective.eq_iff]
#align subtype.preimage_coe_eq_preimage_coe_iff Subtype.preimage_coe_eq_preimage_coe_iff

@[simp]
theorem preimage_coe_inter_self (s t : Set α) : (coe : s → α) ⁻¹' (t ∩ s) = coe ⁻¹' t := by
  rw [preimage_coe_eq_preimage_coe_iff, inter_assoc, inter_self]
#align subtype.preimage_coe_inter_self Subtype.preimage_coe_inter_self

theorem preimage_val_eq_preimage_val_iff (s t u : Set α) :
    (Subtype.val : s → α) ⁻¹' t = Subtype.val ⁻¹' u ↔ t ∩ s = u ∩ s :=
  preimage_coe_eq_preimage_coe_iff
#align subtype.preimage_val_eq_preimage_val_iff Subtype.preimage_val_eq_preimage_val_iff

theorem exists_set_subtype {t : Set α} (p : Set α → Prop) :
    (∃ s : Set t, p (coe ~~ s)) ↔ ∃ s : Set α, s ⊆ t ∧ p s := by
  constructor
  · rintro ⟨s, hs⟩
    refine' ⟨coe ~~ s, _, hs⟩
    convert image_subset_range _ _
    rw [range_coe]
  rintro ⟨s, hs₁, hs₂⟩; refine' ⟨coe ⁻¹' s, _⟩
  rw [image_preimage_eq_of_subset]; exact hs₂; rw [range_coe]; exact hs₁
#align subtype.exists_set_subtype Subtype.exists_set_subtype

theorem preimage_coe_nonempty {s t : Set α} : ((coe : s → α) ⁻¹' t).Nonempty ↔ (s ∩ t).Nonempty :=
  by rw [inter_comm, ← image_preimage_coe, nonempty_image_iff]
#align subtype.preimage_coe_nonempty Subtype.preimage_coe_nonempty

theorem preimage_coe_eq_empty {s t : Set α} : (coe : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ := by
  simp only [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]
#align subtype.preimage_coe_eq_empty Subtype.preimage_coe_eq_empty

@[simp]
theorem preimage_coe_compl (s : Set α) : (coe : s → α) ⁻¹' sᶜ = ∅ :=
  preimage_coe_eq_empty.2 (inter_compl_self s)
#align subtype.preimage_coe_compl Subtype.preimage_coe_compl

@[simp]
theorem preimage_coe_compl' (s : Set α) : (coe : sᶜ → α) ⁻¹' s = ∅ :=
  preimage_coe_eq_empty.2 (compl_inter_self s)
#align subtype.preimage_coe_compl' Subtype.preimage_coe_compl'

end Subtype

/-! ### Images and preimages on `option` -/


open Set

namespace Option

theorem injective_iff {α β} {f : Option α → β} :
    Injective f ↔ Injective (f ∘ some) ∧ f none ∉ range (f ∘ some) := by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine'
    ⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.Ne <| Option.some_ne_none _⟩, _⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts[rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]
#align option.injective_iff Option.injective_iff

theorem range_eq {α β} (f : Option α → β) : range f = insert (f none) (range (f ∘ some)) :=
  Set.ext fun y => Option.exists.trans <| eq_comm.Or Iff.rfl
#align option.range_eq Option.range_eq

end Option

theorem WithBot.range_eq {α β} (f : WithBot α → β) :
    range f = insert (f ⊥) (range (f ∘ coe : α → β)) :=
  Option.range_eq f
#align with_bot.range_eq WithBot.range_eq

theorem WithTop.range_eq {α β} (f : WithTop α → β) :
    range f = insert (f ⊤) (range (f ∘ coe : α → β)) :=
  Option.range_eq f
#align with_top.range_eq WithTop.range_eq

namespace Set

open Function

/-! ### Injectivity and sur<jectivity lemmas for image and preimage -/


section ImagePreimage

variable {α : Type u} {β : Type v} {f : α → β}

@[simp]
theorem preimage_injective : Injective (preimage f) ↔ Surjective f := by
  refine' ⟨fun h y => _, surjective.preimage_injective⟩
  obtain ⟨x, hx⟩ : (f ⁻¹' {y}).Nonempty := by
    rw [h.nonempty_apply_iff preimage_empty]
    apply singleton_nonempty
  exact ⟨x, hx⟩
#align set.preimage_injective Set.preimage_injective

@[simp]
theorem preimage_surjective : Surjective (preimage f) ↔ Injective f := by
  refine' ⟨fun h x x' hx => _, injective.preimage_surjective⟩
  cases' h {x} with s hs; have := mem_singleton x
  rwa [← hs, mem_preimage, hx, ← mem_preimage, hs, mem_singleton_iff, eq_comm] at this
#align set.preimage_surjective Set.preimage_surjective

@[simp]
theorem image_surjective : Surjective (image f) ↔ Surjective f := by
  refine' ⟨fun h y => _, surjective.image_surjective⟩
  cases' h {y} with s hs
  have := mem_singleton y; rw [← hs] at this; rcases this with ⟨x, h1x, h2x⟩
  exact ⟨x, h2x⟩
#align set.image_surjective Set.image_surjective

@[simp]
theorem image_injective : Injective (image f) ↔ Injective f := by
  refine' ⟨fun h x x' hx => _, injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]; apply h
  rw [image_singleton, image_singleton, hx]
#align set.image_injective Set.image_injective

theorem preimage_eq_iff_eq_image {f : α → β} (hf : Bijective f) {s t} : f ⁻¹' s = t ↔ s = f ~~ t :=
  by rw [← image_eq_image hf.1, hf.2.image_preimage]
#align set.preimage_eq_iff_eq_image Set.preimage_eq_iff_eq_image

theorem eq_preimage_iff_image_eq {f : α → β} (hf : Bijective f) {s t} : s = f ⁻¹' t ↔ f ~~ s = t :=
  by rw [← image_eq_image hf.1, hf.2.image_preimage]
#align set.eq_preimage_iff_image_eq Set.eq_preimage_iff_image_eq

end ImagePreimage

end Set
