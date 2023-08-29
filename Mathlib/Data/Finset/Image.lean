/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Algebra.Hom.Embedding
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Order.Basic

#align_import data.finset.image from "leanprover-community/mathlib"@"b685f506164f8d17a6404048bc4d696739c5d976"

/-! # Image and map operations on finite sets

This file provides the finite analog of `Set.image`, along with some other similar functions.

Note there are two ways to take the image over a finset; via `Finset.image` which applies the
function then removes duplicates (requiring `DecidableEq`), or via `Finset.map` which exploits
injectivity of the function to avoid needing to deduplicate. Choosing between these is similar to
choosing between `insert` and `Finset.cons`, or between `Finset.union` and `Finset.disjUnion`.

## Main definitions

* `Finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `Finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `Finset.subtype`: `s.subtype p` is the finset of `Subtype p` whose elements belong to `s`.
* `Finset.fin`:`s.fin n` is the finset of all elements of `s` less than `n`.

-/


variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

/-! ### map -/


section Map

open Function

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α ↪ β) (s : Finset α) : Finset β :=
  ⟨s.1.map f, s.2.map f.2⟩
#align finset.map Finset.map

@[simp]
theorem map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f :=
  rfl
#align finset.map_val Finset.map_val

@[simp]
theorem map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅ :=
  rfl
#align finset.map_empty Finset.map_empty

variable {f : α ↪ β} {s : Finset α}

@[simp]
theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  mem_map.trans <| by simp only [exists_prop]; rfl
                      -- ⊢ (∃ a, a ∈ s.val ∧ ↑f a = b) ↔ ∃ a, a ∈ s ∧ ↑f a = b
                                               -- 🎉 no goals
#align finset.mem_map Finset.mem_map

--Porting note: Higher priority to apply before `mem_map`.
@[simp 1100]
theorem mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.toEmbedding ↔ f.symm b ∈ s := by
  rw [mem_map]
  -- ⊢ (∃ a, a ∈ s ∧ ↑(Equiv.toEmbedding f) a = b) ↔ ↑f.symm b ∈ s
  exact
    ⟨by
      rintro ⟨a, H, rfl⟩
      simpa, fun h => ⟨_, h, by simp⟩⟩
#align finset.mem_map_equiv Finset.mem_map_equiv

-- The simpNF linter says that the LHS can be simplified via `Finset.mem_map`.
-- However this is a higher priority lemma.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem mem_map' (f : α ↪ β) {a} {s : Finset α} : f a ∈ s.map f ↔ a ∈ s :=
  mem_map_of_injective f.2
#align finset.mem_map' Finset.mem_map'

theorem mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a ∈ s → f a ∈ s.map f :=
  (mem_map' _).2
#align finset.mem_map_of_mem Finset.mem_map_of_mem

theorem forall_mem_map {f : α ↪ β} {s : Finset α} {p : ∀ a, a ∈ s.map f → Prop} :
    (∀ y (H : y ∈ s.map f), p y H) ↔ ∀ x (H : x ∈ s), p (f x) (mem_map_of_mem _ H) :=
  ⟨fun h y hy => h (f y) (mem_map_of_mem _ hy),
   fun h x hx => by
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    -- ⊢ p (↑f y) hx
    exact h _ hy⟩
    -- 🎉 no goals
#align finset.forall_mem_map Finset.forall_mem_map

theorem apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x ∈ s.map f :=
  mem_map_of_mem f x.prop
#align finset.apply_coe_mem_map Finset.apply_coe_mem_map

@[simp, norm_cast]
theorem coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s :=
  Set.ext (by simp only [mem_coe, mem_map, Set.mem_image, implies_true])
              -- 🎉 no goals
#align finset.coe_map Finset.coe_map

theorem coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) ⊆ Set.range f :=
  calc
    ↑(s.map f) = f '' s := coe_map f s
    _ ⊆ Set.range f := Set.image_subset_range f ↑s
#align finset.coe_map_subset_range Finset.coe_map_subset_range

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem map_perm {σ : Equiv.Perm α} (hs : { a | σ a ≠ a } ⊆ s) : s.map (σ : α ↪ α) = s :=
  coe_injective <| (coe_map _ _).trans <| Set.image_perm hs
#align finset.map_perm Finset.map_perm

theorem map_toFinset [DecidableEq α] [DecidableEq β] {s : Multiset α} :
    s.toFinset.map f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_map, Multiset.mem_map, exists_prop, Multiset.mem_toFinset]
                  -- 🎉 no goals
#align finset.map_to_finset Finset.map_toFinset

@[simp]
theorem map_refl : s.map (Embedding.refl _) = s :=
  ext fun _ => by simpa only [mem_map, exists_prop] using exists_eq_right
                  -- 🎉 no goals
#align finset.map_refl Finset.map_refl

@[simp]
theorem map_cast_heq {α β} (h : α = β) (s : Finset α) :
    HEq (s.map (Equiv.cast h).toEmbedding) s := by
  subst h
  -- ⊢ HEq (map (Equiv.toEmbedding (Equiv.cast (_ : α = α))) s) s
  simp
  -- 🎉 no goals
#align finset.map_cast_heq Finset.map_cast_heq

theorem map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map f).map g = s.map (f.trans g) :=
  eq_of_veq <| by simp only [map_val, Multiset.map_map]; rfl
                  -- ⊢ Multiset.map ((fun x => ↑g x) ∘ fun x => ↑f x) s.val = Multiset.map (fun x = …
                                                         -- 🎉 no goals
#align finset.map_map Finset.map_map

theorem map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.map g).map f = (s.map f').map g' := by
  simp_rw [map_map, Embedding.trans, Function.comp, h_comm]
  -- 🎉 no goals
#align finset.map_comm Finset.map_comm

theorem _root_.Function.Semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) := fun _ =>
  map_comm h
#align function.semiconj.finset_map Function.Semiconj.finset_map

theorem _root_.Function.Commute.finset_map {f g : α ↪ α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  Function.Semiconj.finset_map h
#align function.commute.finset_map Function.Commute.finset_map

@[simp]
theorem map_subset_map {s₁ s₂ : Finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
  ⟨fun h x xs => (mem_map' _).1 <| h <| (mem_map' f).2 xs,
   fun h => by simp [subset_def, Multiset.map_subset_map h]⟩
               -- 🎉 no goals
#align finset.map_subset_map Finset.map_subset_map

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
def mapEmbedding (f : α ↪ β) : Finset α ↪o Finset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_subset_map
#align finset.map_embedding Finset.mapEmbedding

@[simp]
theorem map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
  (mapEmbedding f).injective.eq_iff
#align finset.map_inj Finset.map_inj

theorem map_injective (f : α ↪ β) : Injective (map f) :=
  (mapEmbedding f).injective
#align finset.map_injective Finset.map_injective

@[simp]
theorem mapEmbedding_apply : mapEmbedding f s = map f s :=
  rfl
#align finset.map_embedding_apply Finset.mapEmbedding_apply

theorem filter_map {p : β → Prop} [DecidablePred p] :
    (s.map f).filter p = (s.filter (p ∘ f)).map f :=
  eq_of_veq (map_filter _ _ _)
#align finset.filter_map Finset.filter_map

theorem map_filter {f : α ≃ β} {p : α → Prop} [DecidablePred p] :
    (s.filter p).map f.toEmbedding = (s.map f.toEmbedding).filter (p ∘ f.symm) := by
  simp only [filter_map, Function.comp, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
  -- 🎉 no goals
#align finset.map_filter Finset.map_filter

@[simp]
theorem disjoint_map {s t : Finset α} (f : α ↪ β) :
    Disjoint (s.map f) (t.map f) ↔ Disjoint s t := by
  simp only [disjoint_iff_ne, mem_map, exists_prop, exists_imp, and_imp]
  -- ⊢ (∀ (a : β) (x : α), x ∈ s → ↑f x = a → ∀ (b : β) (x : α), x ∈ t → ↑f x = b → …
  refine' ⟨fun h a ha b hb hab => h _ _ ha rfl _ _ hb rfl <| congr_arg _ hab, _⟩
  -- ⊢ (∀ (a : α), a ∈ s → ∀ (b : α), b ∈ t → a ≠ b) → ∀ (a : β) (x : α), x ∈ s → ↑ …
  rintro h _ a ha rfl _ b hb rfl
  -- ⊢ ↑f a ≠ ↑f b
  exact f.injective.ne (h _ ha _ hb)
  -- 🎉 no goals
#align finset.disjoint_map Finset.disjoint_map

theorem map_disjUnion {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h' := (disjoint_map _).mpr h) :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  eq_of_veq <| Multiset.map_add _ _ _
#align finset.map_disj_union Finset.map_disjUnion

/-- A version of `Finset.map_disjUnion` for writing in the other direction. -/
theorem map_disjUnion' {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h := (disjoint_map _).mp h') :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  map_disjUnion _ _ _
#align finset.map_disj_union' Finset.map_disjUnion'

theorem map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
  coe_injective <| by simp only [coe_map, coe_union, Set.image_union]
                      -- 🎉 no goals
#align finset.map_union Finset.map_union

theorem map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
  coe_injective <| by simp only [coe_map, coe_inter, Set.image_inter f.injective]
                      -- 🎉 no goals
#align finset.map_inter Finset.map_inter

@[simp]
theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
  coe_injective <| by simp only [coe_map, coe_singleton, Set.image_singleton]
                      -- 🎉 no goals
#align finset.map_singleton Finset.map_singleton

@[simp]
theorem map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α) :
    (insert a s).map f = insert (f a) (s.map f) := by
  simp only [insert_eq, map_union, map_singleton]
  -- 🎉 no goals
#align finset.map_insert Finset.map_insert

@[simp]
theorem map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s) :
    (cons a s ha).map f = cons (f a) (s.map f) (by simpa using ha) :=
                                                   -- 🎉 no goals
  eq_of_veq <| Multiset.map_cons f a s.val
#align finset.map_cons Finset.map_cons

@[simp]
theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem fun _ m => ne_empty_of_mem (mem_map_of_mem _ m) h, fun e =>
    e.symm ▸ rfl⟩
#align finset.map_eq_empty Finset.map_eq_empty

@[simp]
theorem map_nonempty : (s.map f).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne.def, map_eq_empty]
  -- 🎉 no goals
#align finset.map_nonempty Finset.map_nonempty

alias ⟨_, Nonempty.map⟩ := map_nonempty
#align finset.nonempty.map Finset.Nonempty.map

theorem attach_map_val {s : Finset α} : s.attach.map (Embedding.subtype _) = s :=
  eq_of_veq <| by rw [map_val, attach_val]; exact Multiset.attach_map_val _
                  -- ⊢ Multiset.map (↑(Embedding.subtype fun x => x ∈ s)) (Multiset.attach s.val) = …
                                            -- 🎉 no goals
#align finset.attach_map_val Finset.attach_map_val

theorem disjoint_range_addLeftEmbedding (a b : ℕ) :
    Disjoint (range a) (map (addLeftEmbedding a) (range b)) := by
  refine' disjoint_iff_inf_le.mpr _
  -- ⊢ range a ⊓ map (addLeftEmbedding a) (range b) ≤ ⊥
  intro k hk
  -- ⊢ k ∈ ⊥
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, addLeftEmbedding, mem_inter]
    at hk
  obtain ⟨a, _, ha⟩ := hk.2
  -- ⊢ k ∈ ⊥
  simpa [← ha] using hk.1
  -- 🎉 no goals
#align finset.disjoint_range_add_left_embedding Finset.disjoint_range_addLeftEmbedding

theorem disjoint_range_addRightEmbedding (a b : ℕ) :
    Disjoint (range a) (map (addRightEmbedding a) (range b)) := by
  refine' disjoint_iff_inf_le.mpr _
  -- ⊢ range a ⊓ map (addRightEmbedding a) (range b) ≤ ⊥
  intro k hk
  -- ⊢ k ∈ ⊥
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, addRightEmbedding, mem_inter]
    at hk
  obtain ⟨a, _, ha⟩ := hk.2
  -- ⊢ k ∈ ⊥
  simpa [← ha] using hk.1
  -- 🎉 no goals
#align finset.disjoint_range_add_right_embedding Finset.disjoint_range_addRightEmbedding

theorem map_disjiUnion {f : α ↪ β} {s : Finset α} {t : β → Finset γ} {h} :
    (s.map f).disjiUnion t h =
      s.disjiUnion (fun a => t (f a)) fun _ ha _ hb hab =>
        h (mem_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.injective.ne hab) :=
  eq_of_veq <| Multiset.bind_map _ _ _
#align finset.map_disj_Union Finset.map_disjiUnion

theorem disjiUnion_map {s : Finset α} {t : α → Finset β} {f : β ↪ γ} {h} :
    (s.disjiUnion t h).map f =
      s.disjiUnion (fun a => (t a).map f) fun a ha b hb hab =>
        disjoint_left.mpr fun x hxa hxb => by
          obtain ⟨xa, hfa, rfl⟩ := mem_map.mp hxa
          -- ⊢ False
          obtain ⟨xb, hfb, hfab⟩ := mem_map.mp hxb
          -- ⊢ False
          obtain rfl := f.injective hfab
          -- ⊢ False
          exact disjoint_left.mp (h ha hb hab) hfa hfb :=
          -- 🎉 no goals
  eq_of_veq <| Multiset.map_bind _ _ _
#align finset.disj_Union_map Finset.disjiUnion_map

end Map

theorem range_add_one' (n : ℕ) :
    range (n + 1) = insert 0 ((range n).map ⟨fun i => i + 1, fun i j => by simp⟩) := by
                                                                           -- 🎉 no goals
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.succ_eq_add_one, Nat.zero_lt_succ n]
  -- ⊢ Nat.zero ∈ range (n + 1) ↔ Nat.zero ∈ insert 0 (map { toFun := fun i => i +  …
                     -- 🎉 no goals
                     -- 🎉 no goals
#align finset.range_add_one' Finset.range_add_one'

/-! ### image -/


section Image

variable [DecidableEq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset
#align finset.image Finset.image

@[simp]
theorem image_val (f : α → β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup :=
  rfl
#align finset.image_val Finset.image_val

@[simp]
theorem image_empty (f : α → β) : (∅ : Finset α).image f = ∅ :=
  rfl
#align finset.image_empty Finset.image_empty

variable {f g : α → β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

@[simp]
theorem mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b := by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map, exists_prop]
  -- 🎉 no goals
#align finset.mem_image Finset.mem_image

theorem mem_image_of_mem (f : α → β) {a} (h : a ∈ s) : f a ∈ s.image f :=
  mem_image.2 ⟨_, h, rfl⟩
#align finset.mem_image_of_mem Finset.mem_image_of_mem

theorem forall_image {p : β → Prop} : (∀ b ∈ s.image f, p b) ↔ ∀ a ∈ s, p (f a) := by
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  -- 🎉 no goals
#align finset.forall_image Finset.forall_image

--@[simp] Porting note: removing simp, `simp` [Nonempty] can prove it
theorem mem_image_const : c ∈ s.image (const α b) ↔ s.Nonempty ∧ b = c := by
  rw [mem_image]
  -- ⊢ (∃ a, a ∈ s ∧ const α b a = c) ↔ Finset.Nonempty s ∧ b = c
  simp only [exists_prop, const_apply, exists_and_right]
  -- ⊢ (∃ x, x ∈ s) ∧ b = c ↔ Finset.Nonempty s ∧ b = c
  rfl
  -- 🎉 no goals
#align finset.mem_image_const Finset.mem_image_const

theorem mem_image_const_self : b ∈ s.image (const α b) ↔ s.Nonempty :=
  mem_image_const.trans <| and_iff_left rfl
#align finset.mem_image_const_self Finset.mem_image_const_self

instance canLift (c) (p) [CanLift β α c p] :
    CanLift (Finset β) (Finset α) (image c) fun s => ∀ x ∈ s, p x where
  prf := by
    rintro ⟨⟨l⟩, hd : l.Nodup⟩ hl
    -- ⊢ ∃ y, image c y = { val := Quot.mk Setoid.r l, nodup := hd }
    lift l to List α using hl
    -- ⊢ ∃ y, image c y = { val := Quot.mk Setoid.r (List.map c l), nodup := hd }
    exact ⟨⟨l, hd.of_map _⟩, ext fun a => by simp⟩
    -- 🎉 no goals
#align finset.can_lift Finset.canLift

theorem image_congr (h : (s : Set α).EqOn f g) : Finset.image f s = Finset.image g s := by
  ext
  -- ⊢ a✝ ∈ image f s ↔ a✝ ∈ image g s
  simp_rw [mem_image, ← bex_def]
  -- ⊢ (∃ x x_1, f x = a✝) ↔ ∃ x x_1, g x = a✝
  exact bex_congr fun x hx => by rw [h hx]
  -- 🎉 no goals
#align finset.image_congr Finset.image_congr

theorem _root_.Function.Injective.mem_finset_image (hf : Injective f) :
    f a ∈ s.image f ↔ a ∈ s := by
  refine' ⟨fun h => _, Finset.mem_image_of_mem f⟩
  -- ⊢ a ∈ s
  obtain ⟨y, hy, heq⟩ := mem_image.1 h
  -- ⊢ a ∈ s
  exact hf heq ▸ hy
  -- 🎉 no goals
#align function.injective.mem_finset_image Function.Injective.mem_finset_image

theorem filter_mem_image_eq_image (f : α → β) (s : Finset α) (t : Finset β) (h : ∀ x ∈ s, f x ∈ t) :
    (t.filter fun y => y ∈ s.image f) = s.image f := by
  ext
  -- ⊢ a✝ ∈ filter (fun y => y ∈ image f s) t ↔ a✝ ∈ image f s
  simp only [mem_filter, mem_image, decide_eq_true_eq, and_iff_right_iff_imp, forall_exists_index,
    and_imp]
  rintro x xel rfl
  -- ⊢ f x ∈ t
  exact h _ xel
  -- 🎉 no goals
#align finset.filter_mem_image_eq_image Finset.filter_mem_image_eq_image

theorem fiber_nonempty_iff_mem_image (f : α → β) (s : Finset α) (y : β) :
    (s.filter fun x => f x = y).Nonempty ↔ y ∈ s.image f := by simp [Finset.Nonempty]
                                                               -- 🎉 no goals
#align finset.fiber_nonempty_iff_mem_image Finset.fiber_nonempty_iff_mem_image

@[simp, norm_cast]
theorem coe_image {f : α → β} : ↑(s.image f) = f '' ↑s :=
  Set.ext <| by simp only [mem_coe, mem_image, Set.mem_image, implies_true]
                -- 🎉 no goals
#align finset.coe_image Finset.coe_image

protected theorem Nonempty.image (h : s.Nonempty) (f : α → β) : (s.image f).Nonempty :=
  let ⟨a, ha⟩ := h
  ⟨f a, mem_image_of_mem f ha⟩
#align finset.nonempty.image Finset.Nonempty.image

@[simp]
theorem Nonempty.image_iff (f : α → β) : (s.image f).Nonempty ↔ s.Nonempty :=
  ⟨fun ⟨_, hy⟩ =>
    let ⟨x, hx, _⟩ := mem_image.mp hy
    ⟨x, hx⟩,
    fun h => h.image f⟩
#align finset.nonempty.image_iff Finset.Nonempty.image_iff

theorem image_toFinset [DecidableEq α] {s : Multiset α} :
    s.toFinset.image f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_image, Multiset.mem_toFinset, exists_prop, Multiset.mem_map]
                  -- 🎉 no goals
#align finset.image_to_finset Finset.image_toFinset

theorem image_val_of_injOn (H : Set.InjOn f s) : (image f s).1 = s.1.map f :=
  (s.2.map_on H).dedup
#align finset.image_val_of_inj_on Finset.image_val_of_injOn

@[simp]
theorem image_id [DecidableEq α] : s.image id = s :=
  ext fun _ => by simp only [mem_image, exists_prop, id, exists_eq_right]
                  -- 🎉 no goals
#align finset.image_id Finset.image_id

@[simp]
theorem image_id' [DecidableEq α] : (s.image fun x => x) = s :=
  image_id
#align finset.image_id' Finset.image_id'

theorem image_image [DecidableEq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
  eq_of_veq <| by simp only [image_val, dedup_map_dedup_eq, Multiset.map_map]
                  -- 🎉 no goals
#align finset.image_image Finset.image_image

theorem image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f : β → γ} {g : α → β} {f' : α → β'}
    {g' : β' → γ} (h_comm : ∀ a, f (g a) = g' (f' a)) :
    (s.image g).image f = (s.image f').image g' := by simp_rw [image_image, comp, h_comm]
                                                      -- 🎉 no goals
#align finset.image_comm Finset.image_comm

theorem _root_.Function.Semiconj.finset_image [DecidableEq α] {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun _ =>
  image_comm h
#align function.semiconj.finset_image Function.Semiconj.finset_image

theorem _root_.Function.Commute.finset_image [DecidableEq α] {f g : α → α}
    (h : Function.Commute f g) : Function.Commute (image f) (image g) :=
  Function.Semiconj.finset_image h
#align function.commute.finset_image Function.Commute.finset_image

theorem image_subset_image {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f := by
  simp only [subset_def, image_val, subset_dedup', dedup_subset', Multiset.map_subset_map h]
  -- 🎉 no goals
#align finset.image_subset_image Finset.image_subset_image

theorem image_subset_iff : s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
  calc
    s.image f ⊆ t ↔ f '' ↑s ⊆ ↑t := by norm_cast
                                       -- 🎉 no goals
    _ ↔ _ := Set.image_subset_iff
#align finset.image_subset_iff Finset.image_subset_iff

theorem image_mono (f : α → β) : Monotone (Finset.image f) := fun _ _ => image_subset_image
#align finset.image_mono Finset.image_mono

theorem image_subset_image_iff {t : Finset α} (hf : Injective f) :
    s.image f ⊆ t.image f ↔ s ⊆ t := by
  simp_rw [← coe_subset]
  -- ⊢ ↑(image f s) ⊆ ↑(image f t) ↔ ↑s ⊆ ↑t
  push_cast
  -- ⊢ f '' ↑s ⊆ f '' ↑t ↔ ↑s ⊆ ↑t
  exact Set.image_subset_image_iff hf
  -- 🎉 no goals
#align finset.image_subset_image_iff Finset.image_subset_image_iff

theorem coe_image_subset_range : ↑(s.image f) ⊆ Set.range f :=
  calc
    ↑(s.image f) = f '' ↑s := coe_image
    _ ⊆ Set.range f := Set.image_subset_range f ↑s
#align finset.coe_image_subset_range Finset.coe_image_subset_range

theorem image_filter {p : β → Prop} [DecidablePred p] :
    (s.image f).filter p = (s.filter (p ∘ f)).image f :=
  ext fun b => by
    simp only [mem_filter, mem_image, exists_prop]
    -- ⊢ (∃ a, a ∈ s ∧ f a = b) ∧ p b ↔ ∃ a, (a ∈ s ∧ (p ∘ f) a) ∧ f a = b
    exact
      ⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, ⟨h1, h2⟩, rfl⟩,
       by rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩
#align finset.image_filter Finset.image_filter

theorem image_union [DecidableEq α] {f : α → β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
  ext fun _ => by simp only [mem_image, mem_union, exists_prop, or_and_right, exists_or]
                  -- 🎉 no goals
#align finset.image_union Finset.image_union

theorem image_inter_subset [DecidableEq α] (f : α → β) (s t : Finset α) :
    (s ∩ t).image f ⊆ s.image f ∩ t.image f :=
  subset_inter (image_subset_image <| inter_subset_left _ _) <|
    image_subset_image <| inter_subset_right _ _
#align finset.image_inter_subset Finset.image_inter_subset

theorem image_inter_of_injOn [DecidableEq α] {f : α → β} (s t : Finset α)
    (hf : Set.InjOn f (s ∪ t)) : (s ∩ t).image f = s.image f ∩ t.image f :=
  coe_injective <| by
    push_cast
    -- ⊢ f '' (↑s ∩ ↑t) = f '' ↑s ∩ f '' ↑t
    exact Set.image_inter_on fun a ha b hb => hf (Or.inr ha) <| Or.inl hb
    -- 🎉 no goals
#align finset.image_inter_of_inj_on Finset.image_inter_of_injOn

theorem image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f) :
    (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
  image_inter_of_injOn _ _ <| hf.injOn _
#align finset.image_inter Finset.image_inter

@[simp]
theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
  ext fun x => by simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm
                  -- 🎉 no goals
#align finset.image_singleton Finset.image_singleton

@[simp]
theorem image_insert [DecidableEq α] (f : α → β) (a : α) (s : Finset α) :
    (insert a s).image f = insert (f a) (s.image f) := by
  simp only [insert_eq, image_singleton, image_union]
  -- 🎉 no goals
#align finset.image_insert Finset.image_insert

theorem erase_image_subset_image_erase [DecidableEq α] (f : α → β) (s : Finset α) (a : α) :
    (s.image f).erase (f a) ⊆ (s.erase a).image f := by
  simp only [subset_iff, and_imp, exists_prop, mem_image, exists_imp, mem_erase]
  -- ⊢ ∀ ⦃x : β⦄, x ≠ f a → ∀ (x_1 : α), x_1 ∈ s → f x_1 = x → ∃ a_4, (a_4 ≠ a ∧ a_ …
  rintro b hb x hx rfl
  -- ⊢ ∃ a_1, (a_1 ≠ a ∧ a_1 ∈ s) ∧ f a_1 = f x
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩
  -- 🎉 no goals
#align finset.erase_image_subset_image_erase Finset.erase_image_subset_image_erase

@[simp]
theorem image_erase [DecidableEq α] {f : α → β} (hf : Injective f) (s : Finset α) (a : α) :
    (s.erase a).image f = (s.image f).erase (f a) := by
  refine' (erase_image_subset_image_erase _ _ _).antisymm' fun b => _
  -- ⊢ b ∈ image f (erase s a) → b ∈ erase (image f s) (f a)
  simp only [mem_image, exists_prop, mem_erase]
  -- ⊢ (∃ a_1, (a_1 ≠ a ∧ a_1 ∈ s) ∧ f a_1 = b) → b ≠ f a ∧ ∃ a, a ∈ s ∧ f a = b
  rintro ⟨a', ⟨haa', ha'⟩, rfl⟩
  -- ⊢ f a' ≠ f a ∧ ∃ a, a ∈ s ∧ f a = f a'
  exact ⟨hf.ne haa', a', ha', rfl⟩
  -- 🎉 no goals
#align finset.image_erase Finset.image_erase

@[simp]
theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem fun _ m => ne_empty_of_mem (mem_image_of_mem _ m) h,
   fun e => e.symm ▸ rfl⟩
#align finset.image_eq_empty Finset.image_eq_empty

theorem image_sdiff [DecidableEq α] {f : α → β} (s t : Finset α) (hf : Injective f) :
    (s \ t).image f = s.image f \ t.image f :=
  coe_injective <| by
    push_cast
    -- ⊢ f '' (↑s \ ↑t) = f '' ↑s \ f '' ↑t
    exact Set.image_diff hf _ _
    -- 🎉 no goals
#align finset.image_sdiff Finset.image_sdiff

theorem image_symmDiff [DecidableEq α] {f : α → β} (s t : Finset α) (hf : Injective f) :
    (s ∆ t).image f = s.image f ∆ t.image f :=
  coe_injective <| by
    push_cast
    -- ⊢ f '' ↑s ∆ ↑t = (f '' ↑s) ∆ (f '' ↑t)
    exact Set.image_symmDiff hf _ _
    -- 🎉 no goals
#align finset.image_symm_diff Finset.image_symmDiff

@[simp]
theorem _root_.Disjoint.of_image_finset {s t : Finset α} {f : α → β}
    (h : Disjoint (s.image f) (t.image f)) : Disjoint s t :=
  disjoint_iff_ne.2 fun _ ha _ hb =>
    ne_of_apply_ne f <| h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
#align disjoint.of_image_finset Disjoint.of_image_finset

theorem mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image fun i => f i := by
  constructor
  -- ⊢ a ∈ Set.range f → a ∈ image (fun i => f i) (range n)
  · rintro ⟨i, hi⟩
    -- ⊢ a ∈ image (fun i => f i) (range n)
    simp only [mem_image, exists_prop, mem_range]
    -- ⊢ ∃ a_1, a_1 < n ∧ f a_1 = a
    exact ⟨i % n, Nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩
    -- 🎉 no goals
  · rintro h
    -- ⊢ a ∈ Set.range f
    simp only [mem_image, exists_prop, Set.mem_range, mem_range] at *
    -- ⊢ ∃ y, f y = a
    rcases h with ⟨i, _, ha⟩
    -- ⊢ ∃ y, f y = a
    exact ⟨i, ha⟩
    -- 🎉 no goals
#align finset.mem_range_iff_mem_finset_range_of_mod_eq' Finset.mem_range_iff_mem_finset_range_of_mod_eq'

theorem mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image (fun (i : ℕ) => f i) :=
  suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f ↑i = a by simpa [h]
                                                           -- 🎉 no goals
  have hn' : 0 < (n : ℤ) := Int.ofNat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 ≤ i % ↑n := Int.emod_nonneg _ (ne_of_gt hn')
      ⟨Int.toNat (i % n), by
        -- ⊢ i % ↑n < ↑n ∧ f (i % ↑n) = a
                                                       -- 🎉 no goals
        rw [← Int.ofNat_lt, Int.toNat_of_nonneg this]; exact ⟨Int.emod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
           -- 🎉 no goals
    ⟨i, by rw [Int.emod_eq_of_lt (Int.ofNat_zero_le _) (Int.ofNat_lt_ofNat_of_lt hi), ha]⟩
#align finset.mem_range_iff_mem_finset_range_of_mod_eq Finset.mem_range_iff_mem_finset_range_of_mod_eq

theorem range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [← val_inj, union_val]
  -- ⊢ (range (a + b)).val = (range a).val ∪ (map (addLeftEmbedding a) (range b)).val
  exact Multiset.range_add_eq_union a b
  -- 🎉 no goals
#align finset.range_add Finset.range_add

@[simp]
theorem attach_image_val [DecidableEq α] {s : Finset α} : s.attach.image Subtype.val = s :=
  eq_of_veq <| by rw [image_val, attach_val, Multiset.attach_map_val, dedup_eq_self]
                  -- 🎉 no goals
#align finset.attach_image_val Finset.attach_image_val
#align finset.attach_image_coe Finset.attach_image_val

@[simp]
theorem attach_insert [DecidableEq α] {a : α} {s : Finset α} :
    attach (insert a s) =
      insert (⟨a, mem_insert_self a s⟩ : { x // x ∈ insert a s })
        ((attach s).image fun x => ⟨x.1, mem_insert_of_mem x.2⟩) :=
  ext fun ⟨x, hx⟩ =>
    ⟨Or.casesOn (mem_insert.1 hx)
        (fun h : x = a => fun _ => mem_insert.2 <| Or.inl <| Subtype.eq h) fun h : x ∈ s => fun _ =>
        mem_insert_of_mem <| mem_image.2 <| ⟨⟨x, h⟩, mem_attach _ _, Subtype.eq rfl⟩,
      fun _ => Finset.mem_attach _ _⟩
#align finset.attach_insert Finset.attach_insert

theorem map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.image f :=
  eq_of_veq (s.map f).2.dedup.symm
#align finset.map_eq_image Finset.map_eq_image

@[simp]
theorem disjoint_image {s t : Finset α} {f : α → β} (hf : Injective f) :
    Disjoint (s.image f) (t.image f) ↔ Disjoint s t := by
  convert disjoint_map ⟨_, hf⟩ using 1
  -- ⊢ _root_.Disjoint (image f s) (image f t) ↔ _root_.Disjoint (map { toFun := f, …
  simp [map_eq_image]
  -- 🎉 no goals
#align finset.disjoint_image Finset.disjoint_image

theorem image_const {s : Finset α} (h : s.Nonempty) (b : β) : (s.image fun _ => b) = singleton b :=
  ext fun b' => by
    simp only [mem_image, exists_prop, exists_and_right, h.bex, true_and_iff, mem_singleton,
      eq_comm]
#align finset.image_const Finset.image_const

@[simp]
theorem map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) :
    (s.erase a).map f = (s.map f).erase (f a) := by
  simp_rw [map_eq_image]
  -- ⊢ image (↑f) (erase s a) = erase (image (↑f) s) (↑f a)
  exact s.image_erase f.2 a
  -- 🎉 no goals
#align finset.map_erase Finset.map_erase

theorem image_biUnion [DecidableEq γ] {f : α → β} {s : Finset α} {t : β → Finset γ} :
    (s.image f).biUnion t = s.biUnion fun a => t (f a) :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [image_insert, biUnion_insert, ih]
                                               -- 🎉 no goals
#align finset.image_bUnion Finset.image_biUnion

theorem biUnion_image [DecidableEq γ] {s : Finset α} {t : α → Finset β} {f : β → γ} :
    (s.biUnion t).image f = s.biUnion fun a => (t a).image f :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [biUnion_insert, image_union, ih]
                                               -- 🎉 no goals
#align finset.bUnion_image Finset.biUnion_image

theorem image_biUnion_filter_eq [DecidableEq α] (s : Finset β) (g : β → α) :
    ((s.image g).biUnion fun a => s.filter fun c => g c = a) = s :=
  biUnion_filter_eq_of_maps_to fun _ => mem_image_of_mem g
#align finset.image_bUnion_filter_eq Finset.image_biUnion_filter_eq

theorem biUnion_singleton {f : α → β} : (s.biUnion fun a => {f a}) = s.image f :=
  ext fun x => by simp only [mem_biUnion, mem_image, mem_singleton, eq_comm]
                  -- 🎉 no goals
#align finset.bUnion_singleton Finset.biUnion_singleton

end Image

/-! ### Subtype -/


section Subtype

/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `Subtype p` whose
elements belong to `s`. -/
protected def subtype {α} (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset (Subtype p) :=
  (s.filter p).attach.map
    ⟨fun x => ⟨x.1, by simpa using (Finset.mem_filter.1 x.2).2⟩,
                       -- 🎉 no goals
     fun x y H => Subtype.eq <| Subtype.mk.inj H⟩
#align finset.subtype Finset.subtype

@[simp]
theorem mem_subtype {p : α → Prop} [DecidablePred p] {s : Finset α} :
    ∀ {a : Subtype p}, a ∈ s.subtype p ↔ (a : α) ∈ s
  | ⟨a, ha⟩ => by simp [Finset.subtype, ha]
                  -- 🎉 no goals
#align finset.mem_subtype Finset.mem_subtype

theorem subtype_eq_empty {p : α → Prop} [DecidablePred p] {s : Finset α} :
    s.subtype p = ∅ ↔ ∀ x, p x → x ∉ s := by simp [ext_iff, Subtype.forall, Subtype.coe_mk]
                                             -- 🎉 no goals
#align finset.subtype_eq_empty Finset.subtype_eq_empty

@[mono]
theorem subtype_mono {p : α → Prop} [DecidablePred p] : Monotone (Finset.subtype p) :=
  fun _ _ h _ hx => mem_subtype.2 <| h <| mem_subtype.1 hx
#align finset.subtype_mono Finset.subtype_mono

/-- `s.subtype p` converts back to `s.filter p` with
`Embedding.subtype`. -/
@[simp]
theorem subtype_map (p : α → Prop) [DecidablePred p] {s : Finset α} :
    (s.subtype p).map (Embedding.subtype _) = s.filter p := by
  ext x
  -- ⊢ x ∈ map (Embedding.subtype p) (Finset.subtype p s) ↔ x ∈ filter p s
  simp [@and_comm _ (_ = _), @and_left_comm _ (_ = _), @and_comm (p x) (x ∈ s)]
  -- 🎉 no goals
#align finset.subtype_map Finset.subtype_map

/-- If all elements of a `Finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `Embedding.subtype`. -/
theorem subtype_map_of_mem {p : α → Prop} [DecidablePred p] {s : Finset α} (h : ∀ x ∈ s, p x) :
    (s.subtype p).map (Embedding.subtype _) = s := ext <| by simpa [subtype_map] using h
                                                             -- 🎉 no goals
#align finset.subtype_map_of_mem Finset.subtype_map_of_mem

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, all elements of the result have the property of
the subtype. -/
theorem property_of_mem_map_subtype {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : a ∈ s.map (Embedding.subtype _)) : p a := by
  rcases mem_map.1 h with ⟨x, _, rfl⟩
  -- ⊢ p (↑(Embedding.subtype fun x => p x) x)
  exact x.2
  -- 🎉 no goals
#align finset.property_of_mem_map_subtype Finset.property_of_mem_map_subtype

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
theorem not_mem_map_subtype_of_not_property {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : ¬p a) : a ∉ s.map (Embedding.subtype _) :=
  mt s.property_of_mem_map_subtype h
#align finset.not_mem_map_subtype_of_not_property Finset.not_mem_map_subtype_of_not_property

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, the result is a subset of the set giving the
subtype. -/
theorem map_subtype_subset {t : Set α} (s : Finset t) : ↑(s.map (Embedding.subtype _)) ⊆ t := by
  intro a ha
  -- ⊢ a ∈ t
  rw [mem_coe] at ha
  -- ⊢ a ∈ t
  convert property_of_mem_map_subtype s ha
  -- 🎉 no goals
#align finset.map_subtype_subset Finset.map_subtype_subset

end Subtype

/-! ### Fin -/


/-- Given a finset `s` of natural numbers and a bound `n`,
`s.fin n` is the finset of all elements of `s` less than `n`.
-/
protected def fin (n : ℕ) (s : Finset ℕ) : Finset (Fin n) :=
  (s.subtype _).map Fin.equivSubtype.symm.toEmbedding
#align finset.fin Finset.fin

@[simp]
theorem mem_fin {n} {s : Finset ℕ} : ∀ a : Fin n, a ∈ s.fin n ↔ (a : ℕ) ∈ s
  | ⟨a, ha⟩ => by simp [Finset.fin, ha, and_comm]
                  -- 🎉 no goals
#align finset.mem_fin Finset.mem_fin

@[mono]
theorem fin_mono {n} : Monotone (Finset.fin n) := fun s t h x => by simpa using @h x
                                                                    -- 🎉 no goals
#align finset.fin_mono Finset.fin_mono

@[simp]
theorem fin_map {n} {s : Finset ℕ} : (s.fin n).map Fin.valEmbedding = s.filter (· < n) := by
  simp [Finset.fin, Finset.map_map]
  -- 🎉 no goals
#align finset.fin_map Finset.fin_map

theorem subset_image_iff [DecidableEq β] {s : Set α} {t : Finset β} {f : α → β} :
    ↑t ⊆ f '' s ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ s'.image f = t := by
  constructor; swap
  -- ⊢ ↑t ⊆ f '' s → ∃ s', ↑s' ⊆ s ∧ image f s' = t
               -- ⊢ (∃ s', ↑s' ⊆ s ∧ image f s' = t) → ↑t ⊆ f '' s
  · rintro ⟨t, ht, rfl⟩
    -- ⊢ ↑(image f t) ⊆ f '' s
    rw [coe_image]
    -- ⊢ f '' ↑t ⊆ f '' s
    exact Set.image_subset f ht
    -- 🎉 no goals
  intro h
  -- ⊢ ∃ s', ↑s' ⊆ s ∧ image f s' = t
  letI : CanLift β s (f ∘ (↑)) fun y => y ∈ f '' s := ⟨fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
  -- ⊢ ∃ s', ↑s' ⊆ s ∧ image f s' = t
  lift t to Finset s using h
  -- ⊢ ∃ s', ↑s' ⊆ s ∧ image f s' = image (f ∘ Subtype.val) t
  refine' ⟨t.map (Embedding.subtype _), map_subtype_subset _, _⟩
  -- ⊢ image f (map (Embedding.subtype fun x => x ∈ s) t) = image (f ∘ Subtype.val) t
  ext y; simp
  -- ⊢ y ∈ image f (map (Embedding.subtype fun x => x ∈ s) t) ↔ y ∈ image (f ∘ Subt …
         -- 🎉 no goals
#align finset.subset_image_iff Finset.subset_image_iff

theorem range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).image Nat.succ := by
  induction' n with k hk
  -- ⊢ range (Nat.zero + 1) \ {0} = image Nat.succ (range Nat.zero)
  · simp
    -- 🎉 no goals
  conv_rhs => rw [range_succ]
  -- ⊢ range (Nat.succ k + 1) \ {0} = image Nat.succ (insert k (range k))
  rw [range_succ, image_insert, ← hk, insert_sdiff_of_not_mem]
  -- ⊢ ¬k + 1 ∈ {0}
  simp
  -- 🎉 no goals
#align finset.range_sdiff_zero Finset.range_sdiff_zero

end Finset

theorem Multiset.toFinset_map [DecidableEq α] [DecidableEq β] (f : α → β) (m : Multiset α) :
    (m.map f).toFinset = m.toFinset.image f :=
  Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm
#align multiset.to_finset_map Multiset.toFinset_map

namespace Equiv

/-- Given an equivalence `α` to `β`, produce an equivalence between `Finset α` and `Finset β`. -/
protected def finsetCongr (e : α ≃ β) : Finset α ≃ Finset β where
  toFun s := s.map e.toEmbedding
  invFun s := s.map e.symm.toEmbedding
  left_inv s := by simp [Finset.map_map]
                   -- 🎉 no goals
  right_inv s := by simp [Finset.map_map]
                    -- 🎉 no goals
#align equiv.finset_congr Equiv.finsetCongr

@[simp]
theorem finsetCongr_apply (e : α ≃ β) (s : Finset α) : e.finsetCongr s = s.map e.toEmbedding :=
  rfl
#align equiv.finset_congr_apply Equiv.finsetCongr_apply

@[simp]
theorem finsetCongr_refl : (Equiv.refl α).finsetCongr = Equiv.refl _ := by
  ext
  -- ⊢ a✝ ∈ ↑(Equiv.finsetCongr (Equiv.refl α)) x✝ ↔ a✝ ∈ ↑(Equiv.refl (Finset α)) x✝
  simp
  -- 🎉 no goals
#align equiv.finset_congr_refl Equiv.finsetCongr_refl

@[simp]
theorem finsetCongr_symm (e : α ≃ β) : e.finsetCongr.symm = e.symm.finsetCongr :=
  rfl
#align equiv.finset_congr_symm Equiv.finsetCongr_symm

@[simp]
theorem finsetCongr_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.finsetCongr.trans e'.finsetCongr = (e.trans e').finsetCongr := by
  ext
  -- ⊢ a✝ ∈ ↑((Equiv.finsetCongr e).trans (Equiv.finsetCongr e')) x✝ ↔ a✝ ∈ ↑(Equiv …
  simp [-Finset.mem_map, -Equiv.trans_toEmbedding]
  -- 🎉 no goals
#align equiv.finset_congr_trans Equiv.finsetCongr_trans

theorem finsetCongr_toEmbedding (e : α ≃ β) :
    e.finsetCongr.toEmbedding = (Finset.mapEmbedding e.toEmbedding).toEmbedding :=
  rfl
#align equiv.finset_congr_to_embedding Equiv.finsetCongr_toEmbedding

end Equiv
