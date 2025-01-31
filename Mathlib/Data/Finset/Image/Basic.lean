/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image.Defs
import Mathlib.Data.Finset.SymmDiff

/-! # Lemmas about image and map operations on finite sets

-/
assert_not_exists OrderedCommMonoid
assert_not_exists MonoidWithZero
assert_not_exists MulAction

variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

/-! ### map -/


section Map

open Function

@[simp]
theorem map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅ :=
  rfl

variable {f : α ↪ β} {s : Finset α}

theorem filter_map {p : β → Prop} [DecidablePred p] :
    (s.map f).filter p = (s.filter (p ∘ f)).map f :=
  eq_of_veq (Multiset.filter_map _ _ _)

lemma map_filter' (p : α → Prop) [DecidablePred p] (f : α ↪ β) (s : Finset α)
    [DecidablePred (∃ a, p a ∧ f a = ·)] :
    (s.filter p).map f = (s.map f).filter fun b => ∃ a, p a ∧ f a = b := by
  simp [Function.comp_def, filter_map, f.injective.eq_iff]

lemma filter_attach' [DecidableEq α] (s : Finset α) (p : s → Prop) [DecidablePred p] :
    s.attach.filter p =
      (s.filter fun x => ∃ h, p ⟨x, h⟩).attach.map
        ⟨Subtype.map id <| filter_subset _ _, Subtype.map_injective _ injective_id⟩ :=
  eq_of_veq <| Multiset.filter_attach' _ _

lemma filter_attach (p : α → Prop) [DecidablePred p] (s : Finset α) :
    s.attach.filter (fun a : s ↦ p a) =
      (s.filter p).attach.map ((Embedding.refl _).subtypeMap mem_of_mem_filter) :=
  eq_of_veq <| Multiset.filter_attach _ _

theorem map_filter {f : α ≃ β} {p : α → Prop} [DecidablePred p] :
    (s.filter p).map f.toEmbedding = (s.map f.toEmbedding).filter (p ∘ f.symm) := by
  simp only [filter_map, Function.comp_def, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

@[simp]
theorem disjoint_map {s t : Finset α} (f : α ↪ β) :
    Disjoint (s.map f) (t.map f) ↔ Disjoint s t :=
  mod_cast Set.disjoint_image_iff f.injective (s := s) (t := t)

theorem map_disjUnion {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h' := (disjoint_map _).mpr h) :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  eq_of_veq <| Multiset.map_add _ _ _

/-- A version of `Finset.map_disjUnion` for writing in the other direction. -/
theorem map_disjUnion' {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h := (disjoint_map _).mp h') :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  map_disjUnion _ _ _

theorem map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
  mod_cast Set.image_union f s₁ s₂

theorem map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
  mod_cast Set.image_inter f.injective (s := s₁) (t := s₂)

@[simp]
theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
  coe_injective <| by simp only [coe_map, coe_singleton, Set.image_singleton]

@[simp]
theorem map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α) :
    (insert a s).map f = insert (f a) (s.map f) := by
  simp only [insert_eq, map_union, map_singleton]

@[simp]
theorem map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s) :
    (cons a s ha).map f = cons (f a) (s.map f) (by simpa using ha) :=
  eq_of_veq <| Multiset.map_cons f a s.val

@[simp]
theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ := (map_injective f).eq_iff' (map_empty f)

@[simp]
theorem map_nonempty : (s.map f).Nonempty ↔ s.Nonempty :=
  mod_cast Set.image_nonempty (f := f) (s := s)

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.map⟩ := map_nonempty

@[simp]
theorem map_nontrivial : (s.map f).Nontrivial ↔ s.Nontrivial :=
  mod_cast Set.image_nontrivial f.injective (s := s)

theorem attach_map_val {s : Finset α} : s.attach.map (Embedding.subtype _) = s :=
  eq_of_veq <| by rw [map_val, attach_val]; exact Multiset.attach_map_val _

end Map

theorem range_add_one' (n : ℕ) :
    range (n + 1) = insert 0 ((range n).map ⟨fun i => i + 1, fun i j => by simp⟩) := by
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.zero_lt_succ n]

/-! ### image -/


section Image

variable [DecidableEq β]

@[simp]
theorem image_empty (f : α → β) : (∅ : Finset α).image f = ∅ :=
  rfl

variable {f g : α → β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

--@[simp] Porting note: removing simp, `simp` [Nonempty] can prove it
theorem mem_image_const : c ∈ s.image (const α b) ↔ s.Nonempty ∧ b = c := by
  rw [mem_image]
  simp only [exists_prop, const_apply, exists_and_right]
  rfl

theorem mem_image_const_self : b ∈ s.image (const α b) ↔ s.Nonempty :=
  mem_image_const.trans <| and_iff_left rfl

@[simp]
lemma image_nonempty : (s.image f).Nonempty ↔ s.Nonempty :=
  mod_cast Set.image_nonempty (f := f) (s := (s : Set α))

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected theorem Nonempty.image (h : s.Nonempty) (f : α → β) : (s.image f).Nonempty :=
  image_nonempty.2 h

alias ⟨Nonempty.of_image, _⟩ := image_nonempty

theorem filter_image {p : β → Prop} [DecidablePred p] :
    (s.image f).filter p = (s.filter fun a ↦ p (f a)).image f :=
  ext fun b => by
    simp only [mem_filter, mem_image, exists_prop]
    exact
      ⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, ⟨h1, h2⟩, rfl⟩,
       by rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

@[deprecated filter_mem_eq_inter (since := "2024-09-15")]
theorem filter_mem_image_eq_image (f : α → β) (s : Finset α) (t : Finset β) (h : ∀ x ∈ s, f x ∈ t) :
    (t.filter fun y => y ∈ s.image f) = s.image f := by
  rwa [filter_mem_eq_inter, inter_eq_right, image_subset_iff]

theorem fiber_nonempty_iff_mem_image {y : β} : (s.filter (f · = y)).Nonempty ↔ y ∈ s.image f := by
  simp [Finset.Nonempty]

theorem image_union [DecidableEq α] {f : α → β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
  mod_cast Set.image_union f s₁ s₂

theorem image_inter_subset [DecidableEq α] (f : α → β) (s t : Finset α) :
    (s ∩ t).image f ⊆ s.image f ∩ t.image f :=
  (image_mono f).map_inf_le s t

theorem image_inter_of_injOn [DecidableEq α] {f : α → β} (s t : Finset α)
    (hf : Set.InjOn f (s ∪ t)) : (s ∩ t).image f = s.image f ∩ t.image f :=
  coe_injective <| by
    push_cast
    exact Set.image_inter_on fun a ha b hb => hf (Or.inr ha) <| Or.inl hb

theorem image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f) :
    (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
  image_inter_of_injOn _ _ hf.injOn

@[simp]
theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
  ext fun x => by simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm

@[simp]
theorem image_insert [DecidableEq α] (f : α → β) (a : α) (s : Finset α) :
    (insert a s).image f = insert (f a) (s.image f) := by
  simp only [insert_eq, image_singleton, image_union]

theorem erase_image_subset_image_erase [DecidableEq α] (f : α → β) (s : Finset α) (a : α) :
    (s.image f).erase (f a) ⊆ (s.erase a).image f := by
  simp only [subset_iff, and_imp, exists_prop, mem_image, exists_imp, mem_erase]
  rintro b hb x hx rfl
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩

@[simp]
theorem image_erase [DecidableEq α] {f : α → β} (hf : Injective f) (s : Finset α) (a : α) :
    (s.erase a).image f = (s.image f).erase (f a) :=
  coe_injective <| by push_cast [Set.image_diff hf, Set.image_singleton]; rfl

@[simp]
theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ := mod_cast Set.image_eq_empty (f := f) (s := s)

theorem image_sdiff [DecidableEq α] {f : α → β} (s t : Finset α) (hf : Injective f) :
    (s \ t).image f = s.image f \ t.image f :=
  mod_cast Set.image_diff hf s t

lemma image_sdiff_of_injOn [DecidableEq α] {t : Finset α} (hf : Set.InjOn f s) (hts : t ⊆ s) :
    (s \ t).image f = s.image f \ t.image f :=
  mod_cast Set.image_diff_of_injOn hf <| coe_subset.2 hts

open scoped symmDiff in
theorem image_symmDiff [DecidableEq α] {f : α → β} (s t : Finset α) (hf : Injective f) :
    (s ∆ t).image f = s.image f ∆ t.image f :=
  mod_cast Set.image_symmDiff hf s t

@[simp]
theorem _root_.Disjoint.of_image_finset {s t : Finset α} {f : α → β}
    (h : Disjoint (s.image f) (t.image f)) : Disjoint s t :=
  disjoint_iff_ne.2 fun _ ha _ hb =>
    ne_of_apply_ne f <| h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

theorem mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image fun i => f i := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [mem_image, exists_prop, mem_range]
    exact ⟨i % n, Nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩
  · rintro h
    simp only [mem_image, exists_prop, Set.mem_range, mem_range] at *
    rcases h with ⟨i, _, ha⟩
    exact ⟨i, ha⟩

theorem mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image (fun (i : ℕ) => f i) :=
  suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f ↑i = a by simpa [h]
  have hn' : 0 < (n : ℤ) := Int.ofNat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 ≤ i % ↑n := Int.emod_nonneg _ (ne_of_gt hn')
      ⟨Int.toNat (i % n), by
        rw [← Int.ofNat_lt, Int.toNat_of_nonneg this]; exact ⟨Int.emod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
    ⟨i, by rw [Int.emod_eq_of_lt (Int.ofNat_zero_le _) (Int.ofNat_lt_ofNat_of_lt hi), ha]⟩

@[simp]
theorem attach_image_val [DecidableEq α] {s : Finset α} : s.attach.image Subtype.val = s :=
  eq_of_veq <| by rw [image_val, attach_val, Multiset.attach_map_val, dedup_eq_self]

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

@[simp]
theorem disjoint_image {s t : Finset α} {f : α → β} (hf : Injective f) :
    Disjoint (s.image f) (t.image f) ↔ Disjoint s t :=
  mod_cast Set.disjoint_image_iff hf (s := s) (t := t)

theorem image_const {s : Finset α} (h : s.Nonempty) (b : β) : (s.image fun _ => b) = singleton b :=
  mod_cast Set.Nonempty.image_const (coe_nonempty.2 h) b

@[simp]
theorem map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) :
    (s.erase a).map f = (s.map f).erase (f a) := by
  simp_rw [map_eq_image]
  exact s.image_erase f.2 a

end Image

/-! ### filterMap -/

section FilterMap

variable (f : α → Option β) (s' : Finset α) {s t : Finset α}
  {f_inj : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a'}

@[simp]
theorem filterMap_empty : (∅ : Finset α).filterMap f f_inj = ∅ := rfl

end FilterMap

end Finset
