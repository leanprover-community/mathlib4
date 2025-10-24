/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Multiset.Bind
import Mathlib.Order.SetNotation

/-!
# Unions of finite sets

This file defines the union of a family `t : α → Finset β` of finsets bounded by a finset
`s : Finset α`.

## Main declarations

* `Finset.disjUnion`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disjUnion t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.
* `Finset.biUnion`: Finite unions of finsets; given an indexing function `f : α → Finset β` and an
  `s : Finset α`, `s.biUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.

## TODO

Remove `Finset.biUnion` in favour of `Finset.sup`.
-/

assert_not_exists MonoidWithZero MulAction

variable {α β γ : Type*} {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

namespace Finset
section DisjiUnion

/-- `disjiUnion s f h` is the set such that `a ∈ disjiUnion s f` iff `a ∈ f i` for some `i ∈ s`.
It is the same as `s.biUnion f`, but it does not require decidable equality on the type. The
hypothesis ensures that the sets are disjoint. -/
def disjiUnion (s : Finset α) (t : α → Finset β) (hf : (s : Set α).PairwiseDisjoint t) : Finset β :=
  ⟨s.val.bind (Finset.val ∘ t), Multiset.nodup_bind.2
    ⟨fun a _ ↦ (t a).nodup, s.nodup.pairwise fun _ ha _ hb hab ↦ disjoint_val.2 <| hf ha hb hab⟩⟩

@[simp]
lemma disjiUnion_val (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).1 = s.1.bind fun a ↦ (t a).1 := rfl

@[simp] lemma disjiUnion_empty (t : α → Finset β) : disjiUnion ∅ t (by simp) = ∅ := rfl

@[simp, grind =, push]
lemma mem_disjiUnion {b : β} {h} : b ∈ s.disjiUnion t h ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, disjiUnion_val, Multiset.mem_bind]

@[simp, norm_cast]
lemma coe_disjiUnion {h} : (s.disjiUnion t h : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp [Set.ext_iff, mem_disjiUnion, Set.mem_iUnion, mem_coe]

@[simp] lemma disjiUnion_cons (a : α) (s : Finset α) (ha : a ∉ s) (f : α → Finset β) (H) :
    disjiUnion (cons a s ha) f H =
    (f a).disjUnion ((s.disjiUnion f) fun _ hb _ hc ↦ H (mem_cons_of_mem hb) (mem_cons_of_mem hc))
      (disjoint_left.2 fun _ hb h ↦
        let ⟨_, hc, h⟩ := mem_disjiUnion.mp h
        disjoint_left.mp
          (H (mem_cons_self a s) (mem_cons_of_mem hc) (ne_of_mem_of_not_mem hc ha).symm) hb h) :=
  eq_of_veq <| Multiset.cons_bind _ _ _

@[simp] lemma singleton_disjiUnion (a : α) {h} : Finset.disjiUnion {a} t h = t a :=
  eq_of_veq <| Multiset.singleton_bind _ _

lemma disjiUnion_disjiUnion (s : Finset α) (f : α → Finset β) (g : β → Finset γ) (h1 h2) :
    (s.disjiUnion f h1).disjiUnion g h2 =
      s.attach.disjiUnion
        (fun a ↦ ((f a).disjiUnion g) fun _ hb _ hc ↦
            h2 (mem_disjiUnion.mpr ⟨_, a.prop, hb⟩) (mem_disjiUnion.mpr ⟨_, a.prop, hc⟩))
        fun a _ b _ hab ↦
        disjoint_left.mpr fun x hxa hxb ↦ by
          obtain ⟨xa, hfa, hga⟩ := mem_disjiUnion.mp hxa
          obtain ⟨xb, hfb, hgb⟩ := mem_disjiUnion.mp hxb
          refine disjoint_left.mp
            (h2 (mem_disjiUnion.mpr ⟨_, a.prop, hfa⟩) (mem_disjiUnion.mpr ⟨_, b.prop, hfb⟩) ?_) hga
            hgb
          rintro rfl
          exact disjoint_left.mp (h1 a.prop b.prop <| Subtype.coe_injective.ne hab) hfa hfb :=
  eq_of_veq <| Multiset.bind_assoc.trans (Multiset.attach_bind_coe _ _).symm

lemma sUnion_disjiUnion {f : α → Finset (Set β)} (I : Finset α)
    (hf : (I : Set α).PairwiseDisjoint f) :
    ⋃₀ (I.disjiUnion f hf : Set (Set β)) = ⋃ a ∈ I, ⋃₀ ↑(f a) := by
  ext
  simp only [coe_disjiUnion, Set.mem_sUnion, Set.mem_iUnion, mem_coe, exists_prop]
  tauto

section DecidableEq

variable [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β}

private lemma pairwiseDisjoint_fibers : Set.PairwiseDisjoint ↑t fun a ↦ s.filter (f · = a) :=
  fun x' hx y' hy hne ↦ by
    simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[simp] lemma disjiUnion_filter_eq (s : Finset α) (t : Finset β) (f : α → β) :
    t.disjiUnion (fun a ↦ s.filter (f · = a)) pairwiseDisjoint_fibers =
      s.filter fun c ↦ f c ∈ t :=
  ext fun b => by simpa using and_comm

lemma disjiUnion_filter_eq_of_maps_to (h : ∀ x ∈ s, f x ∈ t) :
    t.disjiUnion (fun a ↦ s.filter (f · = a)) pairwiseDisjoint_fibers = s := by
  simpa [filter_eq_self]

end DecidableEq

theorem map_disjiUnion {f : α ↪ β} {s : Finset α} {t : β → Finset γ} {h} :
    (s.map f).disjiUnion t h =
      s.disjiUnion (fun a => t (f a)) fun _ ha _ hb hab =>
        h (mem_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.injective.ne hab) :=
  eq_of_veq <| Multiset.bind_map _ _ _

theorem disjiUnion_map {s : Finset α} {t : α → Finset β} {f : β ↪ γ} {h} :
    (s.disjiUnion t h).map f =
      s.disjiUnion (fun a => (t a).map f) (h.mono' fun _ _ ↦ (disjoint_map _).2) :=
  eq_of_veq <| Multiset.map_bind _ _ _

variable {f : α → β} {op : β → β → β} [hc : Std.Commutative op] [ha : Std.Associative op]

theorem fold_disjiUnion {ι : Type*} {s : Finset ι} {t : ι → Finset α} {b : ι → β} {b₀ : β} (h) :
    (s.disjiUnion t h).fold op (s.fold op b₀ b) f = s.fold op b₀ fun i => (t i).fold op (b i) f :=
  (congr_arg _ <| Multiset.map_bind _ _ _).trans (Multiset.fold_bind _ _ _ _ _)

lemma pairwiseDisjoint_filter {f : α → Finset β} (h : Set.PairwiseDisjoint ↑s f)
    (p : β → Prop) [DecidablePred p] : Set.PairwiseDisjoint ↑s fun a ↦ (f a).filter p :=
  fun _ h₁ _ h₂ hne ↦ Finset.disjoint_filter_filter (h h₁ h₂ hne)

theorem filter_disjiUnion (s : Finset α) (f : α → Finset β) (h) (p : β → Prop) [DecidablePred p] :
    (s.disjiUnion f h).filter p
      = s.disjiUnion (fun a ↦ (f a).filter p) (pairwiseDisjoint_filter h p) := by grind

end DisjiUnion

section BUnion
variable [DecidableEq β]

/-- `Finset.biUnion s t` is the union of `t a` over `a ∈ s`.

(This was formerly `bind` due to the monad structure on types with `DecidableEq`.) -/
protected def biUnion (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.1.bind fun a ↦ (t a).1).toFinset

@[simp] lemma biUnion_val (s : Finset α) (t : α → Finset β) :
    (s.biUnion t).1 = (s.1.bind fun a ↦ (t a).1).dedup := rfl

@[simp] lemma biUnion_empty : Finset.biUnion ∅ t = ∅ := rfl

@[simp, grind =, push] lemma mem_biUnion {b : β} : b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, biUnion_val, Multiset.mem_dedup, Multiset.mem_bind]

@[simp, norm_cast]
lemma coe_biUnion : (s.biUnion t : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp [Set.ext_iff, mem_biUnion, Set.mem_iUnion, mem_coe]

@[simp]
lemma biUnion_insert [DecidableEq α] {a : α} : (insert a s).biUnion t = t a ∪ s.biUnion t := by
  aesop

lemma biUnion_congr (hs : s₁ = s₂) (ht : ∀ a ∈ s₁, t₁ a = t₂ a) :
    s₁.biUnion t₁ = s₂.biUnion t₂ := by
  aesop

@[simp]
lemma disjiUnion_eq_biUnion (s : Finset α) (f : α → Finset β) (hf) :
    s.disjiUnion f hf = s.biUnion f := eq_of_veq (s.disjiUnion f hf).nodup.dedup.symm

lemma biUnion_subset {s' : Finset β} : s.biUnion t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' := by grind

@[simp]
lemma singleton_biUnion {a : α} : Finset.biUnion {a} t = t a := by grind

lemma biUnion_inter (s : Finset α) (f : α → Finset β) (t : Finset β) :
    s.biUnion f ∩ t = s.biUnion fun x ↦ f x ∩ t := by grind

lemma inter_biUnion (t : Finset β) (s : Finset α) (f : α → Finset β) :
    t ∩ s.biUnion f = s.biUnion fun x ↦ t ∩ f x := by grind

lemma biUnion_biUnion [DecidableEq γ] (s : Finset α) (f : α → Finset β) (g : β → Finset γ) :
    (s.biUnion f).biUnion g = s.biUnion fun a ↦ (f a).biUnion g := by grind

lemma bind_toFinset [DecidableEq α] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).toFinset = s.toFinset.biUnion fun a ↦ (t a).toFinset :=
  ext fun x ↦ by simp only [Multiset.mem_toFinset, mem_biUnion, Multiset.mem_bind]

lemma biUnion_mono (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) : s.biUnion t₁ ⊆ s.biUnion t₂ := by grind

@[gcongr]
lemma biUnion_subset_biUnion_of_subset_left (t : α → Finset β) (h : s₁ ⊆ s₂) :
    s₁.biUnion t ⊆ s₂.biUnion t := by grind

lemma subset_biUnion_of_mem (u : α → Finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.biUnion u := by grind

@[simp]
lemma biUnion_subset_iff_forall_subset {α β : Type*} [DecidableEq β] {s : Finset α}
    {t : Finset β} {f : α → Finset β} : s.biUnion f ⊆ t ↔ ∀ x ∈ s, f x ⊆ t := by grind

@[simp]
lemma biUnion_singleton_eq_self [DecidableEq α] : s.biUnion (singleton : α → Finset α) = s := by
  grind

lemma filter_biUnion (s : Finset α) (f : α → Finset β) (p : β → Prop) [DecidablePred p] :
    (s.biUnion f).filter p = s.biUnion fun a ↦ (f a).filter p := by grind

lemma biUnion_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β} {f : α → β}
    (h : ∀ x ∈ s, f x ∈ t) : (t.biUnion fun a ↦ s.filter fun c ↦ f c = a) = s := by grind

lemma erase_biUnion (f : α → Finset β) (s : Finset α) (b : β) :
    (s.biUnion f).erase b = s.biUnion fun x ↦ (f x).erase b := by grind

@[simp]
lemma biUnion_nonempty : (s.biUnion t).Nonempty ↔ ∃ x ∈ s, (t x).Nonempty := by
  simp only [Finset.Nonempty, mem_biUnion]
  rw [exists_swap]
  simp [exists_and_left]

lemma Nonempty.biUnion (hs : s.Nonempty) (ht : ∀ x ∈ s, (t x).Nonempty) :
    (s.biUnion t).Nonempty := biUnion_nonempty.2 <| hs.imp fun x hx ↦ ⟨hx, ht x hx⟩

lemma disjoint_biUnion_left (s : Finset α) (f : α → Finset β) (t : Finset β) :
    Disjoint (s.biUnion f) t ↔ ∀ i ∈ s, Disjoint (f i) t := by
  classical
  refine s.induction ?_ ?_
  · simp only [forall_mem_empty_iff, biUnion_empty, disjoint_empty_left]
  · intro i s his ih
    simp only [disjoint_union_left, biUnion_insert, forall_mem_insert, ih]

lemma disjoint_biUnion_right (s : Finset β) (t : Finset α) (f : α → Finset β) :
    Disjoint s (t.biUnion f) ↔ ∀ i ∈ t, Disjoint s (f i) := by
  simpa only [_root_.disjoint_comm] using disjoint_biUnion_left t f s

theorem image_biUnion [DecidableEq γ] {f : α → β} {s : Finset α} {t : β → Finset γ} :
    (s.image f).biUnion t = s.biUnion fun a => t (f a) :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [image_insert, biUnion_insert, ih]

theorem biUnion_image [DecidableEq γ] {s : Finset α} {t : α → Finset β} {f : β → γ} :
    (s.biUnion t).image f = s.biUnion fun a => (t a).image f :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [biUnion_insert, image_union, ih]

theorem image_biUnion_filter_eq [DecidableEq α] (s : Finset β) (g : β → α) :
    ((s.image g).biUnion fun a => s.filter fun c => g c = a) = s :=
  biUnion_filter_eq_of_maps_to fun _ => mem_image_of_mem g

theorem biUnion_singleton {f : α → β} : (s.biUnion fun a => {f a}) = s.image f := by grind

end BUnion
end Finset
