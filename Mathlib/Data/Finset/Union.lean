/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Basic
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

assert_not_exists MonoidWithZero
assert_not_exists MulAction

variable {α β γ : Type*} {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

namespace Finset
section DisjiUnion

/-- `disjiUnion s f h` is the set such that `a ∈ disjiUnion s f` iff `a ∈ f i` for some `i ∈ s`.
It is the same as `s.biUnion f`, but it does not require decidable equality on the type. The
hypothesis ensures that the sets are disjoint. -/
def disjiUnion (s : Finset α) (t : α → Finset β) (hf : (s : Set α).PairwiseDisjoint t) : Finset β :=
  ⟨s.val.bind (Finset.val ∘ t), Multiset.nodup_bind.2
    ⟨fun a _ ↦ (t a).nodup, s.nodup.pairwise fun _ ha _ hb hab ↦ disjoint_val.2 <| hf ha hb hab⟩⟩
#align finset.disj_Union Finset.disjUnionₓ -- Porting note: universes and more

@[simp]
lemma disjiUnion_val (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).1 = s.1.bind fun a ↦ (t a).1 := rfl
#align finset.disj_Union_val Finset.disjiUnion_val

@[simp] lemma disjiUnion_empty (t : α → Finset β) : disjiUnion ∅ t (by simp) = ∅ := rfl
#align finset.disj_Union_empty Finset.disjiUnion_empty

@[simp] lemma mem_disjiUnion {b : β} {h} : b ∈ s.disjiUnion t h ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, disjiUnion_val, Multiset.mem_bind, exists_prop]
#align finset.mem_disj_Union Finset.mem_disjiUnion

@[simp, norm_cast]
lemma coe_disjiUnion {h} : (s.disjiUnion t h : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp [Set.ext_iff, mem_disjiUnion, Set.mem_iUnion, iff_self_iff, mem_coe, imp_true_iff]
#align finset.coe_disj_Union Finset.coe_disjiUnion

@[simp] lemma disjiUnion_cons (a : α) (s : Finset α) (ha : a ∉ s) (f : α → Finset β) (H) :
    disjiUnion (cons a s ha) f H =
    (f a).disjUnion ((s.disjiUnion f) fun _ hb _ hc ↦ H (mem_cons_of_mem hb) (mem_cons_of_mem hc))
      (disjoint_left.2 fun _ hb h ↦
        let ⟨_, hc, h⟩ := mem_disjiUnion.mp h
        disjoint_left.mp
          (H (mem_cons_self a s) (mem_cons_of_mem hc) (ne_of_mem_of_not_mem hc ha).symm) hb h) :=
  eq_of_veq <| Multiset.cons_bind _ _ _
#align finset.disj_Union_cons Finset.disjiUnion_cons

@[simp] lemma singleton_disjiUnion (a : α) {h} : Finset.disjiUnion {a} t h = t a :=
  eq_of_veq <| Multiset.singleton_bind _ _
#align finset.singleton_disj_Union Finset.singleton_disjiUnion

lemma disjiUnion_disjiUnion (s : Finset α) (f : α → Finset β) (g : β → Finset γ) (h1 h2) :
    (s.disjiUnion f h1).disjiUnion g h2 =
      s.attach.disjiUnion
        (fun a ↦ ((f a).disjiUnion g) fun b hb c hc ↦
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
#align finset.disj_Union_disj_Union Finset.disjiUnion_disjiUnion

variable [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β}

private lemma pairwiseDisjoint_fibers : Set.PairwiseDisjoint ↑t fun a ↦ s.filter (f · = a) :=
  fun x' hx y' hy hne ↦ by
    simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

-- `simpNF` claims that the statement can't simplify itself, but it can (as of 2024-02-14)
@[simp, nolint simpNF] lemma disjiUnion_filter_eq (s : Finset α) (t : Finset β) (f : α → β) :
    t.disjiUnion (fun a ↦ s.filter (f · = a)) pairwiseDisjoint_fibers =
      s.filter fun c ↦ f c ∈ t :=
  ext fun b => by simpa using and_comm

lemma disjiUnion_filter_eq_of_maps_to (h : ∀ x ∈ s, f x ∈ t) :
    t.disjiUnion (fun a ↦ s.filter (f · = a)) pairwiseDisjoint_fibers = s := by
  simpa [filter_eq_self]
#align finset.disj_Union_filter_eq_of_maps_to Finset.disjiUnion_filter_eq_of_maps_to

end DisjiUnion

section BUnion
variable [DecidableEq β]

/-- `Finset.biUnion s t` is the union of `t a` over `a ∈ s`.

(This was formerly `bind` due to the monad structure on types with `DecidableEq`.) -/
protected def biUnion (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.1.bind fun a ↦ (t a).1).toFinset
#align finset.bUnion Finset.biUnion

@[simp] lemma biUnion_val (s : Finset α) (t : α → Finset β) :
    (s.biUnion t).1 = (s.1.bind fun a ↦ (t a).1).dedup := rfl
#align finset.bUnion_val Finset.biUnion_val

@[simp] lemma biUnion_empty : Finset.biUnion ∅ t = ∅ := rfl
#align finset.bUnion_empty Finset.biUnion_empty

@[simp] lemma mem_biUnion {b : β} : b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, biUnion_val, Multiset.mem_dedup, Multiset.mem_bind, exists_prop]
#align finset.mem_bUnion Finset.mem_biUnion

@[simp, norm_cast]
lemma coe_biUnion : (s.biUnion t : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp [Set.ext_iff, mem_biUnion, Set.mem_iUnion, iff_self_iff, mem_coe, imp_true_iff]
#align finset.coe_bUnion Finset.coe_biUnion

@[simp]
lemma biUnion_insert [DecidableEq α] {a : α} : (insert a s).biUnion t = t a ∪ s.biUnion t :=
  ext fun x ↦ by
    simp only [mem_biUnion, exists_prop, mem_union, mem_insert, or_and_right, exists_or,
      exists_eq_left]
#align finset.bUnion_insert Finset.biUnion_insert

lemma biUnion_congr (hs : s₁ = s₂) (ht : ∀ a ∈ s₁, t₁ a = t₂ a) : s₁.biUnion t₁ = s₂.biUnion t₂ :=
  ext fun x ↦ by
    -- Porting note: this entire proof was `simp [or_and_distrib_right, exists_or_distrib]`
    simp_rw [mem_biUnion]
    apply exists_congr
    simp (config := { contextual := true }) only [hs, and_congr_right_iff, ht, implies_true]
#align finset.bUnion_congr Finset.biUnion_congr

@[simp]
lemma disjiUnion_eq_biUnion (s : Finset α) (f : α → Finset β) (hf) :
    s.disjiUnion f hf = s.biUnion f := eq_of_veq (s.disjiUnion f hf).nodup.dedup.symm
#align finset.disj_Union_eq_bUnion Finset.disjiUnion_eq_biUnion

lemma biUnion_subset {s' : Finset β} : s.biUnion t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' := by
  simp only [subset_iff, mem_biUnion]
  exact ⟨fun H a ha b hb ↦ H ⟨a, ha, hb⟩, fun H b ⟨a, ha, hb⟩ ↦ H a ha hb⟩
#align finset.bUnion_subset Finset.biUnion_subset

@[simp]
lemma singleton_biUnion {a : α} : Finset.biUnion {a} t = t a := by
  classical rw [← insert_emptyc_eq, biUnion_insert, biUnion_empty, union_empty]
#align finset.singleton_bUnion Finset.singleton_biUnion

lemma biUnion_inter (s : Finset α) (f : α → Finset β) (t : Finset β) :
    s.biUnion f ∩ t = s.biUnion fun x ↦ f x ∩ t := by
  ext x
  simp only [mem_biUnion, mem_inter]
  tauto
#align finset.bUnion_inter Finset.biUnion_inter

lemma inter_biUnion (t : Finset β) (s : Finset α) (f : α → Finset β) :
    t ∩ s.biUnion f = s.biUnion fun x ↦ t ∩ f x := by
  rw [inter_comm, biUnion_inter]
  simp [inter_comm]
#align finset.inter_bUnion Finset.inter_biUnion

lemma biUnion_biUnion [DecidableEq γ] (s : Finset α) (f : α → Finset β) (g : β → Finset γ) :
    (s.biUnion f).biUnion g = s.biUnion fun a ↦ (f a).biUnion g := by
  ext
  simp only [Finset.mem_biUnion, exists_prop]
  simp_rw [← exists_and_right, ← exists_and_left, and_assoc]
  rw [exists_comm]
#align finset.bUnion_bUnion Finset.biUnion_biUnion

lemma bind_toFinset [DecidableEq α] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).toFinset = s.toFinset.biUnion fun a ↦ (t a).toFinset :=
  ext fun x ↦ by simp only [Multiset.mem_toFinset, mem_biUnion, Multiset.mem_bind, exists_prop]
#align finset.bind_to_finset Finset.bind_toFinset

lemma biUnion_mono (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) : s.biUnion t₁ ⊆ s.biUnion t₂ := by
  have : ∀ b a, a ∈ s → b ∈ t₁ a → ∃ a : α, a ∈ s ∧ b ∈ t₂ a := fun b a ha hb ↦
    ⟨a, ha, Finset.mem_of_subset (h a ha) hb⟩
  simpa only [subset_iff, mem_biUnion, exists_imp, and_imp, exists_prop]
#align finset.bUnion_mono Finset.biUnion_mono

lemma biUnion_subset_biUnion_of_subset_left (t : α → Finset β) (h : s₁ ⊆ s₂) :
    s₁.biUnion t ⊆ s₂.biUnion t := fun x ↦ by
  simp only [and_imp, mem_biUnion, exists_prop]; exact Exists.imp fun a ha ↦ ⟨h ha.1, ha.2⟩
#align finset.bUnion_subset_bUnion_of_subset_left Finset.biUnion_subset_biUnion_of_subset_left

lemma subset_biUnion_of_mem (u : α → Finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.biUnion u :=
  singleton_biUnion.superset.trans <|
    biUnion_subset_biUnion_of_subset_left u <| singleton_subset_iff.2 xs
#align finset.subset_bUnion_of_mem Finset.subset_biUnion_of_mem

@[simp]
lemma biUnion_subset_iff_forall_subset {α β : Type*} [DecidableEq β] {s : Finset α}
    {t : Finset β} {f : α → Finset β} : s.biUnion f ⊆ t ↔ ∀ x ∈ s, f x ⊆ t :=
  ⟨fun h _ hx ↦ (subset_biUnion_of_mem f hx).trans h, fun h _ hx ↦
    let ⟨_, ha₁, ha₂⟩ := mem_biUnion.mp hx
    h _ ha₁ ha₂⟩
#align finset.bUnion_subset_iff_forall_subset Finset.biUnion_subset_iff_forall_subset

@[simp]
lemma biUnion_singleton_eq_self [DecidableEq α] : s.biUnion (singleton : α → Finset α) = s :=
  ext fun x ↦ by simp only [mem_biUnion, mem_singleton, exists_prop, exists_eq_right']
#align finset.bUnion_singleton_eq_self Finset.biUnion_singleton_eq_self

lemma filter_biUnion (s : Finset α) (f : α → Finset β) (p : β → Prop) [DecidablePred p] :
    (s.biUnion f).filter p = s.biUnion fun a ↦ (f a).filter p := by
  ext b
  simp only [mem_biUnion, exists_prop, mem_filter]
  constructor
  · rintro ⟨⟨a, ha, hba⟩, hb⟩
    exact ⟨a, ha, hba, hb⟩
  · rintro ⟨a, ha, hba, hb⟩
    exact ⟨⟨a, ha, hba⟩, hb⟩
#align finset.filter_bUnion Finset.filter_biUnion

lemma biUnion_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β} {f : α → β}
    (h : ∀ x ∈ s, f x ∈ t) : (t.biUnion fun a ↦ s.filter fun c ↦ f c = a) = s := by
  simpa only [disjiUnion_eq_biUnion] using disjiUnion_filter_eq_of_maps_to h
#align finset.bUnion_filter_eq_of_maps_to Finset.biUnion_filter_eq_of_maps_to

lemma erase_biUnion (f : α → Finset β) (s : Finset α) (b : β) :
    (s.biUnion f).erase b = s.biUnion fun x ↦ (f x).erase b := by
  ext a
  simp only [mem_biUnion, not_exists, not_and, mem_erase, ne_eq]
  tauto
#align finset.erase_bUnion Finset.erase_biUnion

@[simp]
lemma biUnion_nonempty : (s.biUnion t).Nonempty ↔ ∃ x ∈ s, (t x).Nonempty := by
  simp only [Finset.Nonempty, mem_biUnion]
  rw [exists_swap]
  simp [exists_and_left]
#align finset.bUnion_nonempty Finset.biUnion_nonempty

lemma Nonempty.biUnion (hs : s.Nonempty) (ht : ∀ x ∈ s, (t x).Nonempty) :
    (s.biUnion t).Nonempty := biUnion_nonempty.2 <| hs.imp fun x hx ↦ ⟨hx, ht x hx⟩
#align finset.nonempty.bUnion Finset.Nonempty.biUnion

lemma disjoint_biUnion_left (s : Finset α) (f : α → Finset β) (t : Finset β) :
    Disjoint (s.biUnion f) t ↔ ∀ i ∈ s, Disjoint (f i) t := by
  classical
  refine s.induction ?_ ?_
  · simp only [forall_mem_empty_iff, biUnion_empty, disjoint_empty_left]
  · intro i s his ih
    simp only [disjoint_union_left, biUnion_insert, his, forall_mem_insert, ih]
#align finset.disjoint_bUnion_left Finset.disjoint_biUnion_left

lemma disjoint_biUnion_right (s : Finset β) (t : Finset α) (f : α → Finset β) :
    Disjoint s (t.biUnion f) ↔ ∀ i ∈ t, Disjoint s (f i) := by
  simpa only [_root_.disjoint_comm] using disjoint_biUnion_left t f s
#align finset.disjoint_bUnion_right Finset.disjoint_biUnion_right

end BUnion
end Finset
