/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Embedding.Set

/-!
## Instances

We provide the `Fintype` instance for the sum of two fintypes.
-/


universe u v

variable {α β : Type*}

open Finset

instance (α : Type u) (β : Type v) [Fintype α] [Fintype β] : Fintype (α ⊕ β) where
  elems := univ.disjSum univ
  complete := by rintro (_ | _) <;> simp

namespace Finset
variable {α β : Type*} {u : Finset (α ⊕ β)} {s : Finset α} {t : Finset β}

section left
variable [Fintype α] {u : Finset (α ⊕ β)}

lemma toLeft_eq_univ : u.toLeft = univ ↔ univ.map .inl ⊆ u := by
  simp [map_inl_subset_iff_subset_toLeft]

lemma toRight_eq_empty : u.toRight = ∅ ↔ u ⊆ univ.map .inl := by simp [subset_map_inl]

end left

section right
variable [Fintype β] {u : Finset (α ⊕ β)}

lemma toRight_eq_univ : u.toRight = univ ↔ univ.map .inr ⊆ u := by
  simp [map_inr_subset_iff_subset_toRight]

lemma toLeft_eq_empty : u.toLeft = ∅ ↔ u ⊆ univ.map .inr := by simp [subset_map_inr]

end right

variable [Fintype α] [Fintype β]

@[simp] lemma univ_disjSum_univ : univ.disjSum univ = (univ : Finset (α ⊕ β)) := rfl
@[simp] lemma toLeft_univ : (univ : Finset (α ⊕ β)).toLeft = univ := by ext; simp
@[simp] lemma toRight_univ : (univ : Finset (α ⊕ β)).toRight = univ := by ext; simp

end Finset

@[simp]
theorem Fintype.card_sum [Fintype α] [Fintype β] :
    Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β :=
  card_disjSum _ _

/-- If the subtype of all-but-one elements is a `Fintype` then the type itself is a `Fintype`. -/
def fintypeOfFintypeNe (a : α) (_ : Fintype { b // b ≠ a }) : Fintype α :=
  Fintype.ofBijective (Sum.elim ((↑) : { b // b = a } → α) ((↑) : { b // b ≠ a } → α)) <| by
    classical exact (Equiv.sumCompl (· = a)).bijective

theorem image_subtype_ne_univ_eq_image_erase [Fintype α] [DecidableEq β] (k : β) (b : α → β) :
    image (fun i : { a // b a ≠ k } => b ↑i) univ = (image b univ).erase k := by
  apply subset_antisymm
  · rw [image_subset_iff]
    intro i _
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _))
  · intro i hi
    rw [mem_image]
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩
    subst ha
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩

theorem image_subtype_univ_ssubset_image_univ [Fintype α] [DecidableEq β] (k : β) (b : α → β)
    (hk : k ∈ Finset.image b univ) (p : β → Prop) [DecidablePred p] (hp : ¬p k) :
    image (fun i : { a // p (b a) } => b ↑i) univ ⊂ image b univ := by
  grind

/-- Any injection from a finset `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
theorem Finset.exists_equiv_extend_of_card_eq [Fintype α] [DecidableEq β] {t : Finset β}
    (hαt : Fintype.card α = #t) {s : Finset α} {f : α → β} (hfst : Finset.image f s ⊆ t)
    (hfs : Set.InjOn f s) : ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i := by
  classical
    induction s using Finset.induction generalizing f with
    | empty =>
      obtain ⟨e⟩ : Nonempty (α ≃ ↥t) := by rwa [← Fintype.card_eq, Fintype.card_coe]
      use e
      simp
    | insert a s has H => ?_
    have hfst' : Finset.image f s ⊆ t := (Finset.image_mono _ (s.subset_insert a)).trans hfst
    have hfs' : Set.InjOn f s := hfs.mono (s.subset_insert a)
    obtain ⟨g', hg'⟩ := H hfst' hfs'
    have hfat : f a ∈ t := hfst (mem_image_of_mem _ (s.mem_insert_self a))
    use g'.trans (Equiv.swap (⟨f a, hfat⟩ : t) (g' a))
    simp_rw [mem_insert]
    rintro i (rfl | hi)
    · simp
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne, hg' _ hi]
    · exact
        ne_of_apply_ne Subtype.val
          (ne_of_eq_of_ne (hg' _ hi) <|
            hfs.ne (subset_insert _ _ hi) (mem_insert_self _ _) <| ne_of_mem_of_not_mem hi has)
    · exact g'.injective.ne (ne_of_mem_of_not_mem hi has)

/-- Any injection from a set `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
theorem Set.MapsTo.exists_equiv_extend_of_card_eq [Fintype α] {t : Finset β}
    (hαt : Fintype.card α = #t) {s : Set α} {f : α → β} (hfst : s.MapsTo f t)
    (hfs : Set.InjOn f s) : ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i := by
  classical
    let s' : Finset α := s.toFinset
    have hfst' : s'.image f ⊆ t := by simpa [s', ← Finset.coe_subset] using hfst
    have hfs' : Set.InjOn f s' := by simpa [s'] using hfs
    obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hαt hfst' hfs'
    refine ⟨g, fun i hi => ?_⟩
    apply hg
    simpa [s'] using hi

theorem Fintype.card_subtype_or (p q : α → Prop) [Fintype { x // p x }] [Fintype { x // q x }]
    [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } ≤ Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
    rw [Fintype.card_sum]

theorem Fintype.card_subtype_or_disjoint (p q : α → Prop) (h : Disjoint p q) [Fintype { x // p x }]
    [Fintype { x // q x }] [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } = Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert Fintype.card_congr (subtypeOrEquiv p q h)
    simp

attribute [local instance] Fintype.ofFinite in
@[simp]
theorem infinite_sum : Infinite (α ⊕ β) ↔ Infinite α ∨ Infinite β := by
  refine ⟨fun H => ?_, fun H => H.elim (@Sum.infinite_of_left α β) (@Sum.infinite_of_right α β)⟩
  contrapose! H; cases H
  infer_instance
