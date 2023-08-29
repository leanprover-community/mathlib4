/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Embedding.Set

#align_import data.fintype.sum from "leanprover-community/mathlib"@"6623e6af705e97002a9054c1c05a980180276fc1"

/-!
## Instances

We provide the `Fintype` instance for the sum of two fintypes.
-/


universe u v

variable {α β : Type*}

open Finset

instance (α : Type u) (β : Type v) [Fintype α] [Fintype β] : Fintype (Sum α β) where
  elems := univ.disjSum univ
  complete := by rintro (_ | _) <;> simp
                 -- ⊢ Sum.inl val✝ ∈ disjSum univ univ
                                    -- 🎉 no goals
                                    -- 🎉 no goals

@[simp]
theorem Finset.univ_disjSum_univ {α β : Type*} [Fintype α] [Fintype β] :
    univ.disjSum univ = (univ : Finset (Sum α β)) :=
  rfl
#align finset.univ_disj_sum_univ Finset.univ_disjSum_univ

@[simp]
theorem Fintype.card_sum [Fintype α] [Fintype β] :
    Fintype.card (Sum α β) = Fintype.card α + Fintype.card β :=
  card_disjSum _ _
#align fintype.card_sum Fintype.card_sum

/-- If the subtype of all-but-one elements is a `Fintype` then the type itself is a `Fintype`. -/
def fintypeOfFintypeNe (a : α) (h : Fintype { b // b ≠ a }) : Fintype α :=
  Fintype.ofBijective (Sum.elim ((↑) : { b // b = a } → α) ((↑) : { b // b ≠ a } → α)) <| by
    classical exact (Equiv.sumCompl (· = a)).bijective
    -- 🎉 no goals
#align fintype_of_fintype_ne fintypeOfFintypeNe

theorem image_subtype_ne_univ_eq_image_erase [Fintype α] [DecidableEq β] (k : β) (b : α → β) :
    image (fun i : { a // b a ≠ k } => b ↑i) univ = (image b univ).erase k := by
  apply subset_antisymm
  -- ⊢ image (fun i => b ↑i) univ ⊆ erase (image b univ) k
  · rw [image_subset_iff]
    -- ⊢ ∀ (x : { a // b a ≠ k }), x ∈ univ → b ↑x ∈ erase (image b univ) k
    intro i _
    -- ⊢ b ↑i ∈ erase (image b univ) k
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _))
    -- 🎉 no goals
  · intro i hi
    -- ⊢ i ∈ image (fun i => b ↑i) univ
    rw [mem_image]
    -- ⊢ ∃ a, a ∈ univ ∧ b ↑a = i
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩
    -- ⊢ ∃ a, a ∈ univ ∧ b ↑a = i
    subst ha
    -- ⊢ ∃ a_1, a_1 ∈ univ ∧ b ↑a_1 = b a
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩
    -- 🎉 no goals
#align image_subtype_ne_univ_eq_image_erase image_subtype_ne_univ_eq_image_erase

theorem image_subtype_univ_ssubset_image_univ [Fintype α] [DecidableEq β] (k : β) (b : α → β)
    (hk : k ∈ Finset.image b univ) (p : β → Prop) [DecidablePred p] (hp : ¬p k) :
    image (fun i : { a // p (b a) } => b ↑i) univ ⊂ image b univ := by
  constructor
  -- ⊢ image (fun i => b ↑i) univ ⊆ image b univ
  · intro x hx
    -- ⊢ x ∈ image b univ
    rcases mem_image.1 hx with ⟨y, _, hy⟩
    -- ⊢ x ∈ image b univ
    exact hy ▸ mem_image_of_mem b (mem_univ (y : α))
    -- 🎉 no goals
  · intro h
    -- ⊢ False
    rw [mem_image] at hk
    -- ⊢ False
    rcases hk with ⟨k', _, hk'⟩
    -- ⊢ False
    subst hk'
    -- ⊢ False
    have := h (mem_image_of_mem b (mem_univ k'))
    -- ⊢ False
    rw [mem_image] at this
    -- ⊢ False
    rcases this with ⟨j, _, hj'⟩
    -- ⊢ False
    exact hp (hj' ▸ j.2)
    -- 🎉 no goals
#align image_subtype_univ_ssubset_image_univ image_subtype_univ_ssubset_image_univ

/-- Any injection from a finset `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
theorem Finset.exists_equiv_extend_of_card_eq [Fintype α] [DecidableEq β] {t : Finset β}
    (hαt : Fintype.card α = t.card) {s : Finset α} {f : α → β} (hfst : Finset.image f s ⊆ t)
    (hfs : Set.InjOn f s) : ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i := by
  classical
    induction' s using Finset.induction with a s has H generalizing f
    · obtain ⟨e⟩ : Nonempty (α ≃ ↥t) := by rwa [← Fintype.card_eq, Fintype.card_coe]
      use e
      simp
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
#align finset.exists_equiv_extend_of_card_eq Finset.exists_equiv_extend_of_card_eq

/-- Any injection from a set `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
theorem Set.MapsTo.exists_equiv_extend_of_card_eq [Fintype α] {t : Finset β}
    (hαt : Fintype.card α = t.card) {s : Set α} {f : α → β} (hfst : s.MapsTo f t)
    (hfs : Set.InjOn f s) : ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i := by
  classical
    let s' : Finset α := s.toFinset
    have hfst' : s'.image f ⊆ t := by simpa [← Finset.coe_subset] using hfst
    have hfs' : Set.InjOn f s' := by simpa using hfs
    obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hαt hfst' hfs'
    refine' ⟨g, fun i hi => _⟩
    apply hg
    simpa using hi
#align set.maps_to.exists_equiv_extend_of_card_eq Set.MapsTo.exists_equiv_extend_of_card_eq

theorem Fintype.card_subtype_or (p q : α → Prop) [Fintype { x // p x }] [Fintype { x // q x }]
    [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } ≤ Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
    rw [Fintype.card_sum]
#align fintype.card_subtype_or Fintype.card_subtype_or

theorem Fintype.card_subtype_or_disjoint (p q : α → Prop) (h : Disjoint p q) [Fintype { x // p x }]
    [Fintype { x // q x }] [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } = Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert Fintype.card_congr (subtypeOrEquiv p q h)
    simp
#align fintype.card_subtype_or_disjoint Fintype.card_subtype_or_disjoint

section

open Classical

@[simp]
theorem infinite_sum : Infinite (Sum α β) ↔ Infinite α ∨ Infinite β := by
  refine' ⟨fun H => _, fun H => H.elim (@Sum.infinite_of_left α β) (@Sum.infinite_of_right α β)⟩
  -- ⊢ Infinite α ∨ Infinite β
  contrapose! H; haveI := fintypeOfNotInfinite H.1; haveI := fintypeOfNotInfinite H.2
  -- ⊢ ¬Infinite (α ⊕ β)
                 -- ⊢ ¬Infinite (α ⊕ β)
                                                    -- ⊢ ¬Infinite (α ⊕ β)
  exact Infinite.false
  -- 🎉 no goals
#align infinite_sum infinite_sum

end
