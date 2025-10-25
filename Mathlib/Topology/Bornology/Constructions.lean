/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Topology.Bornology.Basic

/-!
# Bornology structure on products and subtypes

In this file we define `Bornology` and `BoundedSpace` instances on `α × β`, `Π i, X i`, and
`{x // p x}`. We also prove basic lemmas about `Bornology.cobounded` and `Bornology.IsBounded`
on these types.
-/


open Set Filter Bornology Function

open Filter

variable {α β ι : Type*} {X : ι → Type*} [Bornology α] [Bornology β]
  [∀ i, Bornology (X i)]

instance Prod.instBornology : Bornology (α × β) where
  cobounded := (cobounded α).coprod (cobounded β)
  le_cofinite :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite

instance Pi.instBornology : Bornology (∀ i, X i) where
  cobounded := Filter.coprodᵢ fun i => cobounded (X i)
  le_cofinite := iSup_le fun _ ↦ (comap_mono (Bornology.le_cofinite _)).trans (comap_cofinite_le _)

/-- Inverse image of a bornology. -/
abbrev Bornology.induced {α β : Type*} [Bornology β] (f : α → β) : Bornology α where
  cobounded := comap f (cobounded β)
  le_cofinite := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)

instance {p : α → Prop} : Bornology (Subtype p) :=
  Bornology.induced (Subtype.val : Subtype p → α)

namespace Bornology

/-!
### Bounded sets in `α × β`
-/


theorem cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) :=
  rfl

theorem isBounded_image_fst_and_snd {s : Set (α × β)} :
    IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded s :=
  compl_mem_coprod.symm

lemma IsBounded.image_fst {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.fst '' s) :=
  (isBounded_image_fst_and_snd.2 hs).1

lemma IsBounded.image_snd {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.snd '' s) :=
  (isBounded_image_fst_and_snd.2 hs).2

variable {s : Set α} {t : Set β} {S : ∀ i, Set (X i)}

theorem IsBounded.fst_of_prod (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty) : IsBounded s :=
  fst_image_prod s ht ▸ h.image_fst

theorem IsBounded.snd_of_prod (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty) : IsBounded t :=
  snd_image_prod hs t ▸ h.image_snd

theorem IsBounded.prod (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ˢ t) :=
  isBounded_image_fst_and_snd.1
    ⟨hs.subset <| fst_image_prod_subset _ _, ht.subset <| snd_image_prod_subset _ _⟩

theorem isBounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) :
    IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t :=
  ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩

theorem isBounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or]

theorem isBounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  exact (isBounded_prod_of_nonempty (hs.prod hs)).trans and_self_iff

section tendsto

lemma _root_.Filter.Tendsto.cobounded_prod {γ : Type*} {f : α × β → γ} {l : Filter γ}
    (h₁ : ∀ s : Set α, IsBounded s → Tendsto f (𝓟 s ×ˢ cobounded β) l)
    (h₂ : Tendsto f (cobounded α ×ˢ ⊤) l) :
    Tendsto f (cobounded (α × β)) l := by
  intro s hs
  rw [mem_map, ← isCobounded_def, ← isBounded_compl_iff, ← preimage_compl]
  specialize h₂ hs
  rw [mem_map, mem_prod_top] at h₂
  set t := {a | ∀ (b : β), (a, b) ∈ f ⁻¹' s}
  have ht : t ×ˢ univ ⊆ f ⁻¹' s := by grind
  specialize h₁ tᶜ (IsCobounded.compl h₂) hs
  rw [mem_map, mem_prod_iff] at h₁
  obtain ⟨t₁, ht₁, t₂, ht₂, H⟩ := h₁
  rw [mem_principal, compl_subset_comm] at ht₁
  rw [← compl_subset_compl, ← preimage_compl, compl_prod_eq_union] at H ht
  simp only [compl_univ, prod_empty, union_empty] at ht
  have := subset_inter H ht
  rw [union_inter_distrib_right, prod_inter_prod, prod_inter_prod] at this
  have ht₁t : t₁ᶜ ∩ tᶜ = ∅ := (disjoint_compl_left_iff_subset.mpr ht₁).symm.inter_eq
  simp only [ht₁t, inter_self, empty_prod, univ_inter, inter_univ, empty_union] at this
  exact IsCobounded.compl h₂ |>.prod (IsCobounded.compl ht₂) |>.subset this

end tendsto

/-!
### Bounded sets in `Π i, X i`
-/


theorem cobounded_pi : cobounded (∀ i, X i) = Filter.coprodᵢ fun i => cobounded (X i) :=
  rfl

theorem forall_isBounded_image_eval_iff {s : Set (∀ i, X i)} :
    (∀ i, IsBounded (eval i '' s)) ↔ IsBounded s :=
  compl_mem_coprodᵢ.symm

lemma IsBounded.image_eval {s : Set (∀ i, X i)} (hs : IsBounded s) (i : ι) :
    IsBounded (eval i '' s) :=
  forall_isBounded_image_eval_iff.2 hs i

theorem IsBounded.pi (h : ∀ i, IsBounded (S i)) : IsBounded (pi univ S) :=
  forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset

theorem isBounded_pi_of_nonempty (hne : (pi univ S).Nonempty) :
    IsBounded (pi univ S) ↔ ∀ i, IsBounded (S i) :=
  ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_isBounded_image_eval_iff.2 H i, IsBounded.pi⟩

theorem isBounded_pi : IsBounded (pi univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, IsBounded (S i) := by
  by_cases hne : ∃ i, S i = ∅
  · simp [hne, univ_pi_eq_empty_iff.2 hne]
  · simp only [hne, false_or]
    simp only [not_exists, ← nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne
    exact isBounded_pi_of_nonempty hne

/-!
### Bounded sets in `{x // p x}`
-/


theorem isBounded_induced {α β : Type*} [Bornology β] {f : α → β} {s : Set α} :
    @IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s) :=
  compl_mem_comap

theorem isBounded_image_subtype_val {p : α → Prop} {s : Set { x // p x }} :
    IsBounded (Subtype.val '' s) ↔ IsBounded s :=
  isBounded_induced.symm

end Bornology

/-!
### Bounded spaces
-/


open Bornology

instance [BoundedSpace α] [BoundedSpace β] : BoundedSpace (α × β) := by
  simp [← cobounded_eq_bot_iff, cobounded_prod]

instance [∀ i, BoundedSpace (X i)] : BoundedSpace (∀ i, X i) := by
  simp [← cobounded_eq_bot_iff, cobounded_pi]

theorem boundedSpace_induced_iff {α β : Type*} [Bornology β] {f : α → β} :
    @BoundedSpace α (Bornology.induced f) ↔ IsBounded (range f) := by
  rw [← @isBounded_univ, isBounded_induced, image_univ]

theorem boundedSpace_subtype_iff {p : α → Prop} :
    BoundedSpace (Subtype p) ↔ IsBounded { x | p x } := by
  rw [boundedSpace_induced_iff, Subtype.range_coe_subtype]

theorem boundedSpace_val_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s :=
  boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_subtype⟩ := boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_val⟩ := boundedSpace_val_set_iff

instance [BoundedSpace α] {p : α → Prop} : BoundedSpace (Subtype p) :=
  (IsBounded.all { x | p x }).boundedSpace_subtype

/-!
### `Additive`, `Multiplicative`

The bornology on those type synonyms is inherited without change.
-/


instance : Bornology (Additive α) :=
  ‹Bornology α›

instance : Bornology (Multiplicative α) :=
  ‹Bornology α›

instance [BoundedSpace α] : BoundedSpace (Additive α) :=
  ‹BoundedSpace α›

instance [BoundedSpace α] : BoundedSpace (Multiplicative α) :=
  ‹BoundedSpace α›

/-!
### Order dual

The bornology on this type synonym is inherited without change.
-/


instance : Bornology αᵒᵈ :=
  ‹Bornology α›

instance [BoundedSpace α] : BoundedSpace αᵒᵈ :=
  ‹BoundedSpace α›
