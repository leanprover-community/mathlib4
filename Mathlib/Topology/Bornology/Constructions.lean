/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Topology.Bornology.Basic

#align_import topology.bornology.constructions from "leanprover-community/mathlib"@"e3d9ab8faa9dea8f78155c6c27d62a621f4c152d"

/-!
# Bornology structure on products and subtypes

In this file we define `Bornology` and `BoundedSpace` instances on `α × β`, `Π i, π i`, and
`{x // p x}`. We also prove basic lemmas about `Bornology.cobounded` and `Bornology.IsBounded`
on these types.
-/


open Set Filter Bornology Function

open Filter

variable {α β ι : Type*} {π : ι → Type*} [Bornology α] [Bornology β]
  [∀ i, Bornology (π i)]

instance Prod.instBornology : Bornology (α × β) where
  cobounded' := (cobounded α).coprod (cobounded β)
  le_cofinite' :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite
#align prod.bornology Prod.instBornology

instance Pi.instBornology : Bornology (∀ i, π i) where
  cobounded' := Filter.coprodᵢ fun i => cobounded (π i)
  le_cofinite' := iSup_le fun _ ↦ (comap_mono (Bornology.le_cofinite _)).trans (comap_cofinite_le _)
#align pi.bornology Pi.instBornology

/-- Inverse image of a bornology. -/
abbrev Bornology.induced {α β : Type*} [Bornology β] (f : α → β) : Bornology α where
  cobounded' := comap f (cobounded β)
  le_cofinite' := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)
#align bornology.induced Bornology.induced

instance {p : α → Prop} : Bornology (Subtype p) :=
  Bornology.induced (Subtype.val : Subtype p → α)

namespace Bornology

/-!
### Bounded sets in `α × β`
-/


theorem cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) :=
  rfl
#align bornology.cobounded_prod Bornology.cobounded_prod

theorem isBounded_image_fst_and_snd {s : Set (α × β)} :
    IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded s :=
  compl_mem_coprod.symm
#align bornology.is_bounded_image_fst_and_snd Bornology.isBounded_image_fst_and_snd

lemma IsBounded.image_fst {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.fst '' s) :=
  (isBounded_image_fst_and_snd.2 hs).1

lemma IsBounded.image_snd {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.snd '' s) :=
  (isBounded_image_fst_and_snd.2 hs).2

variable {s : Set α} {t : Set β} {S : ∀ i, Set (π i)}

theorem IsBounded.fst_of_prod (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty) : IsBounded s :=
  fst_image_prod s ht ▸ h.image_fst
#align bornology.is_bounded.fst_of_prod Bornology.IsBounded.fst_of_prod

theorem IsBounded.snd_of_prod (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty) : IsBounded t :=
  snd_image_prod hs t ▸ h.image_snd
#align bornology.is_bounded.snd_of_prod Bornology.IsBounded.snd_of_prod

theorem IsBounded.prod (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ˢ t) :=
  isBounded_image_fst_and_snd.1
    ⟨hs.subset <| fst_image_prod_subset _ _, ht.subset <| snd_image_prod_subset _ _⟩
#align bornology.is_bounded.prod Bornology.IsBounded.prod

theorem isBounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) :
    IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t :=
  ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩
#align bornology.is_bounded_prod_of_nonempty Bornology.isBounded_prod_of_nonempty

theorem isBounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or_iff]
#align bornology.is_bounded_prod Bornology.isBounded_prod

theorem isBounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  exact (isBounded_prod_of_nonempty (hs.prod hs)).trans and_self_iff
#align bornology.is_bounded_prod_self Bornology.isBounded_prod_self

/-!
### Bounded sets in `Π i, π i`
-/


theorem cobounded_pi : cobounded (∀ i, π i) = Filter.coprodᵢ fun i => cobounded (π i) :=
  rfl
#align bornology.cobounded_pi Bornology.cobounded_pi

theorem forall_isBounded_image_eval_iff {s : Set (∀ i, π i)} :
    (∀ i, IsBounded (eval i '' s)) ↔ IsBounded s :=
  compl_mem_coprodᵢ.symm
#align bornology.forall_is_bounded_image_eval_iff Bornology.forall_isBounded_image_eval_iff

lemma IsBounded.image_eval {s : Set (∀ i, π i)} (hs : IsBounded s) (i : ι) :
    IsBounded (eval i '' s) :=
  forall_isBounded_image_eval_iff.2 hs i

theorem IsBounded.pi (h : ∀ i, IsBounded (S i)) : IsBounded (pi univ S) :=
  forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset
#align bornology.is_bounded.pi Bornology.IsBounded.pi

theorem isBounded_pi_of_nonempty (hne : (pi univ S).Nonempty) :
    IsBounded (pi univ S) ↔ ∀ i, IsBounded (S i) :=
  ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_isBounded_image_eval_iff.2 H i, IsBounded.pi⟩
#align bornology.is_bounded_pi_of_nonempty Bornology.isBounded_pi_of_nonempty

theorem isBounded_pi : IsBounded (pi univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, IsBounded (S i) := by
  by_cases hne : ∃ i, S i = ∅
  · simp [hne, univ_pi_eq_empty_iff.2 hne]
  · simp only [hne, false_or_iff]
    simp only [not_exists, ← Ne.eq_def, ← nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne
    exact isBounded_pi_of_nonempty hne
#align bornology.is_bounded_pi Bornology.isBounded_pi

/-!
### Bounded sets in `{x // p x}`
-/


theorem isBounded_induced {α β : Type*} [Bornology β] {f : α → β} {s : Set α} :
    @IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s) :=
  compl_mem_comap
#align bornology.is_bounded_induced Bornology.isBounded_induced

theorem isBounded_image_subtype_val {p : α → Prop} {s : Set { x // p x }} :
    IsBounded (Subtype.val '' s) ↔ IsBounded s :=
  isBounded_induced.symm
#align bornology.is_bounded_image_subtype_coe Bornology.isBounded_image_subtype_val

end Bornology

/-!
### Bounded spaces
-/


open Bornology

instance [BoundedSpace α] [BoundedSpace β] : BoundedSpace (α × β) := by
  simp [← cobounded_eq_bot_iff, cobounded_prod]

instance [∀ i, BoundedSpace (π i)] : BoundedSpace (∀ i, π i) := by
  simp [← cobounded_eq_bot_iff, cobounded_pi]

theorem boundedSpace_induced_iff {α β : Type*} [Bornology β] {f : α → β} :
    @BoundedSpace α (Bornology.induced f) ↔ IsBounded (range f) := by
  rw [← @isBounded_univ _ (Bornology.induced f), isBounded_induced, image_univ]
-- Porting note: had to explicitly provided the bornology to `isBounded_univ`.
#align bounded_space_induced_iff boundedSpace_induced_iff

theorem boundedSpace_subtype_iff {p : α → Prop} :
    BoundedSpace (Subtype p) ↔ IsBounded { x | p x } := by
  rw [boundedSpace_induced_iff, Subtype.range_coe_subtype]
#align bounded_space_subtype_iff boundedSpace_subtype_iff

theorem boundedSpace_val_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s :=
  boundedSpace_subtype_iff
#align bounded_space_coe_set_iff boundedSpace_val_set_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_subtype⟩ := boundedSpace_subtype_iff
#align bornology.is_bounded.bounded_space_subtype Bornology.IsBounded.boundedSpace_subtype

alias ⟨_, Bornology.IsBounded.boundedSpace_val⟩ := boundedSpace_val_set_iff
#align bornology.is_bounded.bounded_space_coe Bornology.IsBounded.boundedSpace_val

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
