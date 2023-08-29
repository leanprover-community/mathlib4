/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Lattice

#align_import data.finset.pairwise from "leanprover-community/mathlib"@"c4c2ed622f43768eff32608d4a0f8a6cec1c047d"

/-!
# Relations holding pairwise on finite sets

In this file we prove a few results about the interaction of `Set.PairwiseDisjoint` and `Finset`,
as well as the interaction of `List.Pairwise Disjoint` and the condition of
`Disjoint` on `List.toFinset`, in `Set` form.
-/


open Finset

variable {α ι ι' : Type*}

instance [DecidableEq α] {r : α → α → Prop} [DecidableRel r] {s : Finset α} :
    Decidable ((s : Set α).Pairwise r) :=
  decidable_of_iff' (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) Iff.rfl

theorem Finset.pairwiseDisjoint_range_singleton :
    (Set.range (singleton : α → Finset α)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  -- ⊢ (Disjoint on id) {a} {b}
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)
  -- 🎉 no goals
#align finset.pairwise_disjoint_range_singleton Finset.pairwiseDisjoint_range_singleton

namespace Set

theorem PairwiseDisjoint.elim_finset {s : Set ι} {f : ι → Finset α} (hs : s.PairwiseDisjoint f)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)
#align set.pairwise_disjoint.elim_finset Set.PairwiseDisjoint.elim_finset

section SemilatticeInf

variable [SemilatticeInf α] [OrderBot α] {s : Finset ι} {f : ι → α}

theorem PairwiseDisjoint.image_finset_of_le [DecidableEq ι] {s : Finset ι} {f : ι → α}
    (hs : (s : Set ι).PairwiseDisjoint f) {g : ι → ι} (hf : ∀ a, f (g a) ≤ f a) :
    (s.image g : Set ι).PairwiseDisjoint f := by
  rw [coe_image]
  -- ⊢ PairwiseDisjoint (g '' ↑s) f
  exact hs.image_of_le hf
  -- 🎉 no goals
#align set.pairwise_disjoint.image_finset_of_le Set.PairwiseDisjoint.image_finset_of_le

theorem PairwiseDisjoint.attach (hs : (s : Set ι).PairwiseDisjoint f) :
    (s.attach : Set { x // x ∈ s }).PairwiseDisjoint (f ∘ Subtype.val) := fun i _ j _ hij =>
  hs i.2 j.2 <| mt Subtype.ext_val hij
#align set.pairwise_disjoint.attach Set.PairwiseDisjoint.attach

end SemilatticeInf

variable [Lattice α] [OrderBot α]

/-- Bind operation for `Set.PairwiseDisjoint`. In a complete lattice, you can use
`Set.PairwiseDisjoint.biUnion`. -/
theorem PairwiseDisjoint.biUnion_finset {s : Set ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => (g i').sup f)
    (hg : ∀ i ∈ s, (g i : Set ι).PairwiseDisjoint f) : (⋃ i ∈ s, ↑(g i)).PairwiseDisjoint f := by
  rintro a ha b hb hab
  -- ⊢ (Disjoint on f) a b
  simp_rw [Set.mem_iUnion] at ha hb
  -- ⊢ (Disjoint on f) a b
  obtain ⟨c, hc, ha⟩ := ha
  -- ⊢ (Disjoint on f) a b
  obtain ⟨d, hd, hb⟩ := hb
  -- ⊢ (Disjoint on f) a b
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  -- ⊢ (Disjoint on f) a b
  · exact hg d hd (by rwa [hcd] at ha) hb hab
    -- 🎉 no goals
  · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (Finset.le_sup ha) (Finset.le_sup hb)
    -- 🎉 no goals
#align set.pairwise_disjoint.bUnion_finset Set.PairwiseDisjoint.biUnion_finset

end Set

namespace List

variable {β : Type*} [DecidableEq α] {r : α → α → Prop} {l : List α}

theorem pairwise_of_coe_toFinset_pairwise (hl : (l.toFinset : Set α).Pairwise r) (hn : l.Nodup) :
    l.Pairwise r := by
  rw [coe_toFinset] at hl
  -- ⊢ Pairwise r l
  exact hn.pairwise_of_set_pairwise hl
  -- 🎉 no goals
#align list.pairwise_of_coe_to_finset_pairwise List.pairwise_of_coe_toFinset_pairwise

theorem pairwise_iff_coe_toFinset_pairwise (hn : l.Nodup) (hs : Symmetric r) :
    (l.toFinset : Set α).Pairwise r ↔ l.Pairwise r := by
  letI : IsSymm α r := ⟨hs⟩
  -- ⊢ Set.Pairwise (↑(toFinset l)) r ↔ Pairwise r l
  rw [coe_toFinset, hn.pairwise_coe]
  -- 🎉 no goals
#align list.pairwise_iff_coe_to_finset_pairwise List.pairwise_iff_coe_toFinset_pairwise

theorem pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint {α ι} [SemilatticeInf α] [OrderBot α]
    [DecidableEq ι] {l : List ι} {f : ι → α} (hl : (l.toFinset : Set ι).PairwiseDisjoint f)
    (hn : l.Nodup) : l.Pairwise (_root_.Disjoint on f) :=
  pairwise_of_coe_toFinset_pairwise hl hn
#align list.pairwise_disjoint_of_coe_to_finset_pairwise_disjoint List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint

theorem pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint {α ι} [SemilatticeInf α] [OrderBot α]
    [DecidableEq ι] {l : List ι} {f : ι → α} (hn : l.Nodup) :
    (l.toFinset : Set ι).PairwiseDisjoint f ↔ l.Pairwise (_root_.Disjoint on f) :=
  pairwise_iff_coe_toFinset_pairwise hn (symmetric_disjoint.comap f)
#align list.pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint

end List
