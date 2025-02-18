/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/

import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Results using cardinal arithmetic

## Main results

- `exists_union_disjoint_ncard_eq_of_even`: Given a set `s` with an even cardinality, there exist
  disjoint sets `t` and `u` such that `t ∪ u = s` and `t.ncard = u.ncard`.
- `exists_union_disjoint_cardinal_eq_iff` is the same, except using cardinal notation.
-/

variable {α : Type*} {s : Set α}

namespace Set

open Cardinal

theorem exists_union_disjoint_cardinal_eq_of_infinite (h : s.Infinite) : ∃ (t u : Set α),
    t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  have := h.to_subtype
  obtain ⟨f⟩ : Nonempty (s ≃ s ⊕ s) := by
    rw [← Cardinal.eq, ← add_def, add_mk_eq_self]
  refine ⟨Subtype.val '' (f ⁻¹' (range .inl)), Subtype.val '' (f ⁻¹' (range .inr)), ?_, ?_, ?_⟩
  · simp [← image_union, ← preimage_union]
  · exact disjoint_image_of_injective Subtype.val_injective
      (isCompl_range_inl_range_inr.disjoint.preimage f)
  · simp [mk_image_eq Subtype.val_injective]

theorem exists_union_disjoint_cardinal_eq_of_even (he : Even s.ncard) : ∃ (t u : Set α),
    t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  obtain hs | hs := s.infinite_or_finite
  · exact exists_union_disjoint_cardinal_eq_of_infinite hs
  classical
  rw [ncard_eq_toFinset_card s hs] at he
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := Finset.exists_disjoint_union_of_even_card he
  use t.toSet, u.toSet
  simp [← Finset.coe_union, *]

theorem exists_union_disjoint_ncard_eq_of_even (he : Even s.ncard) : ∃ (t u : Set α),
    t ∪ u = s ∧ Disjoint t u ∧ t.ncard = u.ncard := by
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := exists_union_disjoint_cardinal_eq_of_even he
  exact ⟨t, u, hutu, hdtu, congrArg Cardinal.toNat hctu⟩

theorem exists_union_disjoint_cardinal_eq_iff (s : Set α) :
    Even (s.ncard) ↔ ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  use exists_union_disjoint_cardinal_eq_of_even
  rintro ⟨t, u, rfl, hdtu, hctu⟩
  obtain hfin | hnfin := (t ∪ u).finite_or_infinite
  · rw [finite_union] at hfin
    have hn : t.ncard = u.ncard := congrArg Cardinal.toNat hctu
    rw [ncard_union_eq hdtu hfin.1 hfin.2, hn]
    exact Even.add_self u.ncard
  · simp [hnfin.ncard]

end Set
