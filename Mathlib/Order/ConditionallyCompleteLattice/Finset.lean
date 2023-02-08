/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.finset
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Finite

/-!
# Conditionally complete lattices and finite sets.

-/


open Set

variable {α β γ : Type _}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

theorem Finset.Nonempty.sup'_eq_cSup_image {s : Finset β} (hs : s.Nonempty) (f : β → α) :
    s.sup' hs f = supₛ (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [csupₛ_le_iff (s.finite_toSet.image f).bddAbove (hs.to_set.image f)]
#align finset.nonempty.sup'_eq_cSup_image Finset.Nonempty.sup'_eq_cSup_image

theorem Finset.Nonempty.sup'_id_eq_cSup {s : Finset α} (hs : s.Nonempty) : s.sup' hs id = supₛ s :=
  by rw [hs.sup'_eq_cSup_image, Set.image_id]
#align finset.nonempty.sup'_id_eq_cSup Finset.Nonempty.sup'_id_eq_cSup

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

theorem Finset.Nonempty.cSup_eq_max' {s : Finset α} (h : s.Nonempty) : supₛ ↑s = s.max' h :=
  eq_of_forall_ge_iff fun _ => (csupₛ_le_iff s.bddAbove h.to_set).trans (s.max'_le_iff h).symm
#align finset.nonempty.cSup_eq_max' Finset.Nonempty.cSup_eq_max'

theorem Finset.Nonempty.cInf_eq_min' {s : Finset α} (h : s.Nonempty) : infₛ ↑s = s.min' h :=
  @Finset.Nonempty.cSup_eq_max' αᵒᵈ _ s h
#align finset.nonempty.cInf_eq_min' Finset.Nonempty.cInf_eq_min'

theorem Finset.Nonempty.cSup_mem {s : Finset α} (h : s.Nonempty) : supₛ (s : Set α) ∈ s := by
  rw [h.cSup_eq_max']
  exact s.max'_mem _
#align finset.nonempty.cSup_mem Finset.Nonempty.cSup_mem

theorem Finset.Nonempty.cInf_mem {s : Finset α} (h : s.Nonempty) : infₛ (s : Set α) ∈ s :=
  @Finset.Nonempty.cSup_mem αᵒᵈ _ _ h
#align finset.nonempty.cInf_mem Finset.Nonempty.cInf_mem

theorem Set.Nonempty.cSup_mem (h : s.Nonempty) (hs : s.Finite) : supₛ s ∈ s := by
  lift s to Finset α using hs
  exact Finset.Nonempty.cSup_mem h
#align set.nonempty.cSup_mem Set.Nonempty.cSup_mem

theorem Set.Nonempty.cInf_mem (h : s.Nonempty) (hs : s.Finite) : infₛ s ∈ s :=
  @Set.Nonempty.cSup_mem αᵒᵈ _ _ h hs
#align set.nonempty.cInf_mem Set.Nonempty.cInf_mem

theorem Set.Finite.cSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : supₛ s < a ↔ ∀ x ∈ s, x < a :=
  ⟨fun h _ hx => (le_csupₛ hs.bddAbove hx).trans_lt h, fun H => H _ <| h.cSup_mem hs⟩
#align set.finite.cSup_lt_iff Set.Finite.cSup_lt_iff

theorem Set.Finite.lt_cInf_iff (hs : s.Finite) (h : s.Nonempty) : a < infₛ s ↔ ∀ x ∈ s, a < x :=
  @Set.Finite.cSup_lt_iff αᵒᵈ _ _ _ hs h
#align set.finite.lt_cInf_iff Set.Finite.lt_cInf_iff

end ConditionallyCompleteLinearOrder

/-!
### Relation between `Sup` / `Inf` and `Finset.sup'` / `Finset.inf'`

Like the `Sup` of a `ConditionallyCompleteLattice`, `Finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/


namespace Finset

theorem sup'_eq_csupₛ_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.sup' H f = supₛ (f '' s) := by
  apply le_antisymm
  · refine' Finset.sup'_le _ _ fun a ha => _
    refine' le_csupₛ ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩
    rintro i ⟨j, hj, rfl⟩
    exact Finset.le_sup' _ hj
  · apply csupₛ_le ((coe_nonempty.mpr H).image _)
    rintro _ ⟨a, ha, rfl⟩
    exact Finset.le_sup' _ ha
#align finset.sup'_eq_cSup_image Finset.sup'_eq_csupₛ_image

theorem inf'_eq_cinfₛ_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.inf' H f = infₛ (f '' s) :=
  @sup'_eq_csupₛ_image _ βᵒᵈ _ _ H _
#align finset.inf'_eq_cInf_image Finset.inf'_eq_cinfₛ_image

theorem sup'_id_eq_csupₛ [ConditionallyCompleteLattice α] (s : Finset α) (H) :
    s.sup' H id = supₛ s := by rw [sup'_eq_csupₛ_image s H, Set.image_id]
#align finset.sup'_id_eq_cSup Finset.sup'_id_eq_csupₛ

theorem inf'_id_eq_cinfₛ [ConditionallyCompleteLattice α] (s : Finset α) (H) :
    s.inf' H id = infₛ s :=
  @sup'_id_eq_csupₛ αᵒᵈ _ _ H
#align finset.inf'_id_eq_cInf Finset.inf'_id_eq_cinfₛ

end Finset
