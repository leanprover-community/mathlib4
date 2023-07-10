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
    s.sup' hs f = sSup (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [csSup_le_iff (s.finite_toSet.image f).bddAbove (hs.to_set.image f)]
#align finset.nonempty.sup'_eq_cSup_image Finset.Nonempty.sup'_eq_cSup_image

theorem Finset.Nonempty.sup'_id_eq_cSup {s : Finset α} (hs : s.Nonempty) : s.sup' hs id = sSup s :=
  by rw [hs.sup'_eq_cSup_image, Set.image_id]
#align finset.nonempty.sup'_id_eq_cSup Finset.Nonempty.sup'_id_eq_cSup

variable {ι : Type _}

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. -/
theorem ciSup_eq_ciSup_finset_sup' [Nonempty ι] (s : ι → α) (bdd : BddAbove (Set.range s)) :
    ⨆ i, s i = ⨆ t : {t : Finset ι | t.Nonempty}, t.1.sup' t.2 s := by
  classical
    let ⟨B, hB⟩ := bdd
    rw [mem_upperBounds, forall_range_iff] at hB
    haveI : Nonempty {t : Finset ι | t.Nonempty} :=
      ⟨{Classical.arbitrary ι}, Finset.singleton_nonempty _⟩
    refine le_antisymm ?_ ?_
    · refine ciSup_le fun b ↦ le_ciSup_of_le ?_ ⟨{b}, Finset.singleton_nonempty _⟩ ?_
      · exact ⟨B, forall_range_iff.mpr fun ⟨t, ht⟩ ↦ Finset.sup'_le ht _ (fun b _ ↦ hB b)⟩
      exact Finset.le_sup' _ (Finset.mem_singleton_self b)
    · exact ciSup_le fun ⟨t, ht⟩ ↦ Finset.sup'_le _ _ fun b _ ↦ le_ciSup bdd b

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. See `ciSup_eq_ciSup_finset_sup'` for a version that does not assume `OrderBot`. -/
theorem ciSup_eq_ciSup_finset_sup [OrderBot α] (s : ι → α) (bdd : BddAbove (Set.range s)) :
    ⨆ i, s i = ⨆ t : Finset ι, t.sup s := by
  rw ciSup

#align supr_eq_supr_finset' iSup_eq_iSup_finset'

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type _`. See `iInf_eq_iInf_finset'` for a version
that works for `ι : Sort*`. -/
theorem iInf_eq_iInf_finset (s : ι → α) : ⨅ i, s i = ⨅ (t : Finset ι) (i ∈ t), s i :=
  @iSup_eq_iSup_finset αᵒᵈ _ _ _
#align infi_eq_infi_finset iInf_eq_iInf_finset

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `iInf_eq_iInf_finset` for a version
that assumes `ι : Type _` but has no `PLift`s. -/
theorem iInf_eq_iInf_finset' (s : ι' → α) :
    ⨅ i, s i = ⨅ t : Finset (PLift ι'), ⨅ i ∈ t, s (PLift.down i) :=
  @iSup_eq_iSup_finset' αᵒᵈ _ _ _
#align infi_eq_infi_finset' iInf_eq_iInf_finset'

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

theorem Finset.Nonempty.cSup_eq_max' {s : Finset α} (h : s.Nonempty) : sSup ↑s = s.max' h :=
  eq_of_forall_ge_iff fun _ => (csSup_le_iff s.bddAbove h.to_set).trans (s.max'_le_iff h).symm
#align finset.nonempty.cSup_eq_max' Finset.Nonempty.cSup_eq_max'

theorem Finset.Nonempty.cInf_eq_min' {s : Finset α} (h : s.Nonempty) : sInf ↑s = s.min' h :=
  @Finset.Nonempty.cSup_eq_max' αᵒᵈ _ s h
#align finset.nonempty.cInf_eq_min' Finset.Nonempty.cInf_eq_min'

theorem Finset.Nonempty.cSup_mem {s : Finset α} (h : s.Nonempty) : sSup (s : Set α) ∈ s := by
  rw [h.cSup_eq_max']
  exact s.max'_mem _
#align finset.nonempty.cSup_mem Finset.Nonempty.cSup_mem

theorem Finset.Nonempty.cInf_mem {s : Finset α} (h : s.Nonempty) : sInf (s : Set α) ∈ s :=
  @Finset.Nonempty.cSup_mem αᵒᵈ _ _ h
#align finset.nonempty.cInf_mem Finset.Nonempty.cInf_mem

theorem Set.Nonempty.cSup_mem (h : s.Nonempty) (hs : s.Finite) : sSup s ∈ s := by
  lift s to Finset α using hs
  exact Finset.Nonempty.cSup_mem h
#align set.nonempty.cSup_mem Set.Nonempty.cSup_mem

theorem Set.Nonempty.cInf_mem (h : s.Nonempty) (hs : s.Finite) : sInf s ∈ s :=
  @Set.Nonempty.cSup_mem αᵒᵈ _ _ h hs
#align set.nonempty.cInf_mem Set.Nonempty.cInf_mem

theorem Set.Finite.cSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : sSup s < a ↔ ∀ x ∈ s, x < a :=
  ⟨fun h _ hx => (le_csSup hs.bddAbove hx).trans_lt h, fun H => H _ <| h.cSup_mem hs⟩
#align set.finite.cSup_lt_iff Set.Finite.cSup_lt_iff

theorem Set.Finite.lt_cInf_iff (hs : s.Finite) (h : s.Nonempty) : a < sInf s ↔ ∀ x ∈ s, a < x :=
  @Set.Finite.cSup_lt_iff αᵒᵈ _ _ _ hs h
#align set.finite.lt_cInf_iff Set.Finite.lt_cInf_iff

end ConditionallyCompleteLinearOrder

/-!
### Relation between `Sup` / `Inf` and `Finset.sup'` / `Finset.inf'`

Like the `Sup` of a `ConditionallyCompleteLattice`, `Finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/


namespace Finset

theorem sup'_eq_csSup_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.sup' H f = sSup (f '' s) := by
  apply le_antisymm
  · refine' Finset.sup'_le _ _ fun a ha => _
    refine' le_csSup ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩
    rintro i ⟨j, hj, rfl⟩
    exact Finset.le_sup' _ hj
  · apply csSup_le ((coe_nonempty.mpr H).image _)
    rintro _ ⟨a, ha, rfl⟩
    exact Finset.le_sup' _ ha
#align finset.sup'_eq_cSup_image Finset.sup'_eq_csSup_image

theorem inf'_eq_csInf_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.inf' H f = sInf (f '' s) :=
  @sup'_eq_csSup_image _ βᵒᵈ _ _ H _
#align finset.inf'_eq_cInf_image Finset.inf'_eq_csInf_image

theorem sup'_id_eq_csSup [ConditionallyCompleteLattice α] (s : Finset α) (H) :
    s.sup' H id = sSup s := by rw [sup'_eq_csSup_image s H, Set.image_id]
#align finset.sup'_id_eq_cSup Finset.sup'_id_eq_csSup

theorem inf'_id_eq_csInf [ConditionallyCompleteLattice α] (s : Finset α) (H) :
    s.inf' H id = sInf s :=
  @sup'_id_eq_csSup αᵒᵈ _ _ H
#align finset.inf'_id_eq_cInf Finset.inf'_id_eq_csInf

/-!
### `OrderBot`/`OrderTop`
-/

variable {ι : Type _} {ι' : Sort _} [ConditionallyCompleteLattice α] [OrderBot α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type _`. See `iSup_eq_iSup_finset'` for a version
that works for `ι : Sort*`. -/
theorem ciSup_eq_ciSup_finset_sup' (s : ι → α) (bdd : BddAbove (Set.range s)) :
    ⨆ i, s i = ⨆ t : Finset ι, t.sup s := by
  classical

    refine le_antisymm ?_ ?_
    refine ciSup_le ?_
    exact ciSup_le fun b => le_ciSup_of_le {b} <| le_ciSup_of_le b <| le_ciSup_of_le (by simp) <| le_rfl
    exact ciSup_le fun t => iSup_le fun b => iSup_le fun _ => le_iSup _ _
#align supr_eq_supr_finset iSup_eq_iSup_finset

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `iSup_eq_iSup_finset` for a version
that assumes `ι : Type _` but has no `PLift`s. -/
theorem iSup_eq_iSup_finset' (s : ι' → α) :
    ⨆ i, s i = ⨆ t : Finset (PLift ι'), ⨆ i ∈ t, s (PLift.down i) := by
  rw [← iSup_eq_iSup_finset, ← Equiv.plift.surjective.iSup_comp]; rfl
#align supr_eq_supr_finset' iSup_eq_iSup_finset'

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type _`. See `iInf_eq_iInf_finset'` for a version
that works for `ι : Sort*`. -/
theorem iInf_eq_iInf_finset (s : ι → α) : ⨅ i, s i = ⨅ (t : Finset ι) (i ∈ t), s i :=
  @iSup_eq_iSup_finset αᵒᵈ _ _ _
#align infi_eq_infi_finset iInf_eq_iInf_finset

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `iInf_eq_iInf_finset` for a version
that assumes `ι : Type _` but has no `PLift`s. -/
theorem iInf_eq_iInf_finset' (s : ι' → α) :
    ⨅ i, s i = ⨅ t : Finset (PLift ι'), ⨅ i ∈ t, s (PLift.down i) :=
  @iSup_eq_iSup_finset' αᵒᵈ _ _ _
#align infi_eq_infi_finset' iInf_eq_iInf_finset'

end Finset
