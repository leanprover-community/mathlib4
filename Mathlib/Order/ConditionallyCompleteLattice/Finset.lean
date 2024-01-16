/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Finite

#align_import order.conditionally_complete_lattice.finset from "leanprover-community/mathlib"@"2445c98ae4b87eabebdde552593519b9b6dc350c"

/-!
# Conditionally complete lattices and finite sets.

-/


open Set

variable {ι α β γ : Type*}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

theorem Finset.Nonempty.sup'_eq_cSup_image {s : Finset β} (hs : s.Nonempty) (f : β → α) :
    s.sup' hs f = sSup (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [csSup_le_iff (s.finite_toSet.image f).bddAbove (hs.to_set.image f)]
#align finset.nonempty.sup'_eq_cSup_image Finset.Nonempty.sup'_eq_cSup_image

theorem Finset.Nonempty.sup'_id_eq_cSup {s : Finset α} (hs : s.Nonempty) :
    s.sup' hs id = sSup s := by
  rw [hs.sup'_eq_cSup_image, Set.image_id]
#align finset.nonempty.sup'_id_eq_cSup Finset.Nonempty.sup'_id_eq_cSup

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

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α]

lemma Finset.sup_univ_eq_ciSup [Fintype ι] (f : ι → α) : univ.sup f = ⨆ i, f i :=
  le_antisymm
    (Finset.sup_le fun _ _ => le_ciSup (finite_range _).bddAbove _)
    (ciSup_le' fun _ => Finset.le_sup (mem_univ _))

end ConditionallyCompleteLinearOrderBot

/-!
### Relation between `Sup` / `Inf` and `Finset.sup'` / `Finset.inf'`

Like the `Sup` of a `ConditionallyCompleteLattice`, `Finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/


namespace Finset
variable {ι : Type*} [ConditionallyCompleteLattice α]

theorem sup'_eq_csSup_image (s : Finset ι) (H) (f : ι → α) : s.sup' H f = sSup (f '' s) := by
  apply le_antisymm
  · refine' Finset.sup'_le _ _ fun a ha => _
    refine' le_csSup ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩
    rintro i ⟨j, hj, rfl⟩
    exact Finset.le_sup' _ hj
  · apply csSup_le ((coe_nonempty.mpr H).image _)
    rintro _ ⟨a, ha, rfl⟩
    exact Finset.le_sup' _ ha
#align finset.sup'_eq_cSup_image Finset.sup'_eq_csSup_image

theorem inf'_eq_csInf_image (s : Finset ι) (hs) (f : ι → α) : s.inf' hs f = sInf (f '' s) :=
  sup'_eq_csSup_image (α := αᵒᵈ) _ hs _
#align finset.inf'_eq_cInf_image Finset.inf'_eq_csInf_image

theorem sup'_id_eq_csSup (s : Finset α) (hs) : s.sup' hs id = sSup s := by
  rw [sup'_eq_csSup_image s hs, Set.image_id]
#align finset.sup'_id_eq_cSup Finset.sup'_id_eq_csSup

theorem inf'_id_eq_csInf (s : Finset α) (hs) : s.inf' hs id = sInf s :=
  sup'_id_eq_csSup (α := αᵒᵈ) _ hs
#align finset.inf'_id_eq_cInf Finset.inf'_id_eq_csInf

variable [Fintype ι] [Nonempty ι]

lemma sup'_univ_eq_ciSup (f : ι → α) : univ.sup' univ_nonempty f = ⨆ i, f i := by
  simp [sup'_eq_csSup_image, iSup]

lemma inf'_univ_eq_ciInf (f : ι → α) : univ.inf' univ_nonempty f = ⨅ i, f i := by
  simp [inf'_eq_csInf_image, iInf]

end Finset
