/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Data.Nat.Lattice
public import Mathlib.Order.Interval.Set.Nat

/-!
# Mex lemmas

The mex (minimum excluded value) of a set is the smallest value in its complement.
<https://en.wikipedia.org/wiki/Mex_(mathematics)>

This file shows that the cardinality of the set is an upper-bound of its mex.

## Tags

minimum excluded value, smallest, infimum, complement
-/

@[expose] public section

open Set

set_option backward.isDefEq.respectTransparency false in
theorem sInf_compl_le_ncard {s : Set ℕ} (hfin : s.Finite) : sInf sᶜ ≤ s.ncard := by
  rw [← csSup_Iic (a := s.ncard)]
  refine csInf_le_csSup_of_nonempty_inter' ?_ <| bddAbove_Iic
  rw [← not_disjoint_iff_nonempty_inter, disjoint_compl_left_iff_subset.not]
  intro h
  have := ncard_le_ncard h hfin
  rw [ncard_Iic_nat] at this
  lia

theorem coe_sInf_compl_le_encard (s : Set ℕ) : sInf sᶜ ≤ s.encard := by
  rcases s.finite_or_infinite with hfin | hinf
  · grw [← ncard_le_encard]
    exact_mod_cast sInf_compl_le_ncard hfin
  · rw [hinf.encard_eq]
    exact le_top

theorem sInf_coe_compl_le_card (s : Finset ℕ) : sInf sᶜ ≤ s.card := by
  grw [sInf_compl_le_ncard <| Finset.finite_toSet s, ncard_coe_finset s]

set_option backward.isDefEq.respectTransparency false in
theorem csInf_coe_compl_le_coe_card' {α : Type*} [ConditionallyCompleteLinearOrderBot α]
    [AddMonoidWithOne α] [AddLeftMono α] [ZeroLEOneClass α] [CharZero α] (s : Finset α) :
    sInf sᶜ ≤ (s.card : α) := by
  rw [← csSup_Iic (a := s.card)]
  grw [← Monotone.csSup_image_le_csSup Nat.mono_cast nonempty_Iic bddAbove_Iic]
  refine csInf_le_csSup_of_nonempty_inter' ?_ <| Set.finite_Iic _ |>.image _ |>.bddAbove
  rw [← not_disjoint_iff_nonempty_inter, disjoint_compl_left_iff_subset.not, ← Finset.coe_Iic]
  intro h
  norm_cast at h
  apply Finset.card_le_card at h
  rw [Finset.card_image_of_injective _ CharZero.cast_injective] at h
  rw [Nat.card_Iic] at h
  lia
