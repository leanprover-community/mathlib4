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

This file shows that the cardinality of a set is an upper-bound for its mex.

## Tags

minimum excluded value, smallest, infimum, complement
-/

public section

open Set

theorem Set.Finite.sInf_compl_le_ncard {s : Set ℕ} (hfin : s.Finite) : sInf sᶜ ≤ s.ncard := by
  rw [← ncard_Iio_nat <| sInf sᶜ]
  refine ncard_le_ncard ?_ hfin
  nth_rw 2 [← compl_compl s]
  apply Nat.notMem_of_lt_sInf

theorem Set.coe_sInf_compl_le_encard (s : Set ℕ) : sInf sᶜ ≤ s.encard := by
  rcases s.finite_or_infinite with hfin | hinf
  · grw [← ncard_le_encard]
    exact_mod_cast hfin.sInf_compl_le_ncard
  · rw [hinf.encard_eq]
    exact le_top

theorem Finset.sInf_coe_compl_le_card (s : Finset ℕ) : sInf sᶜ ≤ s.card := by
  grw [s.finite_toSet.sInf_compl_le_ncard, ncard_coe_finset s]

variable {α : Type*} [ConditionallyCompleteLinearOrderBot α]
variable [AddMonoidWithOne α] [AddLeftMono α] [ZeroLEOneClass α] [CharZero α]

theorem Set.Finite.csInf_coe_compl_le_coe_ncard' {s : Set α} (hfin : s.Finite) :
    sInf sᶜ ≤ (s.ncard : α) := by
  rw [← csSup_Iic (a := s.ncard)]
  grw [← Monotone.csSup_image_le_csSup Nat.mono_cast nonempty_Iic bddAbove_Iic]
  refine csInf_le_csSup_of_nonempty_inter' ?_ <| finite_Iic _ |>.image _ |>.bddAbove
  rw [← not_disjoint_iff_nonempty_inter, disjoint_compl_left_iff_subset.not]
  apply (ncard_le_ncard · hfin).mt
  rw [ncard_image_of_injective _ CharZero.cast_injective, ncard_Iic_nat]
  lia

theorem Finset.csInf_coe_compl_le_coe_card' (s : Finset α) : sInf sᶜ ≤ (s.card : α) := by
  grw [s.finite_toSet.csInf_coe_compl_le_coe_ncard', ncard_coe_finset s]
