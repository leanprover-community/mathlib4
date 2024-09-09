/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Fintype.Units
import Mathlib.Data.ZMod.Basic

/-!
# Some facts about finite rings
-/


open Finset ZMod

variable {R : Type*} [Ring R] [Fintype R] [DecidableEq R]

lemma Finset.univ_of_card_le_two (h : Fintype.card R ≤ 2) :
    (univ : Finset R) = {0, 1} := by
  rcases subsingleton_or_nontrivial R
  · exact le_antisymm (fun a _ ↦ by simp [Subsingleton.elim a 0]) (Finset.subset_univ _)
  · refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
    convert h
    simp

lemma Finset.univ_of_card_le_three (h : Fintype.card R ≤ 3) :
    (univ : Finset R) = {0, 1, -1} := by
  refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
  rcases lt_or_eq_of_le h with h | h
  · apply card_le_card
    rw [Finset.univ_of_card_le_two (Nat.lt_succ_iff.1 h)]
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp
  · have : Nontrivial R := by
      refine Fintype.one_lt_card_iff_nontrivial.1 ?_
      rw [h]
      norm_num
    rw [card_univ, h, card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
    · rw [mem_singleton]
      intro H
      rw [← add_eq_zero_iff_eq_neg, one_add_one_eq_two] at H
      apply_fun (ringEquivOfPrime R Nat.prime_three h).symm at H
      simp only [map_ofNat, map_zero] at H
      replace H : ((2 : ℕ) : ZMod 3) = 0 := H
      rw [natCast_zmod_eq_zero_iff_dvd] at H
      norm_num at H
    · intro h
      simp only [mem_insert, mem_singleton, zero_eq_neg] at h
      rcases h with (h | h)
      · exact zero_ne_one h
      · exact zero_ne_one h.symm

open scoped Classical

theorem card_units_lt (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀] [Fintype M₀] :
    Fintype.card M₀ˣ < Fintype.card M₀ :=
  Fintype.card_lt_of_injective_of_not_mem Units.val Units.ext not_isUnit_zero
