/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.int.conditionally_complete_order
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Int.LeastGreatest

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/


open Int

open Classical

noncomputable section

instance : ConditionallyCompleteLinearOrder ℤ :=
  { Int.linearOrderedCommRing,
    LinearOrder.toLattice with
    supₛ := fun s =>
      if h : s.Nonempty ∧ BddAbove s then
        greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    infₛ := fun s =>
      if h : s.Nonempty ∧ BddBelow s then
        leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    le_csupₛ := by
      intro s n hs hns
      have : s.Nonempty ∧ BddAbove s := ⟨⟨n, hns⟩, hs⟩
      -- Porting note: this was `rw [dif_pos this]`
      simp only [this, and_self, dite_true, ge_iff_le]
      exact (greatestOfBdd _ _ _).2.2 n hns
    csupₛ_le := by
      intro s n hs hns
      have : s.Nonempty ∧ BddAbove s := ⟨hs, ⟨n, hns⟩⟩
      -- Porting note: this was `rw [dif_pos this]`
      simp only [this, and_self, dite_true, ge_iff_le]
      exact hns (greatestOfBdd _ (Classical.choose_spec this.2) _).2.1
    cinfₛ_le := by
      intro s n hs hns
      have : s.Nonempty ∧ BddBelow s := ⟨⟨n, hns⟩, hs⟩
      -- Porting note: this was `rw [dif_pos this]`
      simp only [this, and_self, dite_true, ge_iff_le]
      exact (leastOfBdd _ _ _).2.2 n hns
    le_cinfₛ := by
      intro s n hs hns
      have : s.Nonempty ∧ BddBelow s := ⟨hs, ⟨n, hns⟩⟩
      -- Porting note: this was `rw [dif_pos this]`
      simp only [this, and_self, dite_true, ge_iff_le]
      exact hns (leastOfBdd _ (Classical.choose_spec this.2) _).2.1 }

namespace Int

-- Porting note: mathlib3 proof uses `convert dif_pos _ using 1`
theorem csupₛ_eq_greatest_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : supₛ s = greatestOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddAbove s := ⟨Hinh, b, Hb⟩
  simp only [supₛ, this, and_self, dite_true]
  convert (coe_greatestOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) Hinh).symm
#align int.cSup_eq_greatest_of_bdd Int.csupₛ_eq_greatest_of_bdd

@[simp]
theorem csupₛ_empty : supₛ (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
#align int.cSup_empty Int.csupₛ_empty

theorem csupₛ_of_not_bdd_above {s : Set ℤ} (h : ¬BddAbove s) : supₛ s = 0 :=
  dif_neg (by simp [h])
#align int.cSup_of_not_bdd_above Int.csupₛ_of_not_bdd_above

-- Porting note: mathlib3 proof uses `convert dif_pos _ using 1`
theorem cinfₛ_eq_least_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : infₛ s = leastOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddBelow s := ⟨Hinh, b, Hb⟩
  simp only [infₛ, this, and_self, dite_true]
  convert (coe_leastOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) Hinh).symm
#align int.cInf_eq_least_of_bdd Int.cinfₛ_eq_least_of_bdd

@[simp]
theorem cinfₛ_empty : infₛ (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
#align int.cInf_empty Int.cinfₛ_empty

theorem cinfₛ_of_not_bdd_below {s : Set ℤ} (h : ¬BddBelow s) : infₛ s = 0 :=
  dif_neg (by simp [h])
#align int.cInf_of_not_bdd_below Int.cinfₛ_of_not_bdd_below

theorem csupₛ_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : supₛ s ∈ s := by
  convert (greatestOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩
#align int.cSup_mem Int.csupₛ_mem

theorem cinfₛ_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : infₛ s ∈ s := by
  convert (leastOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩
#align int.cInf_mem Int.cinfₛ_mem

end Int
