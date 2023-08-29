/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Int.LeastGreatest

#align_import data.int.conditionally_complete_order from "leanprover-community/mathlib"@"1e05171a5e8cf18d98d9cf7b207540acb044acae"

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
    sSup := fun s =>
      if h : s.Nonempty ∧ BddAbove s then
        greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    sInf := fun s =>
      if h : s.Nonempty ∧ BddBelow s then
        leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    le_csSup := by
      intro s n hs hns
      -- ⊢ n ≤ sSup s
      have : s.Nonempty ∧ BddAbove s := ⟨⟨n, hns⟩, hs⟩
      -- ⊢ n ≤ sSup s
      -- Porting note: this was `rw [dif_pos this]`
      simp only [this, and_self, dite_true, ge_iff_le]
      -- ⊢ n ≤ ↑(greatestOfBdd (choose (_ : BddAbove s)) (_ : choose (_ : BddAbove s) ∈ …
      exact (greatestOfBdd _ _ _).2.2 n hns
      -- 🎉 no goals
    csSup_le := by
      intro s n hs hns
      -- ⊢ sSup s ≤ n
      have : s.Nonempty ∧ BddAbove s := ⟨hs, ⟨n, hns⟩⟩
      -- ⊢ sSup s ≤ n
      -- Porting note: this was `rw [dif_pos this]`
      simp only [this, and_self, dite_true, ge_iff_le]
      -- ⊢ ↑(greatestOfBdd (choose (_ : BddAbove s)) (_ : choose (_ : BddAbove s) ∈ upp …
      exact hns (greatestOfBdd _ (Classical.choose_spec this.2) _).2.1
      -- 🎉 no goals
    csInf_le := by
      intro s n hs hns
      -- ⊢ sInf s ≤ n
      have : s.Nonempty ∧ BddBelow s := ⟨⟨n, hns⟩, hs⟩
      -- ⊢ sInf s ≤ n
      -- Porting note: this was `rw [dif_pos this]`
      simp only [this, and_self, dite_true, ge_iff_le]
      -- ⊢ ↑(leastOfBdd (choose (_ : BddBelow s)) (_ : choose (_ : BddBelow s) ∈ lowerB …
      exact (leastOfBdd _ _ _).2.2 n hns
      -- 🎉 no goals
    le_csInf := by
      intro s n hs hns
      -- ⊢ n ≤ sInf s
      have : s.Nonempty ∧ BddBelow s := ⟨hs, ⟨n, hns⟩⟩
      -- ⊢ n ≤ sInf s
      -- Porting note: this was `rw [dif_pos this]`
      simp only [this, and_self, dite_true, ge_iff_le]
      -- ⊢ n ≤ ↑(leastOfBdd (choose (_ : BddBelow s)) (_ : choose (_ : BddBelow s) ∈ lo …
      exact hns (leastOfBdd _ (Classical.choose_spec this.2) _).2.1
      -- 🎉 no goals
    csSup_of_not_bddAbove := fun s hs ↦ by simp [hs]
                                           -- 🎉 no goals
    csInf_of_not_bddBelow := fun s hs ↦ by simp [hs] }
                                           -- 🎉 no goals

namespace Int

-- Porting note: mathlib3 proof uses `convert dif_pos _ using 1`
theorem csSup_eq_greatest_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : sSup s = greatestOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddAbove s := ⟨Hinh, b, Hb⟩
  -- ⊢ sSup s = ↑(greatestOfBdd b Hb Hinh)
  simp only [sSup, this, and_self, dite_true]
  -- ⊢ ↑(greatestOfBdd (choose (_ : BddAbove s)) (_ : choose (_ : BddAbove s) ∈ upp …
  convert (coe_greatestOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) Hinh).symm
  -- 🎉 no goals
#align int.cSup_eq_greatest_of_bdd Int.csSup_eq_greatest_of_bdd

@[simp]
theorem csSup_empty : sSup (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
              -- 🎉 no goals
#align int.cSup_empty Int.csSup_empty

theorem csSup_of_not_bdd_above {s : Set ℤ} (h : ¬BddAbove s) : sSup s = 0 :=
  dif_neg (by simp [h])
              -- 🎉 no goals
#align int.cSup_of_not_bdd_above Int.csSup_of_not_bdd_above

-- Porting note: mathlib3 proof uses `convert dif_pos _ using 1`
theorem csInf_eq_least_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : sInf s = leastOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddBelow s := ⟨Hinh, b, Hb⟩
  -- ⊢ sInf s = ↑(leastOfBdd b Hb Hinh)
  simp only [sInf, this, and_self, dite_true]
  -- ⊢ ↑(leastOfBdd (choose (_ : BddBelow s)) (_ : choose (_ : BddBelow s) ∈ lowerB …
  convert (coe_leastOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) Hinh).symm
  -- 🎉 no goals
#align int.cInf_eq_least_of_bdd Int.csInf_eq_least_of_bdd

@[simp]
theorem csInf_empty : sInf (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
              -- 🎉 no goals
#align int.cInf_empty Int.csInf_empty

theorem csInf_of_not_bdd_below {s : Set ℤ} (h : ¬BddBelow s) : sInf s = 0 :=
  dif_neg (by simp [h])
              -- 🎉 no goals
#align int.cInf_of_not_bdd_below Int.csInf_of_not_bdd_below

theorem csSup_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : sSup s ∈ s := by
  convert (greatestOfBdd _ (Classical.choose_spec h2) h1).2.1
  -- ⊢ sSup s = ↑(greatestOfBdd (choose h2) (_ : choose h2 ∈ upperBounds s) h1)
  exact dif_pos ⟨h1, h2⟩
  -- 🎉 no goals
#align int.cSup_mem Int.csSup_mem

theorem csInf_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : sInf s ∈ s := by
  convert (leastOfBdd _ (Classical.choose_spec h2) h1).2.1
  -- ⊢ sInf s = ↑(leastOfBdd (choose h2) (_ : choose h2 ∈ lowerBounds s) h1)
  exact dif_pos ⟨h1, h2⟩
  -- 🎉 no goals
#align int.cInf_mem Int.csInf_mem

end Int
