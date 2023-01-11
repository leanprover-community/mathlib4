/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau

! This file was ported from Lean 3 source module data.int.range
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Range
import Mathbin.Data.Int.Order.Basic

/-!
# Intervals in ℤ

This file defines integer ranges. `range m n` is the set of integers greater than `m` and strictly
less than `n`.

## Note

This could be unified with `data.list.intervals`. See the TODOs there.
-/


namespace Int

/-- List enumerating `[m, n)`. This is the ℤ variant of `list.Ico`. -/
def range (m n : ℤ) : List ℤ :=
  (List.range (toNat (n - m))).map fun r => m + r
#align int.range Int.range

theorem mem_range_iff {m n r : ℤ} : r ∈ range m n ↔ m ≤ r ∧ r < n :=
  ⟨fun H =>
    let ⟨s, h1, h2⟩ := List.mem_map'.1 H
    h2 ▸
      ⟨le_add_of_nonneg_right (ofNat_zero_le s),
        add_lt_of_lt_sub_left <|
          match n - m, h1 with
          | (k : ℕ), h1 => by rwa [List.mem_range, to_nat_coe_nat, ← coe_nat_lt] at h1⟩,
    fun ⟨h1, h2⟩ =>
    List.mem_map'.2
      ⟨toNat (r - m),
        List.mem_range.2 <| by
          rw [← coe_nat_lt, to_nat_of_nonneg (sub_nonneg_of_le h1),
              to_nat_of_nonneg (sub_nonneg_of_le (le_of_lt (lt_of_le_of_lt h1 h2)))] <;>
            exact sub_lt_sub_right h2 _,
        show m + _ = _ by rw [to_nat_of_nonneg (sub_nonneg_of_le h1), add_sub_cancel'_right]⟩⟩
#align int.mem_range_iff Int.mem_range_iff

instance decidableLeLt (P : Int → Prop) [DecidablePred P] (m n : ℤ) :
    Decidable (∀ r, m ≤ r → r < n → P r) :=
  decidable_of_iff (∀ r ∈ range m n, P r) <| by simp only [mem_range_iff, and_imp]
#align int.decidable_le_lt Int.decidableLeLt

instance decidableLeLe (P : Int → Prop) [DecidablePred P] (m n : ℤ) :
    Decidable (∀ r, m ≤ r → r ≤ n → P r) :=
  decidable_of_iff (∀ r ∈ range m (n + 1), P r) <| by
    simp only [mem_range_iff, and_imp, lt_add_one_iff]
#align int.decidable_le_le Int.decidableLeLe

instance decidableLtLt (P : Int → Prop) [DecidablePred P] (m n : ℤ) :
    Decidable (∀ r, m < r → r < n → P r) :=
  Int.decidableLeLt P _ _
#align int.decidable_lt_lt Int.decidableLtLt

instance decidableLtLe (P : Int → Prop) [DecidablePred P] (m n : ℤ) :
    Decidable (∀ r, m < r → r ≤ n → P r) :=
  Int.decidableLeLe P _ _
#align int.decidable_lt_le Int.decidableLtLe

end Int

