/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau

! This file was ported from Lean 3 source module data.int.range
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Range
import Mathlib.Data.Int.Order.Basic

/-!
# Intervals in ℤ

This file defines integer ranges. `range m n` is the set of integers greater than `m` and strictly
less than `n`.

## Note

This could be unified with `Data.List.Intervals`. See the TODOs there.
-/

-- Porting note: Many unfolds about `Lean.Internal.coeM`
namespace Int

/-- List enumerating `[m, n)`. This is the ℤ variant of `List.Ico`. -/
def range (m n : ℤ) : List ℤ :=
  (List.range (toNat (n - m))).map fun r => m + r
#align int.range Int.range

theorem mem_range_iff {m n r : ℤ} : r ∈ range m n ↔ m ≤ r ∧ r < n :=
  ⟨fun H =>
    let ⟨s, h1, h2⟩ := List.mem_map'.1 H
    h2 ▸
      -- Porting note: The previous code was:
      -- ⟨le_add_of_nonneg_right (ofNat_zero_le s),
      --
      -- This can't be used as `s` has type `ℤ`,
      -- while `ofNat_zero_le` requires `ℕ`.
      ⟨le_add_of_nonneg_right
        (by
          unfold Lean.Internal.coeM at h1
          simp at h1; let ⟨a, h⟩ := h1; rw [h.2]
          exact ofNat_zero_le _),
        add_lt_of_lt_sub_left <|
          match n - m, h1 with
          -- Porting note: The previous code was:
          -- | (k : ℕ), h1 => by rwa [List.range, toNat_coe_nat, ← ofNat_lt] at h1
          --
          -- Fails to rewrite `← ofNat_lt`.
          | (k : ℕ), h1 => by
            rw [toNat_coe_nat] at h1
            unfold Lean.Internal.coeM at h1
            simp at h1; let ⟨a, h2, h3⟩ := h1; rw [h3]
            unfold CoeT.coe instCoeT CoeHTCT.coe instCoeHTCTNat_1
            simpa⟩,
    fun ⟨h1, h2⟩ =>
    List.mem_map'.2
      ⟨toNat (r - m),
          -- Porting note: The previous code was:
          -- List.mem_range.2 <| by
          --   rw [← ofNat_lt, toNat_of_nonneg (sub_nonneg_of_le h1),
          --     toNat_of_nonneg (sub_nonneg_of_le (le_of_lt (lt_of_le_of_lt h1 h2)))] <;>
          --    exact sub_lt_sub_right h2 _,
          -- This gives a silly goal `r - m < r - m`, thus is removed.
          by
            unfold Lean.Internal.coeM
            simp; exists toNat (r - m)
            apply And.intro
            . simp only [sub_nonneg, toNat_of_nonneg, sub_lt_sub_iff_right, h1, h2]
            . simp only [sub_nonneg, toNat_of_nonneg, toNat_eq_max, h1, h2]
              unfold CoeT.coe instCoeT CoeHTCT.coe instCoeHTCTNat_1
              simp only [sub_nonneg, toNat_of_nonneg (sub_nonneg_of_le h1)],
          show m + _ = _ by rw [toNat_of_nonneg (sub_nonneg_of_le h1), add_sub_cancel'_right]⟩⟩
#align int.mem_range_iff Int.mem_range_iff

instance decidableLeLt (P : Int → Prop) [DecidablePred P] (m n : ℤ) :
    Decidable (∀ r, m ≤ r → r < n → P r) :=
  decidable_of_iff (∀ r ∈ range m n, P r) <| by simp only [mem_range_iff, and_imp]
#align int.decidable_le_lt Int.decidableLeLt

instance decidableLeLe (P : Int → Prop) [DecidablePred P] (m n : ℤ) :
    Decidable (∀ r, m ≤ r → r ≤ n → P r) :=
  -- Porting note: The previous code was:
  -- decidable_of_iff (∀ r ∈ range m (n + 1), P r) <| by
  --   simp only [mem_range_iff, and_imp, lt_add_one_iff]
  --
  -- This fails to synthesize an instance
  -- `Decidable (∀ (r : ℤ), r ∈ range m (n + 1) → P r)`
  by
    apply decidable_of_iff (∀ r ∈ range m (n + 1), P r)
    apply Iff.intro <;> intros h _ _
    . intro _; apply h
      simp_all only [mem_range_iff, and_imp, lt_add_one_iff]
    . simp_all only [mem_range_iff, and_imp, lt_add_one_iff]
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
