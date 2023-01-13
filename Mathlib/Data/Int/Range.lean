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
  ((List.range (toNat (n - m))) : List ℕ).map fun (r : ℕ) => (m + r : ℤ)
#align int.range Int.range

theorem mem_range_iff {m n r : ℤ} : r ∈ range m n ↔ m ≤ r ∧ r < n := by
  simp only [range, List.mem_map', List.mem_range, lt_toNat, lt_sub_iff_add_lt, add_comm]
  exact ⟨fun ⟨a, ha⟩ => ha.2 ▸ ⟨le_add_of_nonneg_right (Int.coe_nat_nonneg _), ha.1⟩,
    fun h => ⟨toNat (r - m), by simp [toNat_of_nonneg (sub_nonneg.2 h.1), h.2] ⟩⟩

#align int.mem_range_iff Int.mem_range_iff

instance decidableLeLt (P : Int → Prop) [DecidablePred P] (m n : ℤ) :
    Decidable (∀ r, m ≤ r → r < n → P r) :=
  decidable_of_iff (∀ r ∈ range m n, P r) <| by simp only [mem_range_iff, and_imp]
#align int.decidable_le_lt Int.decidableLeLt

instance decidableLeLe (P : Int → Prop) [DecidablePred P] (m n : ℤ) :
    Decidable (∀ r, m ≤ r → r ≤ n → P r) := by
  -- Porting note: The previous code was:
  -- decidable_of_iff (∀ r ∈ range m (n + 1), P r) <| by
  --   simp only [mem_range_iff, and_imp, lt_add_one_iff]
  --
  -- This fails to synthesize an instance
  -- `Decidable (∀ (r : ℤ), r ∈ range m (n + 1) → P r)`
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
