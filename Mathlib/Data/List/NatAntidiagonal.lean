/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range

#align_import data.list.nat_antidiagonal from "leanprover-community/mathlib"@"7b78d1776212a91ecc94cf601f83bdcc46b04213"

/-!
# Antidiagonals in ℕ × ℕ as lists

This file defines the antidiagonals of ℕ × ℕ as lists: the `n`-th antidiagonal is the list of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

Files `Data.Multiset.NatAntidiagonal` and `Data.Finset.NatAntidiagonal` successively turn the
`List` definition we have here into `Multiset` and `Finset`.
-/


open List Function Nat

namespace List

namespace Nat

/-- The antidiagonal of a natural number `n` is the list of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal (n : ℕ) : List (ℕ × ℕ) :=
  (range (n + 1)).map fun i ↦ (i, n - i)
#align list.nat.antidiagonal List.Nat.antidiagonal

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp]
theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ x.1 + x.2 = n := by
  rw [antidiagonal, mem_map]; constructor
  -- ⊢ (∃ a, a ∈ range (n + 1) ∧ (a, n - a) = x) ↔ x.fst + x.snd = n
                              -- ⊢ (∃ a, a ∈ range (n + 1) ∧ (a, n - a) = x) → x.fst + x.snd = n
  · rintro ⟨i, hi, rfl⟩
    -- ⊢ (i, n - i).fst + (i, n - i).snd = n
    rw [mem_range, lt_succ_iff] at hi
    -- ⊢ (i, n - i).fst + (i, n - i).snd = n
    exact add_tsub_cancel_of_le hi
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ ∃ a, a ∈ range (x.fst + x.snd + 1) ∧ (a, x.fst + x.snd - a) = x
    refine' ⟨x.fst, _, _⟩
    -- ⊢ x.fst ∈ range (x.fst + x.snd + 1)
    · rw [mem_range, add_assoc, lt_add_iff_pos_right]
      -- ⊢ 0 < x.snd + 1
      exact zero_lt_succ _
      -- 🎉 no goals
    · exact Prod.ext rfl (by simp only [add_tsub_cancel_left])
      -- 🎉 no goals
#align list.nat.mem_antidiagonal List.Nat.mem_antidiagonal

/-- The length of the antidiagonal of `n` is `n + 1`. -/
@[simp]
theorem length_antidiagonal (n : ℕ) : (antidiagonal n).length = n + 1 := by
  rw [antidiagonal, length_map, length_range]
  -- 🎉 no goals
#align list.nat.length_antidiagonal List.Nat.length_antidiagonal

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
theorem antidiagonal_zero : antidiagonal 0 = [(0, 0)] :=
  rfl
#align list.nat.antidiagonal_zero List.Nat.antidiagonal_zero

/-- The antidiagonal of `n` does not contain duplicate entries. -/
theorem nodup_antidiagonal (n : ℕ) : Nodup (antidiagonal n) :=
  (nodup_range _).map ((@LeftInverse.injective ℕ (ℕ × ℕ) Prod.fst fun i ↦ (i, n - i)) fun _ ↦ rfl)
#align list.nat.nodup_antidiagonal List.Nat.nodup_antidiagonal

@[simp]
theorem antidiagonal_succ {n : ℕ} :
    antidiagonal (n + 1) = (0, n + 1) :: (antidiagonal n).map (Prod.map Nat.succ id) := by
  simp only [antidiagonal, range_succ_eq_map, map_cons, true_and_iff, Nat.add_succ_sub_one,
    add_zero, id.def, eq_self_iff_true, tsub_zero, map_map, Prod.map_mk]
  apply congr rfl (congr rfl _)
  -- ⊢ map ((fun i => (i, n + 1 - i)) ∘ succ ∘ succ) (range n) = map (Prod.map succ …
  ext; simp
  -- ⊢ a✝ ∈ get? (map ((fun i => (i, n + 1 - i)) ∘ succ ∘ succ) (range n)) n✝ ↔ a✝  …
       -- 🎉 no goals
#align list.nat.antidiagonal_succ List.Nat.antidiagonal_succ

theorem antidiagonal_succ' {n : ℕ} :
    antidiagonal (n + 1) = (antidiagonal n).map (Prod.map id Nat.succ) ++ [(n + 1, 0)] := by
  simp only [antidiagonal, range_succ, add_tsub_cancel_left, map_append, append_assoc, tsub_self,
    singleton_append, map_map, map]
  congr 1
  -- ⊢ map (fun i => (i, n + 1 - i)) (range n) = map (Prod.map id succ ∘ fun i => ( …
  apply map_congr
  -- ⊢ ∀ (x : ℕ), x ∈ range n → (x, n + 1 - x) = (Prod.map id succ ∘ fun i => (i, n …
  simp (config := { contextual := true }) [le_of_lt, Nat.succ_eq_add_one, Nat.sub_add_comm]
  -- 🎉 no goals
#align list.nat.antidiagonal_succ' List.Nat.antidiagonal_succ'

theorem antidiagonal_succ_succ' {n : ℕ} :
    antidiagonal (n + 2) =
      (0, n + 2) :: (antidiagonal n).map (Prod.map Nat.succ Nat.succ) ++ [(n + 2, 0)] := by
  rw [antidiagonal_succ']
  -- ⊢ map (Prod.map id succ) (antidiagonal (n + 1)) ++ [(n + 1 + 1, 0)] = (0, n +  …
  simp
  -- ⊢ map (Prod.map id succ ∘ Prod.map succ id) (antidiagonal n) = map (Prod.map s …
  ext
  -- ⊢ a✝ ∈ get? (map (Prod.map id succ ∘ Prod.map succ id) (antidiagonal n)) n✝ ↔  …
  simp
  -- 🎉 no goals
#align list.nat.antidiagonal_succ_succ' List.Nat.antidiagonal_succ_succ'

theorem map_swap_antidiagonal {n : ℕ} :
    (antidiagonal n).map Prod.swap = (antidiagonal n).reverse := by
  rw [antidiagonal, map_map, ← List.map_reverse, range_eq_range', reverse_range', ←
    range_eq_range', map_map]
  apply map_congr
  -- ⊢ ∀ (x : ℕ), x ∈ range (n + 1) → (Prod.swap ∘ fun i => (i, n - i)) x = ((fun i …
  simp (config := { contextual := true }) [Nat.sub_sub_self, lt_succ_iff]
  -- 🎉 no goals
#align list.nat.map_swap_antidiagonal List.Nat.map_swap_antidiagonal

end Nat

end List

