/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.Range
import Mathlib.Data.Bool.Basic

#align_import data.list.intervals from "leanprover-community/mathlib"@"7b78d1776212a91ecc94cf601f83bdcc46b04213"
/-!
# Intervals in ℕ

This file defines intervals of naturals. `List.Ico m n` is the list of integers greater than `m`
and strictly less than `n`.

## TODO
- Define `Ioo` and `Icc`, state basic lemmas about them.
- Also do the versions for integers?
- One could generalise even further, defining 'locally finite partial orders', for which
  `Set.Ico a b` is `[Finite]`, and 'locally finite total orders', for which there is a list model.
- Once the above is done, get rid of `Data.Int.range` (and maybe `List.range'`?).
-/


open Nat

namespace List

/-- `Ico n m` is the list of natural numbers `n ≤ x < m`.
(Ico stands for "interval, closed-open".)

See also `Data/Set/Intervals.lean` for `Set.Ico`, modelling intervals in general preorders, and
`Multiset.Ico` and `Finset.Ico` for `n ≤ x < m` as a multiset or as a finset.
 -/
def Ico (n m : ℕ) : List ℕ :=
  range' n (m - n)
#align list.Ico List.Ico

namespace Ico

theorem zero_bot (n : ℕ) : Ico 0 n = range n := by rw [Ico, tsub_zero, range_eq_range']
                                                   -- 🎉 no goals
#align list.Ico.zero_bot List.Ico.zero_bot

@[simp]
theorem length (n m : ℕ) : length (Ico n m) = m - n := by
  dsimp [Ico]
  -- ⊢ List.length (range' n (m - n)) = m - n
  simp only [length_range']
  -- 🎉 no goals
#align list.Ico.length List.Ico.length

theorem pairwise_lt (n m : ℕ) : Pairwise (· < ·) (Ico n m) := by
  dsimp [Ico]
  -- ⊢ Pairwise (fun x x_1 => x < x_1) (range' n (m - n))
  simp only [pairwise_lt_range']
  -- 🎉 no goals
#align list.Ico.pairwise_lt List.Ico.pairwise_lt

theorem nodup (n m : ℕ) : Nodup (Ico n m) := by
  dsimp [Ico]
  -- ⊢ Nodup (range' n (m - n))
  simp only [nodup_range']
  -- 🎉 no goals
#align list.Ico.nodup List.Ico.nodup

@[simp]
theorem mem {n m l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m := by
  suffices n ≤ l ∧ l < n + (m - n) ↔ n ≤ l ∧ l < m by simp [Ico, this]
  -- ⊢ n ≤ l ∧ l < n + (m - n) ↔ n ≤ l ∧ l < m
  cases' le_total n m with hnm hmn
  -- ⊢ n ≤ l ∧ l < n + (m - n) ↔ n ≤ l ∧ l < m
  · rw [add_tsub_cancel_of_le hnm]
    -- 🎉 no goals
  · rw [tsub_eq_zero_iff_le.mpr hmn, add_zero]
    -- ⊢ n ≤ l ∧ l < n ↔ n ≤ l ∧ l < m
    exact
      and_congr_right fun hnl =>
        Iff.intro (fun hln => (not_le_of_gt hln hnl).elim) fun hlm => lt_of_lt_of_le hlm hmn
#align list.Ico.mem List.Ico.mem

theorem eq_nil_of_le {n m : ℕ} (h : m ≤ n) : Ico n m = [] := by
  simp [Ico, tsub_eq_zero_iff_le.mpr h]
  -- 🎉 no goals
#align list.Ico.eq_nil_of_le List.Ico.eq_nil_of_le

theorem map_add (n m k : ℕ) : (Ico n m).map ((· + ·) k) = Ico (n + k) (m + k) := by
  rw [Ico, Ico, map_add_range', add_tsub_add_eq_tsub_right m k, add_comm n k]
  -- 🎉 no goals
#align list.Ico.map_add List.Ico.map_add

theorem map_sub (n m k : ℕ) (h₁ : k ≤ n) :
    ((Ico n m).map fun x => x - k) = Ico (n - k) (m - k) := by
  rw [Ico, Ico, tsub_tsub_tsub_cancel_right h₁, map_sub_range' _ _ _ h₁]
  -- 🎉 no goals
#align list.Ico.map_sub List.Ico.map_sub

@[simp]
theorem self_empty {n : ℕ} : Ico n n = [] :=
  eq_nil_of_le (le_refl n)
#align list.Ico.self_empty List.Ico.self_empty

@[simp]
theorem eq_empty_iff {n m : ℕ} : Ico n m = [] ↔ m ≤ n :=
  Iff.intro (fun h => tsub_eq_zero_iff_le.mp <| by rw [← length, h, List.length]) eq_nil_of_le
                                                   -- 🎉 no goals
#align list.Ico.eq_empty_iff List.Ico.eq_empty_iff

theorem append_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    Ico n m ++ Ico m l = Ico n l := by
  dsimp only [Ico]
  -- ⊢ range' n (m - n) ++ range' m (l - m) = range' n (l - n)
  convert range'_append n (m-n) (l-m) 1 using 2
  -- ⊢ range' m (l - m) = range' (n + 1 * (m - n)) (l - m)
  · rw [one_mul, add_tsub_cancel_of_le hnm]
    -- 🎉 no goals
  · rw [tsub_add_tsub_cancel hml hnm]
    -- 🎉 no goals
#align list.Ico.append_consecutive List.Ico.append_consecutive

@[simp]
theorem inter_consecutive (n m l : ℕ) : Ico n m ∩ Ico m l = [] := by
  apply eq_nil_iff_forall_not_mem.2
  -- ⊢ ∀ (a : ℕ), ¬a ∈ Ico n m ∩ Ico m l
  intro a
  -- ⊢ ¬a ∈ Ico n m ∩ Ico m l
  simp only [and_imp, not_and, not_lt, List.mem_inter_iff, List.Ico.mem]
  -- ⊢ n ≤ a → a < m → m ≤ a → l ≤ a
  intro _ h₂ h₃
  -- ⊢ l ≤ a
  exfalso
  -- ⊢ False
  exact not_lt_of_ge h₃ h₂
  -- 🎉 no goals
#align list.Ico.inter_consecutive List.Ico.inter_consecutive

@[simp]
theorem bagInter_consecutive (n m l : Nat) :  @List.bagInter ℕ instBEq (Ico n m) (Ico m l) = [] :=
  (bagInter_nil_iff_inter_nil _ _).2 (inter_consecutive n m l)
#align list.Ico.bag_inter_consecutive List.Ico.bagInter_consecutive

@[simp]
theorem succ_singleton {n : ℕ} : Ico n (n + 1) = [n] := by
  dsimp [Ico]
  -- ⊢ range' n (n + 1 - n) = [n]
  simp [range', add_tsub_cancel_left]
  -- 🎉 no goals
#align list.Ico.succ_singleton List.Ico.succ_singleton

theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = Ico n m ++ [m] := by
  rwa [← succ_singleton, append_consecutive]
  -- ⊢ m ≤ m + 1
  exact Nat.le_succ _
  -- 🎉 no goals
#align list.Ico.succ_top List.Ico.succ_top

theorem eq_cons {n m : ℕ} (h : n < m) : Ico n m = n :: Ico (n + 1) m := by
  rw [← append_consecutive (Nat.le_succ n) h, succ_singleton]
  -- ⊢ [n] ++ Ico (succ n) m = n :: Ico (n + 1) m
  rfl
  -- 🎉 no goals
#align list.Ico.eq_cons List.Ico.eq_cons

@[simp]
theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = [m - 1] := by
  dsimp [Ico]
  -- ⊢ range' (m - 1) (m - (m - 1)) = [m - 1]
  rw [tsub_tsub_cancel_of_le (succ_le_of_lt h)]
  -- ⊢ range' (m - 1) (succ 0) = [m - 1]
  simp [← Nat.one_eq_succ_zero]
  -- 🎉 no goals

#align list.Ico.pred_singleton List.Ico.pred_singleton

theorem chain'_succ (n m : ℕ) : Chain' (fun a b => b = succ a) (Ico n m) := by
  by_cases n < m
  -- ⊢ Chain' (fun a b => b = succ a) (Ico n m)
  -- ⊢ Chain' (fun a b => b = succ a) (Ico n m)
  · rw [eq_cons h]
    -- ⊢ Chain' (fun a b => b = succ a) (n :: Ico (n + 1) m)
    exact chain_succ_range' _ _ 1
    -- 🎉 no goals
  · rw [eq_nil_of_le (le_of_not_gt h)]
    -- ⊢ Chain' (fun a b => b = succ a) []
    trivial
    -- 🎉 no goals
#align list.Ico.chain'_succ List.Ico.chain'_succ

-- Porting Note: simp can prove this
-- @[simp]
theorem not_mem_top {n m : ℕ} : m ∉ Ico n m := by simp
                                                  -- 🎉 no goals
#align list.Ico.not_mem_top List.Ico.not_mem_top

theorem filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) :
    ((Ico n m).filter fun x => x < l) = Ico n m :=
  filter_eq_self.2 fun k hk => by
    simp only [(lt_of_lt_of_le (mem.1 hk).2 hml), decide_True]
    -- 🎉 no goals
#align list.Ico.filter_lt_of_top_le List.Ico.filter_lt_of_top_le

theorem filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : ((Ico n m).filter fun x => x < l) = [] :=
  filter_eq_nil.2 fun k hk => by
     simp only [decide_eq_true_eq, not_lt]
     -- ⊢ l ≤ k
     apply le_trans hln
     -- ⊢ n ≤ k
     exact (mem.1 hk).1
     -- 🎉 no goals
#align list.Ico.filter_lt_of_le_bot List.Ico.filter_lt_of_le_bot

theorem filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) :
    ((Ico n m).filter fun x => x < l) = Ico n l := by
  cases' le_total n l with hnl hln
  -- ⊢ filter (fun x => decide (x < l)) (Ico n m) = Ico n l
  · rw [← append_consecutive hnl hlm, filter_append, filter_lt_of_top_le (le_refl l),
      filter_lt_of_le_bot (le_refl l), append_nil]
  · rw [eq_nil_of_le hln, filter_lt_of_le_bot hln]
    -- 🎉 no goals
#align list.Ico.filter_lt_of_ge List.Ico.filter_lt_of_ge

@[simp]
theorem filter_lt (n m l : ℕ) :
    ((Ico n m).filter fun x => x < l) = Ico n (min m l) := by
  cases' le_total m l with hml hlm
  -- ⊢ filter (fun x => decide (x < l)) (Ico n m) = Ico n (min m l)
  · rw [min_eq_left hml, filter_lt_of_top_le hml]
    -- 🎉 no goals
  · rw [min_eq_right hlm, filter_lt_of_ge hlm]
    -- 🎉 no goals
#align list.Ico.filter_lt List.Ico.filter_lt

theorem filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) :
    ((Ico n m).filter fun x => l ≤ x) = Ico n m :=
  filter_eq_self.2 fun k hk => by
    rw [decide_eq_true_eq]
    -- ⊢ l ≤ k
    exact le_trans hln (mem.1 hk).1
    -- 🎉 no goals
#align list.Ico.filter_le_of_le_bot List.Ico.filter_le_of_le_bot

theorem filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : ((Ico n m).filter fun x => l ≤ x) = [] :=
  filter_eq_nil.2 fun k hk => by
    rw [decide_eq_true_eq]
    -- ⊢ ¬l ≤ k
    exact not_le_of_gt (lt_of_lt_of_le (mem.1 hk).2 hml)
    -- 🎉 no goals
#align list.Ico.filter_le_of_top_le List.Ico.filter_le_of_top_le

theorem filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) :
    ((Ico n m).filter fun x => l ≤ x) = Ico l m := by
  cases' le_total l m with hlm hml
  -- ⊢ filter (fun x => decide (l ≤ x)) (Ico n m) = Ico l m
  · rw [← append_consecutive hnl hlm, filter_append, filter_le_of_top_le (le_refl l),
      filter_le_of_le_bot (le_refl l), nil_append]
  · rw [eq_nil_of_le hml, filter_le_of_top_le hml]
    -- 🎉 no goals
#align list.Ico.filter_le_of_le List.Ico.filter_le_of_le

@[simp]
theorem filter_le (n m l : ℕ) : ((Ico n m).filter fun x => l ≤ x) = Ico (max n l) m := by
  cases' le_total n l with hnl hln
  -- ⊢ filter (fun x => decide (l ≤ x)) (Ico n m) = Ico (max n l) m
  · rw [max_eq_right hnl, filter_le_of_le hnl]
    -- 🎉 no goals
  · rw [max_eq_left hln, filter_le_of_le_bot hln]
    -- 🎉 no goals
#align list.Ico.filter_le List.Ico.filter_le

theorem filter_lt_of_succ_bot {n m : ℕ} (hnm : n < m) :
    ((Ico n m).filter fun x => x < n + 1) = [n] := by
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm
  -- ⊢ filter (fun x => decide (x < n + 1)) (Ico n m) = [n]
  simp [filter_lt n m (n + 1), r]
  -- 🎉 no goals
#align list.Ico.filter_lt_of_succ_bot List.Ico.filter_lt_of_succ_bot

@[simp]
theorem filter_le_of_bot {n m : ℕ} (hnm : n < m) : ((Ico n m).filter fun x => x ≤ n) = [n] := by
  rw [← filter_lt_of_succ_bot hnm]
  -- ⊢ filter (fun x => decide (x ≤ n)) (Ico n m) = filter (fun x => decide (x < n  …
  exact filter_congr' fun _ _ => by
    rw [decide_eq_true_eq, decide_eq_true_eq]
    exact lt_succ_iff.symm
#align list.Ico.filter_le_of_bot List.Ico.filter_le_of_bot

/-- For any natural numbers n, a, and b, one of the following holds:
1. n < a
2. n ≥ b
3. n ∈ Ico a b
-/
theorem trichotomy (n a b : ℕ) : n < a ∨ b ≤ n ∨ n ∈ Ico a b := by
  by_cases h₁ : n < a
  -- ⊢ n < a ∨ b ≤ n ∨ n ∈ Ico a b
  · left
    -- ⊢ n < a
    exact h₁
    -- 🎉 no goals
  · right
    -- ⊢ b ≤ n ∨ n ∈ Ico a b
    by_cases h₂ : n ∈ Ico a b
    -- ⊢ b ≤ n ∨ n ∈ Ico a b
    · right
      -- ⊢ n ∈ Ico a b
      exact h₂
      -- 🎉 no goals
    · left
      -- ⊢ b ≤ n
      simp only [Ico.mem, not_and, not_lt] at *
      -- ⊢ b ≤ n
      exact h₂ h₁
      -- 🎉 no goals
#align list.Ico.trichotomy List.Ico.trichotomy

end Ico

end List
