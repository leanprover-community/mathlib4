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

theorem zero_bot (n : ℕ) : Ico 0 n = range n := by rw [Ico, Nat.sub_zero, range_eq_range']
#align list.Ico.zero_bot List.Ico.zero_bot

@[simp]
theorem length (n m : ℕ) : length (Ico n m) = m - n := by
  dsimp [Ico]
  simp [length_range', autoParam]
#align list.Ico.length List.Ico.length

theorem pairwise_lt (n m : ℕ) : Pairwise (· < ·) (Ico n m) := by
  dsimp [Ico]
  simp [pairwise_lt_range', autoParam]
#align list.Ico.pairwise_lt List.Ico.pairwise_lt

theorem nodup (n m : ℕ) : Nodup (Ico n m) := by
  dsimp [Ico]
  simp [nodup_range', autoParam]
#align list.Ico.nodup List.Ico.nodup

@[simp]
theorem mem {n m l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m := by
  suffices n ≤ l ∧ l < n + (m - n) ↔ n ≤ l ∧ l < m by simp [Ico, this]
  rcases le_total n m with hnm | hmn
  · rw [Nat.add_sub_cancel' hnm]
  · rw [Nat.sub_eq_zero_iff_le.mpr hmn, Nat.add_zero]
    exact
      and_congr_right fun hnl =>
        Iff.intro (fun hln => (not_le_of_gt hln hnl).elim) fun hlm => lt_of_lt_of_le hlm hmn
#align list.Ico.mem List.Ico.mem

theorem eq_nil_of_le {n m : ℕ} (h : m ≤ n) : Ico n m = [] := by
  simp [Ico, Nat.sub_eq_zero_iff_le.mpr h]
#align list.Ico.eq_nil_of_le List.Ico.eq_nil_of_le

theorem map_add (n m k : ℕ) : (Ico n m).map (k + ·) = Ico (n + k) (m + k) := by
  rw [Ico, Ico, map_add_range', Nat.add_sub_add_right m k, Nat.add_comm n k]
#align list.Ico.map_add List.Ico.map_add

theorem map_sub (n m k : ℕ) (h₁ : k ≤ n) :
    ((Ico n m).map fun x => x - k) = Ico (n - k) (m - k) := by
  rw [Ico, Ico, Nat.sub_sub_sub_cancel_right h₁, map_sub_range' _ _ _ h₁]
#align list.Ico.map_sub List.Ico.map_sub

@[simp]
theorem self_empty {n : ℕ} : Ico n n = [] :=
  eq_nil_of_le (le_refl n)
#align list.Ico.self_empty List.Ico.self_empty

@[simp]
theorem eq_empty_iff {n m : ℕ} : Ico n m = [] ↔ m ≤ n :=
  Iff.intro (fun h => Nat.sub_eq_zero_iff_le.mp <| by rw [← length, h, List.length]) eq_nil_of_le
#align list.Ico.eq_empty_iff List.Ico.eq_empty_iff

theorem append_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    Ico n m ++ Ico m l = Ico n l := by
  dsimp only [Ico]
  convert range'_append n (m-n) (l-m) 1 using 2
  · rw [Nat.one_mul, Nat.add_sub_cancel' hnm]
  · rw [Nat.sub_add_sub_cancel hml hnm]
#align list.Ico.append_consecutive List.Ico.append_consecutive

@[simp]
theorem inter_consecutive (n m l : ℕ) : Ico n m ∩ Ico m l = [] := by
  apply eq_nil_iff_forall_not_mem.2
  intro a
  simp only [and_imp, not_and, not_lt, List.mem_inter_iff, List.Ico.mem]
  intro _ h₂ h₃
  exfalso
  exact not_lt_of_ge h₃ h₂
#align list.Ico.inter_consecutive List.Ico.inter_consecutive

@[simp]
theorem bagInter_consecutive (n m l : Nat) :
    @List.bagInter ℕ instBEqOfDecidableEq (Ico n m) (Ico m l) = [] :=
  (bagInter_nil_iff_inter_nil _ _).2 (by convert inter_consecutive n m l)
#align list.Ico.bag_inter_consecutive List.Ico.bagInter_consecutive

@[simp]
theorem succ_singleton {n : ℕ} : Ico n (n + 1) = [n] := by
  dsimp [Ico]
  simp [range', Nat.add_sub_cancel_left]
#align list.Ico.succ_singleton List.Ico.succ_singleton

theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = Ico n m ++ [m] := by
  rwa [← succ_singleton, append_consecutive]
  exact Nat.le_succ _
#align list.Ico.succ_top List.Ico.succ_top

theorem eq_cons {n m : ℕ} (h : n < m) : Ico n m = n :: Ico (n + 1) m := by
  rw [← append_consecutive (Nat.le_succ n) h, succ_singleton]
  rfl
#align list.Ico.eq_cons List.Ico.eq_cons

@[simp]
theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = [m - 1] := by
  dsimp [Ico]
  rw [Nat.sub_sub_self (succ_le_of_lt h)]
  simp [← Nat.one_eq_succ_zero]

#align list.Ico.pred_singleton List.Ico.pred_singleton

theorem chain'_succ (n m : ℕ) : Chain' (fun a b => b = succ a) (Ico n m) := by
  by_cases h : n < m
  · rw [eq_cons h]
    exact chain_succ_range' _ _ 1
  · rw [eq_nil_of_le (le_of_not_gt h)]
    trivial
#align list.Ico.chain'_succ List.Ico.chain'_succ

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem not_mem_top {n m : ℕ} : m ∉ Ico n m := by simp
#align list.Ico.not_mem_top List.Ico.not_mem_top

theorem filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) :
    ((Ico n m).filter fun x => x < l) = Ico n m :=
  filter_eq_self.2 fun k hk => by
    simp only [(lt_of_lt_of_le (mem.1 hk).2 hml), decide_True]
#align list.Ico.filter_lt_of_top_le List.Ico.filter_lt_of_top_le

theorem filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : ((Ico n m).filter fun x => x < l) = [] :=
  filter_eq_nil.2 fun k hk => by
     simp only [decide_eq_true_eq, not_lt]
     apply le_trans hln
     exact (mem.1 hk).1
#align list.Ico.filter_lt_of_le_bot List.Ico.filter_lt_of_le_bot

theorem filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) :
    ((Ico n m).filter fun x => x < l) = Ico n l := by
  rcases le_total n l with hnl | hln
  · rw [← append_consecutive hnl hlm, filter_append, filter_lt_of_top_le (le_refl l),
      filter_lt_of_le_bot (le_refl l), append_nil]
  · rw [eq_nil_of_le hln, filter_lt_of_le_bot hln]
#align list.Ico.filter_lt_of_ge List.Ico.filter_lt_of_ge

@[simp]
theorem filter_lt (n m l : ℕ) :
    ((Ico n m).filter fun x => x < l) = Ico n (min m l) := by
  rcases le_total m l with hml | hlm
  · rw [min_eq_left hml, filter_lt_of_top_le hml]
  · rw [min_eq_right hlm, filter_lt_of_ge hlm]
#align list.Ico.filter_lt List.Ico.filter_lt

theorem filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) :
    ((Ico n m).filter fun x => l ≤ x) = Ico n m :=
  filter_eq_self.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact le_trans hln (mem.1 hk).1
#align list.Ico.filter_le_of_le_bot List.Ico.filter_le_of_le_bot

theorem filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : ((Ico n m).filter fun x => l ≤ x) = [] :=
  filter_eq_nil.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact not_le_of_gt (lt_of_lt_of_le (mem.1 hk).2 hml)
#align list.Ico.filter_le_of_top_le List.Ico.filter_le_of_top_le

theorem filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) :
    ((Ico n m).filter fun x => l ≤ x) = Ico l m := by
  rcases le_total l m with hlm | hml
  · rw [← append_consecutive hnl hlm, filter_append, filter_le_of_top_le (le_refl l),
      filter_le_of_le_bot (le_refl l), nil_append]
  · rw [eq_nil_of_le hml, filter_le_of_top_le hml]
#align list.Ico.filter_le_of_le List.Ico.filter_le_of_le

@[simp]
theorem filter_le (n m l : ℕ) : ((Ico n m).filter fun x => l ≤ x) = Ico (max n l) m := by
  rcases le_total n l with hnl | hln
  · rw [max_eq_right hnl, filter_le_of_le hnl]
  · rw [max_eq_left hln, filter_le_of_le_bot hln]
#align list.Ico.filter_le List.Ico.filter_le

theorem filter_lt_of_succ_bot {n m : ℕ} (hnm : n < m) :
    ((Ico n m).filter fun x => x < n + 1) = [n] := by
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm
  simp [filter_lt n m (n + 1), r]
#align list.Ico.filter_lt_of_succ_bot List.Ico.filter_lt_of_succ_bot

@[simp]
theorem filter_le_of_bot {n m : ℕ} (hnm : n < m) : ((Ico n m).filter fun x => x ≤ n) = [n] := by
  rw [← filter_lt_of_succ_bot hnm]
  exact filter_congr' fun _ _ => by
    rw [decide_eq_true_eq, decide_eq_true_eq]
    exact Nat.lt_succ_iff.symm
#align list.Ico.filter_le_of_bot List.Ico.filter_le_of_bot

/-- For any natural numbers n, a, and b, one of the following holds:
1. n < a
2. n ≥ b
3. n ∈ Ico a b
-/
theorem trichotomy (n a b : ℕ) : n < a ∨ b ≤ n ∨ n ∈ Ico a b := by
  by_cases h₁ : n < a
  · left
    exact h₁
  · right
    by_cases h₂ : n ∈ Ico a b
    · right
      exact h₂
    · left
      simp only [Ico.mem, not_and, not_lt] at *
      exact h₂ h₁
#align list.Ico.trichotomy List.Ico.trichotomy

end Ico

end List
