/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison
-/
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Join
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Zip

#align_import data.list.range from "leanprover-community/mathlib"@"7b78d1776212a91ecc94cf601f83bdcc46b04213"

/-!
# Ranges of naturals as lists

This file shows basic results about `List.iota`, `List.range`, `List.range'`
and defines `List.finRange`.
`finRange n` is the list of elements of `Fin n`.
`iota n = [n, n - 1, ..., 1]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `List.Ico` instead.
-/

set_option autoImplicit true


universe u

open Nat

namespace List

variable {α : Type u}

@[simp] theorem range'_one {step} : range' s 1 step = [s] := rfl

#align list.length_range' List.length_range'
#align list.range'_eq_nil List.range'_eq_nil
#align list.mem_range' List.mem_range'_1
#align list.map_add_range' List.map_add_range'
#align list.map_sub_range' List.map_sub_range'
#align list.chain_succ_range' List.chain_succ_range'
#align list.chain_lt_range' List.chain_lt_range'

theorem pairwise_lt_range' : ∀ s n (step := 1) (_ : 0 < step := by simp),
  Pairwise (· < ·) (range' s n step)
  | _, 0, _, _ => Pairwise.nil
  | s, n + 1, _, h => chain_iff_pairwise.1 (chain_lt_range' s n h)
#align list.pairwise_lt_range' List.pairwise_lt_range'

theorem nodup_range' (s n : ℕ) (step := 1) (h : 0 < step := by simp) : Nodup (range' s n step) :=
  (pairwise_lt_range' s n step h).imp _root_.ne_of_lt
#align list.nodup_range' List.nodup_range'
#align list.range'_append List.range'_append
#align list.range'_sublist_right List.range'_sublist_right
#align list.range'_subset_right List.range'_subset_right
#align list.nth_range' List.get?_range'

set_option linter.deprecated false in
@[simp]
theorem nthLe_range' {n m step} (i) (H : i < (range' n m step).length) :
    nthLe (range' n m step) i H = n + step * i := get_range' i H

set_option linter.deprecated false in
theorem nthLe_range'_1 {n m} (i) (H : i < (range' n m).length) :
    nthLe (range' n m) i H = n + i := by simp
#align list.nth_le_range' List.nthLe_range'_1

#align list.range'_concat List.range'_concat
#align list.range_core List.range.loop
#align list.range_core_range' List.range_loop_range'
#align list.range_eq_range' List.range_eq_range'
#align list.range_succ_eq_map List.range_succ_eq_map
#align list.range'_eq_map_range List.range'_eq_map_range
#align list.length_range List.length_range
#align list.range_eq_nil List.range_eq_nil

theorem pairwise_lt_range (n : ℕ) : Pairwise (· < ·) (range n) := by
  simp (config := {decide := true}) only [range_eq_range', pairwise_lt_range']
#align list.pairwise_lt_range List.pairwise_lt_range

theorem pairwise_le_range (n : ℕ) : Pairwise (· ≤ ·) (range n) :=
  Pairwise.imp (@le_of_lt ℕ _) (pairwise_lt_range _)
#align list.pairwise_le_range List.pairwise_le_range

theorem nodup_range (n : ℕ) : Nodup (range n) := by
  simp (config := {decide := true}) only [range_eq_range', nodup_range']
#align list.nodup_range List.nodup_range
#align list.range_sublist List.range_sublist
#align list.range_subset List.range_subset
#align list.mem_range List.mem_range
#align list.not_mem_range_self List.not_mem_range_self
#align list.self_mem_range_succ List.self_mem_range_succ
#align list.nth_range List.get?_range
#align list.range_succ List.range_succ
#align list.range_zero List.range_zero

theorem chain'_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    Chain' r (range n.succ) ↔ ∀ m < n, r m m.succ := by
  rw [range_succ]
  induction' n with n hn
  · simp
  · rw [range_succ]
    simp only [append_assoc, singleton_append, chain'_append_cons_cons, chain'_singleton,
      and_true_iff]
    rw [hn, forall_lt_succ]
#align list.chain'_range_succ List.chain'_range_succ

theorem chain_range_succ (r : ℕ → ℕ → Prop) (n a : ℕ) :
    Chain r a (range n.succ) ↔ r a 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ_eq_map, chain_cons, and_congr_right_iff, ← chain'_range_succ, range_succ_eq_map]
  exact fun _ => Iff.rfl
#align list.chain_range_succ List.chain_range_succ

#align list.range_add List.range_add
#align list.iota_eq_reverse_range' List.iota_eq_reverse_range'
#align list.length_iota List.length_iota

theorem pairwise_gt_iota (n : ℕ) : Pairwise (· > ·) (iota n) := by
  simpa only [iota_eq_reverse_range', pairwise_reverse] using pairwise_lt_range' 1 n
#align list.pairwise_gt_iota List.pairwise_gt_iota

theorem nodup_iota (n : ℕ) : Nodup (iota n) :=
  (pairwise_gt_iota n).imp _root_.ne_of_gt
#align list.nodup_iota List.nodup_iota

#align list.mem_iota List.mem_iota
#align list.reverse_range' List.reverse_range'

/-- All elements of `Fin n`, from `0` to `n-1`. The corresponding finset is `Finset.univ`. -/
def finRange (n : ℕ) : List (Fin n) :=
  (range n).pmap Fin.mk fun _ => List.mem_range.1
#align list.fin_range List.finRange

@[simp]
theorem finRange_zero : finRange 0 = [] :=
  rfl
#align list.fin_range_zero List.finRange_zero

@[simp]
theorem mem_finRange {n : ℕ} (a : Fin n) : a ∈ finRange n :=
  mem_pmap.2
    ⟨a.1, mem_range.2 a.2, by
      cases a
      rfl⟩
#align list.mem_fin_range List.mem_finRange

theorem nodup_finRange (n : ℕ) : (finRange n).Nodup :=
  (Pairwise.pmap (nodup_range n) _) fun _ _ _ _ => @Fin.ne_of_vne _ ⟨_, _⟩ ⟨_, _⟩
#align list.nodup_fin_range List.nodup_finRange

@[simp]
theorem length_finRange (n : ℕ) : (finRange n).length = n := by
  rw [finRange, length_pmap, length_range]
#align list.length_fin_range List.length_finRange

@[simp]
theorem finRange_eq_nil {n : ℕ} : finRange n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_finRange]
#align list.fin_range_eq_nil List.finRange_eq_nil

theorem pairwise_lt_finRange (n : ℕ) : Pairwise (· < ·) (finRange n) :=
  (List.pairwise_lt_range n).pmap (by simp) (by simp)

theorem pairwise_le_finRange (n : ℕ) : Pairwise (· ≤ ·) (finRange n) :=
  (List.pairwise_le_range n).pmap (by simp) (by simp)

@[to_additive]
theorem prod_range_succ {α : Type u} [Monoid α] (f : ℕ → α) (n : ℕ) :
    ((range n.succ).map f).prod = ((range n).map f).prod * f n := by
  rw [range_succ, map_append, map_singleton, prod_append, prod_cons, prod_nil, mul_one]
#align list.prod_range_succ List.prod_range_succ
#align list.sum_range_succ List.sum_range_succ

/-- A variant of `prod_range_succ` which pulls off the first
  term in the product rather than the last.-/
@[to_additive
  "A variant of `sum_range_succ` which pulls off the first term in the sum rather than the last."]
theorem prod_range_succ' {α : Type u} [Monoid α] (f : ℕ → α) (n : ℕ) :
    ((range n.succ).map f).prod = f 0 * ((range n).map fun i => f (succ i)).prod :=
  Nat.recOn n (show 1 * f 0 = f 0 * 1 by rw [one_mul, mul_one]) fun _ hd => by
    rw [List.prod_range_succ, hd, mul_assoc, ← List.prod_range_succ]
#align list.prod_range_succ' List.prod_range_succ'
#align list.sum_range_succ' List.sum_range_succ'

#align list.enum_from_map_fst List.enumFrom_map_fst
#align list.enum_map_fst List.enum_map_fst

theorem enum_eq_zip_range (l : List α) : l.enum = (range l.length).zip l :=
  zip_of_prod (enum_map_fst _) (enum_map_snd _)
#align list.enum_eq_zip_range List.enum_eq_zip_range

@[simp]
theorem unzip_enum_eq_prod (l : List α) : l.enum.unzip = (range l.length, l) := by
  simp only [enum_eq_zip_range, unzip_zip, length_range]
#align list.unzip_enum_eq_prod List.unzip_enum_eq_prod

theorem enumFrom_eq_zip_range' (l : List α) {n : ℕ} : l.enumFrom n = (range' n l.length).zip l :=
  zip_of_prod (enumFrom_map_fst _ _) (enumFrom_map_snd _ _)
#align list.enum_from_eq_zip_range' List.enumFrom_eq_zip_range'

@[simp]
theorem unzip_enumFrom_eq_prod (l : List α) {n : ℕ} :
    (l.enumFrom n).unzip = (range' n l.length, l) := by
  simp only [enumFrom_eq_zip_range', unzip_zip, length_range']
#align list.unzip_enum_from_eq_prod List.unzip_enumFrom_eq_prod

set_option linter.deprecated false in
@[simp]
theorem nthLe_range {n} (i) (H : i < (range n).length) : nthLe (range n) i H = i :=
  get_range i H
#align list.nth_le_range List.nthLe_range

-- Porting note: new theorem
@[simp]
theorem get_finRange {n : ℕ} {i : ℕ} (h) :
    (finRange n).get ⟨i, h⟩ = ⟨i, length_finRange n ▸ h⟩ := by
  simp only [finRange, get_range, get_pmap]

--Porting note: new theorem, corresponding theorem used to be in Data.List.FinRange
@[simp]
theorem finRange_map_get (l : List α) : (finRange l.length).map l.get = l :=
  List.ext_get (by simp) (by simp)
#align list.map_nth_le List.finRange_map_get

set_option linter.deprecated false in
@[simp]
theorem nthLe_finRange {n : ℕ} {i : ℕ} (h) :
    (finRange n).nthLe i h = ⟨i, length_finRange n ▸ h⟩ :=
  get_finRange h
#align list.nth_le_fin_range List.nthLe_finRange

@[simp] theorem indexOf_finRange (i : Fin k) : (finRange k).indexOf i = i := by
  have : (finRange k).indexOf i < (finRange k).length := indexOf_lt_length.mpr (by simp)
  have h₁ : (finRange k).get ⟨(finRange k).indexOf i, this⟩ = i := indexOf_get this
  have h₂ : (finRange k).get ⟨i, by simp⟩ = i := get_finRange _
  simpa using (Nodup.get_inj_iff (nodup_finRange k)).mp (Eq.trans h₁ h₂.symm)

section Ranges

/-- From `l : List ℕ`, construct `l.ranges : List (List ℕ)` such that
  `l.ranges.map List.length = l` and `l.ranges.join = range l.sum`
* Example: `[1,2,3].ranges = [[0],[1,2],[3,4,5]]` -/
def ranges : List ℕ → List (List ℕ)
  | [] => nil
  | a::l => range a::(ranges l).map (map (Nat.add a))

/-- The members of `l.ranges` are pairwise disjoint -/
theorem ranges_disjoint (l : List ℕ) :
    Pairwise Disjoint (ranges l) := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rintro ⟨v, _, rfl⟩
      rw [mem_range] at hu
      exact lt_iff_not_le.mp hu le_self_add
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel
#align list.ranges_disjoint List.ranges_disjoint

/-- The lengths of the members of `l.ranges` are those given by `l` -/
theorem ranges_length (l : List ℕ) :
    l.ranges.map length = l := by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => -- (a :: l)
    simp only [map, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr
    intro s _
    simp only [Function.comp_apply, length_map]

theorem ranges_join (l : List ℕ) :
    l.ranges.join = range l.sum := by
  induction l with
  | nil => exact rfl
  | cons a l hl =>
    simp only [sum_cons, join]
    rw [← map_join, hl]
    rw [range_add]
    rfl

/-- Any entry of any member of `l.ranges` is strictly smaller than `l.sum` -/
theorem mem_mem_ranges_iff_lt_sum (l : List ℕ) {n : ℕ} :
    (∃ s ∈ List.ranges l,  n ∈ s) ↔ n < l.sum := by
  rw [← mem_range, ← ranges_join, mem_join]

 /-- The members of `l.ranges` have no duplicate -/
theorem ranges_nodup {l s : List ℕ} (hs : s ∈ ranges l) :
    s.Nodup := by
  refine (List.pairwise_join.mp ?_).1 s hs
  rw [ranges_join]
  exact nodup_range (sum l)

end Ranges

end List
