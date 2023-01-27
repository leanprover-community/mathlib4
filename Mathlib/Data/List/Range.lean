/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison

! This file was ported from Lean 3 source module data.list.range
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Zip

/-!
# Ranges of naturals as lists

This file shows basic results about `list.iota`, `list.range`, `list.range'` (all defined in
`data.list.defs`) and defines `list.fin_range`.
`fin_range n` is the list of elements of `fin n`.
`iota n = [n, n - 1, ..., 1]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `list.Ico` instead.
-/


universe u

open Nat

namespace List

variable {α : Type u}

@[simp]
theorem length_range' : ∀ s n : ℕ, length (range' s n) = n
  | _, 0 => rfl
  | _, _ + 1 => congr_arg succ (length_range' _ _)
#align list.length_range' List.length_range'

@[simp]
theorem range'_eq_nil {s n : ℕ} : range' s n = [] ↔ n = 0 := by rw [← length_eq_zero, length_range']
#align list.range'_eq_nil List.range'_eq_nil

@[simp]
theorem mem_range' {m : ℕ} : ∀ {s n : ℕ}, m ∈ range' s n ↔ s ≤ m ∧ m < s + n
  | s, 0 => by
    simp only [range', find?, not_mem_nil, add_zero, false_iff, not_and, not_lt, imp_self]
  | s, n + 1 =>
    have : m = s → m < s + n + 1 := fun e => e ▸ lt_succ_of_le (Nat.le_add_right _ _)
    have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m := by
      simpa only [eq_comm] using (@Decidable.le_iff_eq_or_lt _ _ _ s m).symm
    mem_cons.trans <| by
      simp only [@mem_range' m (s + 1) n, or_and_left, or_iff_right_of_imp this, l,
        add_right_comm, add_eq, add_zero, and_congr_right_iff, add_assoc, or_iff_right_iff_imp]
      intro; exact this
#align list.mem_range' List.mem_range'

theorem map_add_range' (a) : ∀ s n : ℕ, map ((· + ·) a) (range' s n) = range' (a + s) n
  | _, 0 => rfl
  | s, n + 1 => congr_arg (cons _) (map_add_range' _ (s + 1) n)
#align list.map_add_range' List.map_add_range'

theorem map_sub_range' (a) :
    ∀ (s n : ℕ) (_ : a ≤ s), map (fun x => x - a) (range' s n) = range' (s - a) n
  | s, 0, _ => rfl
  | s, n + 1, h => by
    convert congr_arg (cons (s - a)) (map_sub_range' _ (s + 1) n (Nat.le_succ_of_le h))
    rw [Nat.succ_sub h]
    rfl
#align list.map_sub_range' List.map_sub_range'

theorem chain_succ_range' : ∀ s n : ℕ, Chain (fun a b => b = succ a) s (range' (s + 1) n)
  | _, 0 => Chain.nil
  | s, n + 1 => (chain_succ_range' (s + 1) n).cons rfl
#align list.chain_succ_range' List.chain_succ_range'

theorem chain_lt_range' (s n : ℕ) : Chain (· < ·) s (range' (s + 1) n) :=
  (chain_succ_range' s n).imp fun _ _ e => e.symm ▸ lt_succ_self _
#align list.chain_lt_range' List.chain_lt_range'

theorem pairwise_lt_range' : ∀ s n : ℕ, Pairwise (· < ·) (range' s n)
  | _, 0 => Pairwise.nil
  | s, n + 1 => chain_iff_pairwise.1 (chain_lt_range' s n)
#align list.pairwise_lt_range' List.pairwise_lt_range'

theorem nodup_range' (s n : ℕ) : Nodup (range' s n) :=
  (pairwise_lt_range' s n).imp _root_.ne_of_lt
#align list.nodup_range' List.nodup_range'

@[simp]
theorem range'_append : ∀ s m n : ℕ, range' s m ++ range' (s + m) n = range' s (n + m)
  | s, 0, n => rfl
  | s, m + 1, n =>
    show s :: (range' (s + 1) m ++ range' (s + m + 1) n) = s :: range' (s + 1) (n + m) by
      rw [add_right_comm, range'_append (s + 1) m n]
#align list.range'_append List.range'_append

theorem range'_sublist_right {s m n : ℕ} : range' s m <+ range' s n ↔ m ≤ n :=
  ⟨fun h => by simpa only [length_range'] using h.length_le, fun h => by
    rw [← tsub_add_cancel_of_le h, ← range'_append] ; apply sublist_append_left⟩
#align list.range'_sublist_right List.range'_sublist_right

theorem range'_subset_right {s m n : ℕ} : range' s m ⊆ range' s n ↔ m ≤ n :=
  ⟨fun h =>
    le_of_not_lt fun hn =>
      lt_irrefl (s + n) <|
        (mem_range'.1 <| h <| mem_range'.2 ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hn s⟩).2,
    fun h => (range'_sublist_right.2 h).subset⟩
#align list.range'_subset_right List.range'_subset_right

theorem get?_range' : ∀ (s) {m n : ℕ}, m < n → get? (range' s n) m = some (s + m)
  | s, 0, n + 1, _ => rfl
  | s, m + 1, n + 1, h =>
    (get?_range' (s + 1) (lt_of_add_lt_add_right h)).trans <| by rw [add_right_comm] ; rfl
#align list.nth_range' List.get?_range'

-- Porting note: new theorem
@[simp]
theorem get_range' {n m} (i) (H : i < (range' n m).length) : get (range' n m) ⟨i, H⟩ = n + i :=
  Option.some.inj <| by rw [← get?_eq_get _, get?_range' _ (by simpa using H)]

set_option linter.deprecated false in
@[simp]
theorem nth_le_range' {n m} (i) (H : i < (range' n m).length) : nthLe (range' n m) i H = n + i :=
  get_range' i H
#align list.nth_le_range' List.nth_le_range'

theorem range'_concat (s n : ℕ) : range' s (n + 1) = range' s n ++ [s + n] := by
  rw [add_comm n 1] ; exact (range'_append s n 1).symm
#align list.range'_concat List.range'_concat

#align list.range_core List.range.loop

theorem range_loop_range' : ∀ s n : ℕ, range.loop s (range' s n) = range' 0 (n + s)
  | 0, n => rfl
  | s + 1, n => by
    rw [show n + (s + 1) = n + 1 + s from add_right_comm n s 1] ;
      exact range_loop_range' s (n + 1)
#align list.range_core_range' List.range_loop_range'

theorem range_eq_range' (n : ℕ) : range n = range' 0 n :=
  (range_loop_range' n 0).trans <| by rw [zero_add]
#align list.range_eq_range' List.range_eq_range'

theorem range_succ_eq_map (n : ℕ) : range (n + 1) = 0 :: map succ (range n) := by
  rw [range_eq_range', range_eq_range', range', add_comm, ← map_add_range'] ; congr ;
    exact funext one_add
#align list.range_succ_eq_map List.range_succ_eq_map

theorem range'_eq_map_range (s n : ℕ) : range' s n = map ((· + ·) s) (range n) := by
  rw [range_eq_range', map_add_range'] ; rfl
#align list.range'_eq_map_range List.range'_eq_map_range

@[simp]
theorem length_range (n : ℕ) : length (range n) = n := by simp only [range_eq_range', length_range']
#align list.length_range List.length_range

@[simp]
theorem range_eq_nil {n : ℕ} : range n = [] ↔ n = 0 := by rw [← length_eq_zero, length_range]
#align list.range_eq_nil List.range_eq_nil

theorem pairwise_lt_range (n : ℕ) : Pairwise (· < ·) (range n) := by
  simp only [range_eq_range', pairwise_lt_range']
#align list.pairwise_lt_range List.pairwise_lt_range

theorem pairwise_le_range (n : ℕ) : Pairwise (· ≤ ·) (range n) :=
  Pairwise.imp (@le_of_lt ℕ _) (pairwise_lt_range _)
#align list.pairwise_le_range List.pairwise_le_range

theorem nodup_range (n : ℕ) : Nodup (range n) := by simp only [range_eq_range', nodup_range']
#align list.nodup_range List.nodup_range

theorem range_sublist {m n : ℕ} : range m <+ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_sublist_right]
#align list.range_sublist List.range_sublist

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_subset_right]
#align list.range_subset List.range_subset

@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range', Nat.zero_le, true_and_iff, zero_add]
#align list.mem_range List.mem_range

-- @[simp] -- Porting note: simp can prove this
theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
  mt mem_range.1 <| lt_irrefl _
#align list.not_mem_range_self List.not_mem_range_self

-- @[simp] -- Porting note: simp can prove this
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := by
  simp only [succ_pos', lt_add_iff_pos_right, mem_range]
#align list.self_mem_range_succ List.self_mem_range_succ

theorem nth_range {m n : ℕ} (h : m < n) : get? (range n) m = some m := by
  simp only [range_eq_range', get?_range' _ h, zero_add]
#align list.nth_range List.nth_range

theorem range_succ (n : ℕ) : range (succ n) = range n ++ [n] := by
  simp only [range_eq_range', range'_concat, zero_add]
#align list.range_succ List.range_succ

@[simp]
theorem range_zero : range 0 = [] :=
  rfl
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

theorem range_add (a : ℕ) : ∀ b, range (a + b) = range a ++ (range b).map fun x => a + x
  | 0 => by rw [add_zero, range_zero, map_nil, append_nil]
  | b + 1 => by
    rw [Nat.add_succ, range_succ, range_add a b, range_succ, map_append,
      map_singleton, append_assoc]
#align list.range_add List.range_add

theorem iota_eq_reverse_range' : ∀ n : ℕ, iota n = reverse (range' 1 n)
  | 0 => rfl
  | n + 1 => by
    simp only [iota, range'_concat, iota_eq_reverse_range' (n.add 0), reverse_append, add_comm]; rfl
#align list.iota_eq_reverse_range' List.iota_eq_reverse_range'

@[simp]
theorem length_iota (n : ℕ) : length (iota n) = n := by
  simp only [iota_eq_reverse_range', length_reverse, length_range']
#align list.length_iota List.length_iota

theorem pairwise_gt_iota (n : ℕ) : Pairwise (· > ·) (iota n) := by
  simpa only [iota_eq_reverse_range', pairwise_reverse] using pairwise_lt_range' 1 n
#align list.pairwise_gt_iota List.pairwise_gt_iota

theorem nodup_iota (n : ℕ) : Nodup (iota n) :=
  (pairwise_gt_iota n).imp _root_.ne_of_gt
#align list.nodup_iota List.nodup_iota

theorem mem_iota {m n : ℕ} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp only [iota_eq_reverse_range', mem_reverse, mem_range', add_comm, lt_succ_iff]
#align list.mem_iota List.mem_iota

theorem reverse_range' : ∀ s n : ℕ, reverse (range' s n) = map (fun i => s + n - 1 - i) (range n)
  | s, 0 => rfl
  | s, n + 1 => by
    rw [range'_concat, reverse_append, range_succ_eq_map]
    simp only [show s + (n + 1) - 1 = s + n from rfl, (· ∘ ·), fun a i =>
      show a - 1 - i = a - succ i from pred_sub _ _, reverse_singleton, map_cons, tsub_zero,
      cons_append, nil_append, eq_self_iff_true, true_and_iff, map_map, reverse_range' s n]
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

@[simp]
theorem enum_from_map_fst : ∀ (n) (l : List α), map Prod.fst (enumFrom n l) = range' n l.length
  | _, [] => rfl
  | _, _ :: _ => congr_arg (cons _) (enum_from_map_fst _ _)
#align list.enum_from_map_fst List.enum_from_map_fst

@[simp]
theorem enum_map_fst (l : List α) : map Prod.fst (enum l) = range l.length := by
  simp only [enum, enum_from_map_fst, range_eq_range']
#align list.enum_map_fst List.enum_map_fst

theorem enum_eq_zip_range (l : List α) : l.enum = (range l.length).zip l :=
  zip_of_prod (enum_map_fst _) (enum_map_snd _)
#align list.enum_eq_zip_range List.enum_eq_zip_range

@[simp]
theorem unzip_enum_eq_prod (l : List α) : l.enum.unzip = (range l.length, l) := by
  simp only [enum_eq_zip_range, unzip_zip, length_range]
#align list.unzip_enum_eq_prod List.unzip_enum_eq_prod

theorem enum_from_eq_zip_range' (l : List α) {n : ℕ} : l.enumFrom n = (range' n l.length).zip l :=
  zip_of_prod (enum_from_map_fst _ _) (enumFrom_map_snd _ _)
#align list.enum_from_eq_zip_range' List.enum_from_eq_zip_range'

@[simp]
theorem unzip_enum_from_eq_prod (l : List α) {n : ℕ} :
    (l.enumFrom n).unzip = (range' n l.length, l) := by
  simp only [enum_from_eq_zip_range', unzip_zip, length_range']
#align list.unzip_enum_from_eq_prod List.unzip_enum_from_eq_prod

-- Porting note: new theorem
@[simp]
theorem get_range {n} (i) (H : i < (range n).length) : get (range n) ⟨i, H⟩ = i :=
  Option.some.inj <| by rw [← get?_eq_get _, nth_range (by simpa using H)]

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

end List
