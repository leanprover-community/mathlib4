/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module data.list.cycle
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Sort
import Mathbin.Data.Fintype.List
import Mathbin.Data.List.Rotate

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `is_rotated`.

Based on this, we define the quotient of lists by the rotation relation, called `cycle`.

We also define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representatble types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.

-/


namespace List

variable {α : Type _} [DecidableEq α]

/-- Return the `z` such that `x :: z :: _` appears in `xs`, or `default` if there is no such `z`. -/
def nextOr : ∀ (xs : List α) (x default : α), α
  | [], x, default => default
  | [y], x, default => default
  |-- Handles the not-found and the wraparound case
      y ::
      z :: xs,
    x, default => if x = y then z else next_or (z :: xs) x default
#align list.next_or List.nextOr

@[simp]
theorem next_or_nil (x d : α) : nextOr [] x d = d :=
  rfl
#align list.next_or_nil List.next_or_nil

@[simp]
theorem next_or_singleton (x y d : α) : nextOr [y] x d = d :=
  rfl
#align list.next_or_singleton List.next_or_singleton

@[simp]
theorem next_or_self_cons_cons (xs : List α) (x y d : α) : nextOr (x :: y :: xs) x d = y :=
  if_pos rfl
#align list.next_or_self_cons_cons List.next_or_self_cons_cons

theorem next_or_cons_of_ne (xs : List α) (y x d : α) (h : x ≠ y) :
    nextOr (y :: xs) x d = nextOr xs x d :=
  by
  cases' xs with z zs
  · rfl
  · exact if_neg h
#align list.next_or_cons_of_ne List.next_or_cons_of_ne

/-- `next_or` does not depend on the default value, if the next value appears. -/
theorem next_or_eq_next_or_of_mem_of_ne (xs : List α) (x d d' : α) (x_mem : x ∈ xs)
    (x_ne : x ≠ xs.last (ne_nil_of_mem x_mem)) : nextOr xs x d = nextOr xs x d' :=
  by
  induction' xs with y ys IH
  · cases x_mem
  cases' ys with z zs
  · simp at x_mem x_ne
    contradiction
  by_cases h : x = y
  · rw [h, next_or_self_cons_cons, next_or_self_cons_cons]
  · rw [next_or, next_or, IH] <;> simpa [h] using x_mem
#align list.next_or_eq_next_or_of_mem_of_ne List.next_or_eq_next_or_of_mem_of_ne

theorem mem_of_next_or_ne {xs : List α} {x d : α} (h : nextOr xs x d ≠ d) : x ∈ xs :=
  by
  induction' xs with y ys IH
  · simpa using h
  cases' ys with z zs
  · simpa using h
  · by_cases hx : x = y
    · simp [hx]
    · rw [next_or_cons_of_ne _ _ _ _ hx] at h
      simpa [hx] using IH h
#align list.mem_of_next_or_ne List.mem_of_next_or_ne

theorem next_or_concat {xs : List α} {x : α} (d : α) (h : x ∉ xs) : nextOr (xs ++ [x]) x d = d :=
  by
  induction' xs with z zs IH
  · simp
  · obtain ⟨hz, hzs⟩ := not_or_distrib.mp (mt (mem_cons_iff _ _ _).mp h)
    rw [cons_append, next_or_cons_of_ne _ _ _ _ hz, IH hzs]
#align list.next_or_concat List.next_or_concat

theorem next_or_mem {xs : List α} {x d : α} (hd : d ∈ xs) : nextOr xs x d ∈ xs :=
  by
  revert hd
  suffices ∀ (xs' : List α) (h : ∀ x ∈ xs, x ∈ xs') (hd : d ∈ xs'), next_or xs x d ∈ xs' by
    exact this xs fun _ => id
  intro xs' hxs' hd
  induction' xs with y ys ih
  · exact hd
  cases' ys with z zs
  · exact hd
  rw [next_or]
  split_ifs with h
  · exact hxs' _ (mem_cons_of_mem _ (mem_cons_self _ _))
  · exact ih fun _ h => hxs' _ (mem_cons_of_mem _ h)
#align list.next_or_mem List.next_or_mem

/-- Given an element `x : α` of `l : list α` such that `x ∈ l`, get the next
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.

For example:
 * `next [1, 2, 3] 2 _ = 3`
 * `next [1, 2, 3] 3 _ = 1`
 * `next [1, 2, 3, 2, 4] 2 _ = 3`
 * `next [1, 2, 3, 2] 2 _ = 3`
 * `next [1, 1, 2, 3, 2] 1 _ = 1`
-/
def next (l : List α) (x : α) (h : x ∈ l) : α :=
  nextOr l x (l.nthLe 0 (length_pos_of_mem h))
#align list.next List.next

/-- Given an element `x : α` of `l : list α` such that `x ∈ l`, get the previous
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.

 * `prev [1, 2, 3] 2 _ = 1`
 * `prev [1, 2, 3] 1 _ = 3`
 * `prev [1, 2, 3, 2, 4] 2 _ = 1`
 * `prev [1, 2, 3, 4, 2] 2 _ = 1`
 * `prev [1, 1, 2] 1 _ = 2`
-/
def prev : ∀ (l : List α) (x : α) (h : x ∈ l), α
  | [], _, h => by simpa using h
  | [y], _, _ => y
  | y :: z :: xs, x, h =>
    if hx : x = y then getLast (z :: xs) (cons_ne_nil _ _)
    else if x = z then y else prev (z :: xs) x (by simpa [hx] using h)
#align list.prev List.prev

variable (l : List α) (x : α) (h : x ∈ l)

@[simp]
theorem next_singleton (x y : α) (h : x ∈ [y]) : next [y] x h = y :=
  rfl
#align list.next_singleton List.next_singleton

@[simp]
theorem prev_singleton (x y : α) (h : x ∈ [y]) : prev [y] x h = y :=
  rfl
#align list.prev_singleton List.prev_singleton

theorem next_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
    next (y :: z :: l) x h = z := by rw [next, next_or, if_pos hx]
#align list.next_cons_cons_eq' List.next_cons_cons_eq'

@[simp]
theorem next_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) : next (x :: z :: l) x h = z :=
  next_cons_cons_eq' l x x z h rfl
#align list.next_cons_cons_eq List.next_cons_cons_eq

theorem next_ne_head_ne_last (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x ≠ getLast (y :: l) (cons_ne_nil _ _)) :
    next (y :: l) x h = next l x (by simpa [hy] using h) :=
  by
  rw [next, next, next_or_cons_of_ne _ _ _ _ hy, next_or_eq_next_or_of_mem_of_ne]
  · rwa [last_cons] at hx
  · simpa [hy] using h
#align list.next_ne_head_ne_last List.next_ne_head_ne_last

theorem next_cons_concat (y : α) (hy : x ≠ y) (hx : x ∉ l)
    (h : x ∈ y :: l ++ [x] := mem_append_right _ (mem_singleton_self x)) :
    next (y :: l ++ [x]) x h = y := by
  rw [next, next_or_concat]
  · rfl
  · simp [hy, hx]
#align list.next_cons_concat List.next_cons_concat

theorem next_last_cons (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x = getLast (y :: l) (cons_ne_nil _ _)) (hl : Nodup l) : next (y :: l) x h = y :=
  by
  rw [next, nth_le, ← init_append_last (cons_ne_nil y l), hx, next_or_concat]
  subst hx
  intro H
  obtain ⟨_ | k, hk, hk'⟩ := nth_le_of_mem H
  · simpa [init_eq_take, nth_le_take', hy.symm] using hk'
  suffices k.succ = l.length by simpa [this] using hk
  cases' l with hd tl
  · simpa using hk
  · rw [nodup_iff_nth_le_inj] at hl
    rw [length, Nat.succ_inj']
    apply hl
    simpa [init_eq_take, nth_le_take', last_eq_nth_le] using hk'
#align list.next_last_cons List.next_last_cons

theorem prev_last_cons' (y : α) (h : x ∈ y :: l) (hx : x = y) :
    prev (y :: l) x h = getLast (y :: l) (cons_ne_nil _ _) := by cases l <;> simp [prev, hx]
#align list.prev_last_cons' List.prev_last_cons'

@[simp]
theorem prev_last_cons (h : x ∈ x :: l) : prev (x :: l) x h = getLast (x :: l) (cons_ne_nil _ _) :=
  prev_last_cons' l x x h rfl
#align list.prev_last_cons List.prev_last_cons

theorem prev_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
    prev (y :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) := by rw [prev, dif_pos hx]
#align list.prev_cons_cons_eq' List.prev_cons_cons_eq'

@[simp]
theorem prev_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) :
    prev (x :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) :=
  prev_cons_cons_eq' l x x z h rfl
#align list.prev_cons_cons_eq List.prev_cons_cons_eq

theorem prev_cons_cons_of_ne' (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x = z) :
    prev (y :: z :: l) x h = y := by
  cases l
  · simp [prev, hy, hz]
  · rw [prev, dif_neg hy, if_pos hz]
#align list.prev_cons_cons_of_ne' List.prev_cons_cons_of_ne'

theorem prev_cons_cons_of_ne (y : α) (h : x ∈ y :: x :: l) (hy : x ≠ y) :
    prev (y :: x :: l) x h = y :=
  prev_cons_cons_of_ne' _ _ _ _ _ hy rfl
#align list.prev_cons_cons_of_ne List.prev_cons_cons_of_ne

theorem prev_ne_cons_cons (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x ≠ z) :
    prev (y :: z :: l) x h = prev (z :: l) x (by simpa [hy] using h) :=
  by
  cases l
  · simpa [hy, hz] using h
  · rw [prev, dif_neg hy, if_neg hz]
#align list.prev_ne_cons_cons List.prev_ne_cons_cons

include h

theorem next_mem : l.next x h ∈ l :=
  next_or_mem (nthLe_mem _ _ _)
#align list.next_mem List.next_mem

theorem prev_mem : l.prev x h ∈ l := by
  cases' l with hd tl
  · simpa using h
  induction' tl with hd' tl hl generalizing hd
  · simp
  · by_cases hx : x = hd
    · simp only [hx, prev_cons_cons_eq]
      exact mem_cons_of_mem _ (last_mem _)
    · rw [prev, dif_neg hx]
      split_ifs with hm
      · exact mem_cons_self _ _
      · exact mem_cons_of_mem _ (hl _ _)
#align list.prev_mem List.prev_mem

theorem next_nth_le (l : List α) (h : Nodup l) (n : ℕ) (hn : n < l.length) :
    next l (l.nthLe n hn) (nthLe_mem _ _ _) =
      l.nthLe ((n + 1) % l.length) (Nat.mod_lt _ (n.zero_le.trans_lt hn)) :=
  by
  cases' l with x l
  · simpa using hn
  induction' l with y l hl generalizing x n
  · simp
  · cases n
    · simp
    · have hn' : n.succ ≤ l.length.succ :=
        by
        refine' Nat.succ_le_of_lt _
        simpa [Nat.succ_lt_succ_iff] using hn
      have hx' : (x :: y :: l).nthLe n.succ hn ≠ x :=
        by
        intro H
        suffices n.succ = 0 by simpa
        rw [nodup_iff_nth_le_inj] at h
        refine' h _ _ hn Nat.succ_pos' _
        simpa using H
      rcases hn'.eq_or_lt with (hn'' | hn'')
      · rw [next_last_cons]
        · simp [hn'']
        · exact hx'
        · simp [last_eq_nth_le, hn'']
        · exact h.of_cons
      · have : n < l.length := by simpa [Nat.succ_lt_succ_iff] using hn''
        rw [next_ne_head_ne_last _ _ _ _ hx']
        ·
          simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.succ_lt_succ this)), hl _ _ h.of_cons,
            Nat.mod_eq_of_lt (Nat.succ_lt_succ this)]
        · rw [last_eq_nth_le]
          intro H
          suffices n.succ = l.length.succ by exact absurd hn'' this.ge.not_lt
          rw [nodup_iff_nth_le_inj] at h
          refine' h _ _ hn _ _
          · simp
          · simpa using H
#align list.next_nth_le List.next_nth_le

theorem prev_nth_le (l : List α) (h : Nodup l) (n : ℕ) (hn : n < l.length) :
    prev l (l.nthLe n hn) (nthLe_mem _ _ _) =
      l.nthLe ((n + (l.length - 1)) % l.length) (Nat.mod_lt _ (n.zero_le.trans_lt hn)) :=
  by
  cases' l with x l
  · simpa using hn
  induction' l with y l hl generalizing n x
  · simp
  · rcases n with (_ | _ | n)
    · simpa [last_eq_nth_le, Nat.mod_eq_of_lt (Nat.succ_lt_succ l.length.lt_succ_self)]
    · simp only [mem_cons_iff, nodup_cons] at h
      push_neg  at h
      simp [add_comm, prev_cons_cons_of_ne, h.left.left.symm]
    · rw [prev_ne_cons_cons]
      · convert hl _ _ h.of_cons _ using 1
        have : ∀ k hk, (y :: l).nthLe k hk = (x :: y :: l).nthLe (k + 1) (Nat.succ_lt_succ hk) :=
          by
          intros
          simpa
        rw [this]
        congr
        simp only [Nat.add_succ_sub_one, add_zero, length]
        simp only [length, Nat.succ_lt_succ_iff] at hn
        set k := l.length
        rw [Nat.succ_add, ← Nat.add_succ, Nat.add_mod_right, Nat.succ_add, ← Nat.add_succ _ k,
          Nat.add_mod_right, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
        · exact Nat.lt_succ_of_lt hn
        · exact Nat.succ_lt_succ (Nat.lt_succ_of_lt hn)
      · intro H
        suffices n.succ.succ = 0 by simpa
        rw [nodup_iff_nth_le_inj] at h
        refine' h _ _ hn Nat.succ_pos' _
        simpa using H
      · intro H
        suffices n.succ.succ = 1 by simpa
        rw [nodup_iff_nth_le_inj] at h
        refine' h _ _ hn (Nat.succ_lt_succ Nat.succ_pos') _
        simpa using H
#align list.prev_nth_le List.prev_nth_le

theorem pmap_next_eq_rotate_one (h : Nodup l) : (l.pmap l.next fun _ h => h) = l.rotate 1 :=
  by
  apply List.ext_nthLe
  · simp
  · intros
    rw [nth_le_pmap, nth_le_rotate, next_nth_le _ h]
#align list.pmap_next_eq_rotate_one List.pmap_next_eq_rotate_one

theorem pmap_prev_eq_rotate_length_sub_one (h : Nodup l) :
    (l.pmap l.prev fun _ h => h) = l.rotate (l.length - 1) :=
  by
  apply List.ext_nthLe
  · simp
  · intro n hn hn'
    rw [nth_le_rotate, nth_le_pmap, prev_nth_le _ h]
#align list.pmap_prev_eq_rotate_length_sub_one List.pmap_prev_eq_rotate_length_sub_one

theorem prev_next (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    prev l (next l x hx) (next_mem _ _ _) = x :=
  by
  obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx
  simp only [next_nth_le, prev_nth_le, h, Nat.mod_add_mod]
  cases' l with hd tl
  · simp
  · have : n < 1 + tl.length := by simpa [add_comm] using hn
    simp [add_left_comm, add_comm, add_assoc, Nat.mod_eq_of_lt this]
#align list.prev_next List.prev_next

theorem next_prev (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    next l (prev l x hx) (prev_mem _ _ _) = x :=
  by
  obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx
  simp only [next_nth_le, prev_nth_le, h, Nat.mod_add_mod]
  cases' l with hd tl
  · simp
  · have : n < 1 + tl.length := by simpa [add_comm] using hn
    simp [add_left_comm, add_comm, add_assoc, Nat.mod_eq_of_lt this]
#align list.next_prev List.next_prev

theorem prev_reverse_eq_next (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    prev l.reverse x (mem_reverse'.mpr hx) = next l x hx :=
  by
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx
  have lpos : 0 < l.length := k.zero_le.trans_lt hk
  have key : l.length - 1 - k < l.length :=
    (Nat.sub_le _ _).trans_lt (tsub_lt_self lpos Nat.succ_pos')
  rw [← nth_le_pmap l.next (fun _ h => h) (by simpa using hk)]
  simp_rw [← nth_le_reverse l k (key.trans_le (by simp)), pmap_next_eq_rotate_one _ h]
  rw [← nth_le_pmap l.reverse.prev fun _ h => h]
  · simp_rw [pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), rotate_reverse,
      length_reverse, Nat.mod_eq_of_lt (tsub_lt_self lpos Nat.succ_pos'),
      tsub_tsub_cancel_of_le (Nat.succ_le_of_lt lpos)]
    rw [← nth_le_reverse]
    · simp [tsub_tsub_cancel_of_le (Nat.le_pred_of_lt hk)]
    · simpa using (Nat.sub_le _ _).trans_lt (tsub_lt_self lpos Nat.succ_pos')
  · simpa using (Nat.sub_le _ _).trans_lt (tsub_lt_self lpos Nat.succ_pos')
#align list.prev_reverse_eq_next List.prev_reverse_eq_next

theorem next_reverse_eq_prev (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    next l.reverse x (mem_reverse'.mpr hx) = prev l x hx :=
  by
  convert (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm
  exact (reverse_reverse l).symm
#align list.next_reverse_eq_prev List.next_reverse_eq_prev

theorem is_rotated_next_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x ∈ l) :
    l.next x hx = l'.next x (h.mem_iff.mp hx) :=
  by
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx
  obtain ⟨n, rfl⟩ := id h
  rw [next_nth_le _ hn]
  simp_rw [← nth_le_rotate' _ n k]
  rw [next_nth_le _ (h.nodup_iff.mp hn), ← nth_le_rotate' _ n]
  simp [add_assoc]
#align list.is_rotated_next_eq List.is_rotated_next_eq

theorem is_rotated_prev_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x ∈ l) :
    l.prev x hx = l'.prev x (h.mem_iff.mp hx) :=
  by
  rw [← next_reverse_eq_prev _ hn, ← next_reverse_eq_prev _ (h.nodup_iff.mp hn)]
  exact is_rotated_next_eq h.reverse (nodup_reverse.mpr hn) _
#align list.is_rotated_prev_eq List.is_rotated_prev_eq

end List

open List

/-- `cycle α` is the quotient of `list α` by cyclic permutation.
Duplicates are allowed.
-/
def Cycle (α : Type _) : Type _ :=
  Quotient (IsRotated.setoid α)
#align cycle Cycle

namespace Cycle

variable {α : Type _}

instance : Coe (List α) (Cycle α) :=
  ⟨Quot.mk _⟩

@[simp]
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = l₂ ↔ l₁ ~r l₂ :=
  @Quotient.eq _ (IsRotated.setoid _) _ _
#align cycle.coe_eq_coe Cycle.coe_eq_coe

@[simp]
theorem mk_eq_coe (l : List α) : Quot.mk _ l = (l : Cycle α) :=
  rfl
#align cycle.mk_eq_coe Cycle.mk_eq_coe

@[simp]
theorem mk'_eq_coe (l : List α) : Quotient.mk' l = (l : Cycle α) :=
  rfl
#align cycle.mk'_eq_coe Cycle.mk'_eq_coe

theorem coe_cons_eq_coe_append (l : List α) (a : α) : (↑(a :: l) : Cycle α) = ↑(l ++ [a]) :=
  Quot.sound ⟨1, by rw [rotate_cons_succ, rotate_zero]⟩
#align cycle.coe_cons_eq_coe_append Cycle.coe_cons_eq_coe_append

/-- The unique empty cycle. -/
def nil : Cycle α :=
  ([] : List α)
#align cycle.nil Cycle.nil

@[simp]
theorem coe_nil : ↑([] : List α) = @nil α :=
  rfl
#align cycle.coe_nil Cycle.coe_nil

@[simp]
theorem coe_eq_nil (l : List α) : (l : Cycle α) = nil ↔ l = [] :=
  coe_eq_coe.trans isRotated_nil_iff
#align cycle.coe_eq_nil Cycle.coe_eq_nil

/-- For consistency with `list.has_emptyc`. -/
instance : EmptyCollection (Cycle α) :=
  ⟨nil⟩

@[simp]
theorem empty_eq : ∅ = @nil α :=
  rfl
#align cycle.empty_eq Cycle.empty_eq

instance : Inhabited (Cycle α) :=
  ⟨nil⟩

/-- An induction principle for `cycle`. Use as `induction s using cycle.induction_on`. -/
@[elab_as_elim]
theorem induction_on {C : Cycle α → Prop} (s : Cycle α) (H0 : C nil)
    (HI : ∀ (a) (l : List α), C ↑l → C ↑(a :: l)) : C s :=
  Quotient.inductionOn' s fun l => by
    apply List.recOn l <;> simp
    assumption'
#align cycle.induction_on Cycle.induction_on

/-- For `x : α`, `s : cycle α`, `x ∈ s` indicates that `x` occurs at least once in `s`. -/
def Mem (a : α) (s : Cycle α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun l₁ l₂ e => propext <| e.mem_iff
#align cycle.mem Cycle.Mem

instance : Membership α (Cycle α) :=
  ⟨Mem⟩

@[simp]
theorem mem_coe_iff {a : α} {l : List α} : a ∈ (l : Cycle α) ↔ a ∈ l :=
  Iff.rfl
#align cycle.mem_coe_iff Cycle.mem_coe_iff

@[simp]
theorem not_mem_nil : ∀ a, a ∉ @nil α :=
  not_mem_nil
#align cycle.not_mem_nil Cycle.not_mem_nil

instance [DecidableEq α] : DecidableEq (Cycle α) := fun s₁ s₂ =>
  Quotient.recOnSubsingleton₂' s₁ s₂ fun l₁ l₂ => decidable_of_iff' _ Quotient.eq'

instance [DecidableEq α] (x : α) (s : Cycle α) : Decidable (x ∈ s) :=
  Quotient.recOnSubsingleton' s fun l => List.decidableMem x l

/-- Reverse a `s : cycle α` by reversing the underlying `list`. -/
def reverse (s : Cycle α) : Cycle α :=
  Quot.map reverse (fun l₁ l₂ => IsRotated.reverse) s
#align cycle.reverse Cycle.reverse

@[simp]
theorem reverse_coe (l : List α) : (l : Cycle α).reverse = l.reverse :=
  rfl
#align cycle.reverse_coe Cycle.reverse_coe

@[simp]
theorem mem_reverse_iff {a : α} {s : Cycle α} : a ∈ s.reverse ↔ a ∈ s :=
  Quot.inductionOn s fun _ => mem_reverse'
#align cycle.mem_reverse_iff Cycle.mem_reverse_iff

@[simp]
theorem reverse_reverse (s : Cycle α) : s.reverse.reverse = s :=
  Quot.inductionOn s fun _ => by simp
#align cycle.reverse_reverse Cycle.reverse_reverse

@[simp]
theorem reverse_nil : nil.reverse = @nil α :=
  rfl
#align cycle.reverse_nil Cycle.reverse_nil

/-- The length of the `s : cycle α`, which is the number of elements, counting duplicates. -/
def length (s : Cycle α) : ℕ :=
  Quot.liftOn s length fun l₁ l₂ e => e.Perm.length_eq
#align cycle.length Cycle.length

@[simp]
theorem length_coe (l : List α) : length (l : Cycle α) = l.length :=
  rfl
#align cycle.length_coe Cycle.length_coe

@[simp]
theorem length_nil : length (@nil α) = 0 :=
  rfl
#align cycle.length_nil Cycle.length_nil

@[simp]
theorem length_reverse (s : Cycle α) : s.reverse.length = s.length :=
  Quot.inductionOn s length_reverse
#align cycle.length_reverse Cycle.length_reverse

/-- A `s : cycle α` that is at most one element. -/
def Subsingleton (s : Cycle α) : Prop :=
  s.length ≤ 1
#align cycle.subsingleton Cycle.Subsingleton

theorem subsingleton_nil : Subsingleton (@nil α) :=
  zero_le_one
#align cycle.subsingleton_nil Cycle.subsingleton_nil

theorem length_subsingleton_iff {s : Cycle α} : Subsingleton s ↔ length s ≤ 1 :=
  Iff.rfl
#align cycle.length_subsingleton_iff Cycle.length_subsingleton_iff

@[simp]
theorem subsingleton_reverse_iff {s : Cycle α} : s.reverse.Subsingleton ↔ s.Subsingleton := by
  simp [length_subsingleton_iff]
#align cycle.subsingleton_reverse_iff Cycle.subsingleton_reverse_iff

theorem Subsingleton.congr {s : Cycle α} (h : Subsingleton s) :
    ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x = y :=
  by
  induction' s using Quot.inductionOn with l
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe, le_iff_lt_or_eq, Nat.lt_add_one_iff,
    length_eq_zero, length_eq_one, Nat.not_lt_zero, false_or_iff] at h
  rcases h with (rfl | ⟨z, rfl⟩) <;> simp
#align cycle.subsingleton.congr Cycle.Subsingleton.congr

/-- A `s : cycle α` that is made up of at least two unique elements. -/
def Nontrivial (s : Cycle α) : Prop :=
  ∃ (x y : α)(h : x ≠ y), x ∈ s ∧ y ∈ s
#align cycle.nontrivial Cycle.Nontrivial

@[simp]
theorem nontrivial_coe_nodup_iff {l : List α} (hl : l.Nodup) :
    Nontrivial (l : Cycle α) ↔ 2 ≤ l.length :=
  by
  rw [Nontrivial]
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp
  · simp
  · simp only [mem_cons_iff, exists_prop, mem_coe_iff, List.length, Ne.def, Nat.succ_le_succ_iff,
      zero_le, iff_true_iff]
    refine' ⟨hd, hd', _, by simp⟩
    simp only [not_or, mem_cons_iff, nodup_cons] at hl
    exact hl.left.left
#align cycle.nontrivial_coe_nodup_iff Cycle.nontrivial_coe_nodup_iff

@[simp]
theorem nontrivial_reverse_iff {s : Cycle α} : s.reverse.Nontrivial ↔ s.Nontrivial := by
  simp [Nontrivial]
#align cycle.nontrivial_reverse_iff Cycle.nontrivial_reverse_iff

theorem length_nontrivial {s : Cycle α} (h : Nontrivial s) : 2 ≤ length s :=
  by
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  induction' s using Quot.inductionOn with l
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simpa using hx
  · simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy
    simpa [hx, hy] using hxy
  · simp [bit0]
#align cycle.length_nontrivial Cycle.length_nontrivial

/-- The `s : cycle α` contains no duplicates. -/
def Nodup (s : Cycle α) : Prop :=
  Quot.liftOn s Nodup fun l₁ l₂ e => propext <| e.nodup_iff
#align cycle.nodup Cycle.Nodup

@[simp]
theorem nodup_nil : Nodup (@nil α) :=
  nodup_nil
#align cycle.nodup_nil Cycle.nodup_nil

@[simp]
theorem nodup_coe_iff {l : List α} : Nodup (l : Cycle α) ↔ l.Nodup :=
  Iff.rfl
#align cycle.nodup_coe_iff Cycle.nodup_coe_iff

@[simp]
theorem nodup_reverse_iff {s : Cycle α} : s.reverse.Nodup ↔ s.Nodup :=
  Quot.inductionOn s fun _ => nodup_reverse
#align cycle.nodup_reverse_iff Cycle.nodup_reverse_iff

theorem Subsingleton.nodup {s : Cycle α} (h : Subsingleton s) : Nodup s :=
  by
  induction' s using Quot.inductionOn with l
  cases' l with hd tl
  · simp
  · have : tl = [] := by simpa [Subsingleton, length_eq_zero] using h
    simp [this]
#align cycle.subsingleton.nodup Cycle.Subsingleton.nodup

theorem Nodup.nontrivial_iff {s : Cycle α} (h : Nodup s) : Nontrivial s ↔ ¬Subsingleton s :=
  by
  rw [length_subsingleton_iff]
  induction s using Quotient.inductionOn'
  simp only [mk'_eq_coe, nodup_coe_iff] at h
  simp [h, Nat.succ_le_iff]
#align cycle.nodup.nontrivial_iff Cycle.Nodup.nontrivial_iff

/-- The `s : cycle α` as a `multiset α`.
-/
def toMultiset (s : Cycle α) : Multiset α :=
  Quotient.liftOn' s coe fun l₁ l₂ h => Multiset.coe_eq_coe.mpr h.Perm
#align cycle.to_multiset Cycle.toMultiset

@[simp]
theorem coe_to_multiset (l : List α) : (l : Cycle α).toMultiset = l :=
  rfl
#align cycle.coe_to_multiset Cycle.coe_to_multiset

@[simp]
theorem nil_to_multiset : nil.toMultiset = (0 : Multiset α) :=
  rfl
#align cycle.nil_to_multiset Cycle.nil_to_multiset

@[simp]
theorem card_to_multiset (s : Cycle α) : s.toMultiset.card = s.length :=
  Quotient.inductionOn' s (by simp)
#align cycle.card_to_multiset Cycle.card_to_multiset

@[simp]
theorem to_multiset_eq_nil {s : Cycle α} : s.toMultiset = 0 ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)
#align cycle.to_multiset_eq_nil Cycle.to_multiset_eq_nil

/-- The lift of `list.map`. -/
def map {β : Type _} (f : α → β) : Cycle α → Cycle β :=
  Quotient.map' (List.map f) fun l₁ l₂ h => h.map _
#align cycle.map Cycle.map

@[simp]
theorem map_nil {β : Type _} (f : α → β) : map f nil = nil :=
  rfl
#align cycle.map_nil Cycle.map_nil

@[simp]
theorem map_coe {β : Type _} (f : α → β) (l : List α) : map f ↑l = List.map f l :=
  rfl
#align cycle.map_coe Cycle.map_coe

@[simp]
theorem map_eq_nil {β : Type _} (f : α → β) (s : Cycle α) : map f s = nil ↔ s = nil :=
  Quotient.inductionOn' s (by simp)
#align cycle.map_eq_nil Cycle.map_eq_nil

/-- The `multiset` of lists that can make the cycle. -/
def lists (s : Cycle α) : Multiset (List α) :=
  Quotient.liftOn' s (fun l => (l.cyclicPermutations : Multiset (List α))) fun l₁ l₂ h => by
    simpa using h.cyclic_permutations.perm
#align cycle.lists Cycle.lists

@[simp]
theorem lists_coe (l : List α) : lists (l : Cycle α) = ↑l.cyclicPermutations :=
  rfl
#align cycle.lists_coe Cycle.lists_coe

@[simp]
theorem mem_lists_iff_coe_eq {s : Cycle α} {l : List α} : l ∈ s.lists ↔ (l : Cycle α) = s :=
  Quotient.inductionOn' s fun l =>
    by
    rw [lists, Quotient.lift_on'_mk']
    simp
#align cycle.mem_lists_iff_coe_eq Cycle.mem_lists_iff_coe_eq

@[simp]
theorem lists_nil : lists (@nil α) = [([] : List α)] := by
  rw [nil, lists_coe, cyclic_permutations_nil]
#align cycle.lists_nil Cycle.lists_nil

section Decidable

variable [DecidableEq α]

/-- Auxiliary decidability algorithm for lists that contain at least two unique elements.
-/
def decidableNontrivialCoe : ∀ l : List α, Decidable (Nontrivial (l : Cycle α))
  | [] => isFalse (by simp [Nontrivial])
  | [x] => isFalse (by simp [Nontrivial])
  | x :: y :: l =>
    if h : x = y then
      @decidable_of_iff' _ (Nontrivial (x :: l : Cycle α)) (by simp [h, Nontrivial])
        (decidable_nontrivial_coe (x :: l))
    else isTrue ⟨x, y, h, by simp, by simp⟩
#align cycle.decidable_nontrivial_coe Cycle.decidableNontrivialCoe

instance {s : Cycle α} : Decidable (Nontrivial s) :=
  Quot.recOnSubsingleton' s decidableNontrivialCoe

instance {s : Cycle α} : Decidable (Nodup s) :=
  Quot.recOnSubsingleton' s List.nodupDecidable

instance fintypeNodupCycle [Fintype α] : Fintype { s : Cycle α // s.Nodup } :=
  Fintype.ofSurjective (fun l : { l : List α // l.Nodup } => ⟨l.val, by simpa using l.prop⟩)
    fun ⟨s, hs⟩ => by
    induction s using Quotient.inductionOn'
    exact ⟨⟨s, hs⟩, by simp⟩
#align cycle.fintype_nodup_cycle Cycle.fintypeNodupCycle

instance fintypeNodupNontrivialCycle [Fintype α] :
    Fintype { s : Cycle α // s.Nodup ∧ s.Nontrivial } :=
  Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.Nodup }).map (Function.Embedding.subtype _)).filter
      Cycle.Nontrivial)
    (by simp)
#align cycle.fintype_nodup_nontrivial_cycle Cycle.fintypeNodupNontrivialCycle

/-- The `s : cycle α` as a `finset α`. -/
def toFinset (s : Cycle α) : Finset α :=
  s.toMultiset.toFinset
#align cycle.to_finset Cycle.toFinset

@[simp]
theorem to_finset_to_multiset (s : Cycle α) : s.toMultiset.toFinset = s.toFinset :=
  rfl
#align cycle.to_finset_to_multiset Cycle.to_finset_to_multiset

@[simp]
theorem coe_to_finset (l : List α) : (l : Cycle α).toFinset = l.toFinset :=
  rfl
#align cycle.coe_to_finset Cycle.coe_to_finset

@[simp]
theorem nil_to_finset : (@nil α).toFinset = ∅ :=
  rfl
#align cycle.nil_to_finset Cycle.nil_to_finset

@[simp]
theorem to_finset_eq_nil {s : Cycle α} : s.toFinset = ∅ ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)
#align cycle.to_finset_eq_nil Cycle.to_finset_eq_nil

/-- Given a `s : cycle α` such that `nodup s`, retrieve the next element after `x ∈ s`. -/
def next : ∀ (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s), α := fun s =>
  Quot.hrecOn s (fun l hn x hx => next l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by simpa [eq_of_heq hxy] using h.mem_iff)) fun hm hm' he' =>
          heq_of_eq (by simpa [eq_of_heq hxy] using is_rotated_next_eq h h₁ _)
#align cycle.next Cycle.next

/-- Given a `s : cycle α` such that `nodup s`, retrieve the previous element before `x ∈ s`. -/
def prev : ∀ (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s), α := fun s =>
  Quot.hrecOn s (fun l hn x hx => prev l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by simpa [eq_of_heq hxy] using h.mem_iff)) fun hm hm' he' =>
          heq_of_eq (by simpa [eq_of_heq hxy] using is_rotated_prev_eq h h₁ _)
#align cycle.prev Cycle.prev

@[simp]
theorem prev_reverse_eq_next (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) :
    s.reverse.prev (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.next hs x hx :=
  (Quotient.inductionOn' s prev_reverse_eq_next) hs x hx
#align cycle.prev_reverse_eq_next Cycle.prev_reverse_eq_next

@[simp]
theorem next_reverse_eq_prev (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) :
    s.reverse.next (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.prev hs x hx := by
  simp [← prev_reverse_eq_next]
#align cycle.next_reverse_eq_prev Cycle.next_reverse_eq_prev

@[simp]
theorem next_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) : s.next hs x hx ∈ s :=
  by
  induction s using Quot.inductionOn
  apply next_mem
#align cycle.next_mem Cycle.next_mem

theorem prev_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) : s.prev hs x hx ∈ s :=
  by
  rw [← next_reverse_eq_prev, ← mem_reverse_iff]
  apply next_mem
#align cycle.prev_mem Cycle.prev_mem

@[simp]
theorem prev_next (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) :
    s.prev hs (s.next hs x hx) (next_mem s hs x hx) = x :=
  (Quotient.inductionOn' s prev_next) hs x hx
#align cycle.prev_next Cycle.prev_next

@[simp]
theorem next_prev (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) :
    s.next hs (s.prev hs x hx) (prev_mem s hs x hx) = x :=
  (Quotient.inductionOn' s next_prev) hs x hx
#align cycle.next_prev Cycle.next_prev

end Decidable

/-- We define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.
-/
unsafe instance [Repr α] : Repr (Cycle α) :=
  ⟨fun s => "c[" ++ String.intercalate ", " (s.map repr).lists.unquot.head ++ "]"⟩

/-- `chain R s` means that `R` holds between adjacent elements of `s`.

`chain R ([a, b, c] : cycle α) ↔ R a b ∧ R b c ∧ R c a` -/
def Chain (r : α → α → Prop) (c : Cycle α) : Prop :=
  Quotient.liftOn' c
    (fun l =>
      match l with
      | [] => True
      | a :: m => Chain r a (m ++ [a]))
    fun a b hab =>
    propext <| by
      cases' a with a l <;> cases' b with b m
      · rfl
      · have := is_rotated_nil_iff'.1 hab
        contradiction
      · have := is_rotated_nil_iff.1 hab
        contradiction
      · unfold chain._match_1
        cases' hab with n hn
        induction' n with d hd generalizing a b l m
        · simp only [rotate_zero] at hn
          rw [hn.1, hn.2]
        · cases' l with c s
          · simp only [rotate_singleton] at hn
            rw [hn.1, hn.2]
          · rw [Nat.succ_eq_one_add, ← rotate_rotate, rotate_cons_succ, rotate_zero, cons_append] at
              hn
            rw [← hd c _ _ _ hn]
            simp [and_comm]
#align cycle.chain Cycle.Chain

@[simp]
theorem Chain.nil (r : α → α → Prop) : Cycle.Chain r (@nil α) := by trivial
#align cycle.chain.nil Cycle.Chain.nil

@[simp]
theorem chain_coe_cons (r : α → α → Prop) (a : α) (l : List α) :
    Chain r (a :: l) ↔ List.Chain r a (l ++ [a]) :=
  Iff.rfl
#align cycle.chain_coe_cons Cycle.chain_coe_cons

@[simp]
theorem chain_singleton (r : α → α → Prop) (a : α) : Chain r [a] ↔ r a a := by
  rw [chain_coe_cons, nil_append, chain_singleton]
#align cycle.chain_singleton Cycle.chain_singleton

theorem chain_ne_nil (r : α → α → Prop) {l : List α} :
    ∀ hl : l ≠ [], Chain r l ↔ List.Chain r (getLast l hl) l :=
  by
  apply l.reverse_rec_on
  exact fun hm => hm.irrefl.elim
  intro m a H _
  rw [← coe_cons_eq_coe_append, chain_coe_cons, last_append_singleton]
#align cycle.chain_ne_nil Cycle.chain_ne_nil

theorem chain_map {β : Type _} {r : α → α → Prop} (f : β → α) {s : Cycle β} :
    Chain r (s.map f) ↔ Chain (fun a b => r (f a) (f b)) s :=
  Quotient.inductionOn' s fun l => by
    cases' l with a l
    rfl
    convert List.chain_map f
    rw [map_append f l [a]]
    rfl
#align cycle.chain_map Cycle.chain_map

theorem chain_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    Chain r (List.range n.succ) ↔ r n 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ, ← coe_cons_eq_coe_append, chain_coe_cons, ← range_succ, chain_range_succ]
#align cycle.chain_range_succ Cycle.chain_range_succ

variable {r : α → α → Prop} {s : Cycle α}

theorem chain_of_pairwise : (∀ a ∈ s, ∀ b ∈ s, r a b) → Chain r s :=
  by
  induction' s using Cycle.induction_on with a l _
  exact fun _ => Cycle.Chain.nil r
  intro hs
  have Ha : a ∈ (a :: l : Cycle α) := by simp
  have Hl : ∀ {b} (hb : b ∈ l), b ∈ (a :: l : Cycle α) := fun b hb => by simp [hb]
  rw [Cycle.chain_coe_cons]
  apply pairwise.chain
  rw [pairwise_cons]
  refine'
    ⟨fun b hb => _,
      pairwise_append.2
        ⟨pairwise_of_forall_mem_list fun b hb c hc => hs b (Hl hb) c (Hl hc),
          pairwise_singleton r a, fun b hb c hc => _⟩⟩
  · rw [mem_append] at hb
    cases hb
    · exact hs a Ha b (Hl hb)
    · rw [mem_singleton] at hb
      rw [hb]
      exact hs a Ha a Ha
  · rw [mem_singleton] at hc
    rw [hc]
    exact hs b (Hl hb) a Ha
#align cycle.chain_of_pairwise Cycle.chain_of_pairwise

theorem chain_iff_pairwise [IsTrans α r] : Chain r s ↔ ∀ a ∈ s, ∀ b ∈ s, r a b :=
  ⟨by
    induction' s using Cycle.induction_on with a l _
    exact fun _ b hb => hb.elim
    intro hs b hb c hc
    rw [Cycle.chain_coe_cons, chain_iff_pairwise] at hs
    simp only [pairwise_append, pairwise_cons, mem_append, mem_singleton, List.not_mem_nil,
      IsEmpty.forall_iff, imp_true_iff, pairwise.nil, forall_eq, true_and_iff] at hs
    simp only [mem_coe_iff, mem_cons_iff] at hb hc
    rcases hb with (rfl | hb) <;> rcases hc with (rfl | hc)
    · exact hs.1 c (Or.inr rfl)
    · exact hs.1 c (Or.inl hc)
    · exact hs.2.2 b hb
    · exact trans (hs.2.2 b hb) (hs.1 c (Or.inl hc)), Cycle.chain_of_pairwise⟩
#align cycle.chain_iff_pairwise Cycle.chain_iff_pairwise

theorem forall_eq_of_chain [IsTrans α r] [IsAntisymm α r] (hs : Chain r s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : a = b := by
  rw [chain_iff_pairwise] at hs
  exact antisymm (hs a ha b hb) (hs b hb a ha)
#align cycle.forall_eq_of_chain Cycle.forall_eq_of_chain

end Cycle

