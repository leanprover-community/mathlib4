/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Rotate

#align_import data.list.cycle from "leanprover-community/mathlib"@"7413128c3bcb3b0818e3e18720abc9ea3100fb49"

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `IsRotated`.

Based on this, we define the quotient of lists by the rotation relation, called `Cycle`.

We also define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.

-/


namespace List

variable {α : Type*} [DecidableEq α]

/-- Return the `z` such that `x :: z :: _` appears in `xs`, or `default` if there is no such `z`. -/
def nextOr : ∀ (_ : List α) (_ _ : α), α
  | [], _, default => default
  | [_], _, default => default
  -- Handles the not-found and the wraparound case
  | y :: z :: xs, x, default => if x = y then z else nextOr (z :: xs) x default
#align list.next_or List.nextOr

@[simp]
theorem nextOr_nil (x d : α) : nextOr [] x d = d :=
  rfl
#align list.next_or_nil List.nextOr_nil

@[simp]
theorem nextOr_singleton (x y d : α) : nextOr [y] x d = d :=
  rfl
#align list.next_or_singleton List.nextOr_singleton

@[simp]
theorem nextOr_self_cons_cons (xs : List α) (x y d : α) : nextOr (x :: y :: xs) x d = y :=
  if_pos rfl
#align list.next_or_self_cons_cons List.nextOr_self_cons_cons

theorem nextOr_cons_of_ne (xs : List α) (y x d : α) (h : x ≠ y) :
    nextOr (y :: xs) x d = nextOr xs x d := by
  cases' xs with z zs
  -- ⊢ nextOr [y] x d = nextOr [] x d
  · rfl
    -- 🎉 no goals
  · exact if_neg h
    -- 🎉 no goals
#align list.next_or_cons_of_ne List.nextOr_cons_of_ne

/-- `nextOr` does not depend on the default value, if the next value appears. -/
theorem nextOr_eq_nextOr_of_mem_of_ne (xs : List α) (x d d' : α) (x_mem : x ∈ xs)
    (x_ne : x ≠ xs.getLast (ne_nil_of_mem x_mem)) : nextOr xs x d = nextOr xs x d' := by
  induction' xs with y ys IH
  -- ⊢ nextOr [] x d = nextOr [] x d'
  · cases x_mem
    -- 🎉 no goals
  cases' ys with z zs
  -- ⊢ nextOr [y] x d = nextOr [y] x d'
  · simp at x_mem x_ne
    -- ⊢ nextOr [y] x d = nextOr [y] x d'
    contradiction
    -- 🎉 no goals
  by_cases h : x = y
  -- ⊢ nextOr (y :: z :: zs) x d = nextOr (y :: z :: zs) x d'
  · rw [h, nextOr_self_cons_cons, nextOr_self_cons_cons]
    -- 🎉 no goals
  · rw [nextOr, nextOr, IH]
    -- ⊢ x ∈ z :: zs
    · simpa [h] using x_mem
      -- 🎉 no goals
    · simpa using x_ne
      -- 🎉 no goals
#align list.next_or_eq_next_or_of_mem_of_ne List.nextOr_eq_nextOr_of_mem_of_ne

theorem mem_of_nextOr_ne {xs : List α} {x d : α} (h : nextOr xs x d ≠ d) : x ∈ xs := by
  induction' xs with y ys IH
  -- ⊢ x ∈ []
  · simp at h
    -- 🎉 no goals
  cases' ys with z zs
  -- ⊢ x ∈ [y]
  · simp at h
    -- 🎉 no goals
  · by_cases hx : x = y
    -- ⊢ x ∈ y :: z :: zs
    · simp [hx]
      -- 🎉 no goals
    · rw [nextOr_cons_of_ne _ _ _ _ hx] at h
      -- ⊢ x ∈ y :: z :: zs
      simpa [hx] using IH h
      -- 🎉 no goals
#align list.mem_of_next_or_ne List.mem_of_nextOr_ne

theorem nextOr_concat {xs : List α} {x : α} (d : α) (h : x ∉ xs) : nextOr (xs ++ [x]) x d = d := by
  induction' xs with z zs IH
  -- ⊢ nextOr ([] ++ [x]) x d = d
  · simp
    -- 🎉 no goals
  · obtain ⟨hz, hzs⟩ := not_or.mp (mt mem_cons.2 h)
    -- ⊢ nextOr (z :: zs ++ [x]) x d = d
    rw [cons_append, nextOr_cons_of_ne _ _ _ _ hz, IH hzs]
    -- 🎉 no goals
#align list.next_or_concat List.nextOr_concat

theorem nextOr_mem {xs : List α} {x d : α} (hd : d ∈ xs) : nextOr xs x d ∈ xs := by
  revert hd
  -- ⊢ d ∈ xs → nextOr xs x d ∈ xs
  suffices ∀ (xs' : List α) (_ : ∀ x ∈ xs, x ∈ xs') (_ : d ∈ xs'), nextOr xs x d ∈ xs' by
    exact this xs fun _ => id
  intro xs' hxs' hd
  -- ⊢ nextOr xs x d ∈ xs'
  induction' xs with y ys ih
  -- ⊢ nextOr [] x d ∈ xs'
  · exact hd
    -- 🎉 no goals
  cases' ys with z zs
  -- ⊢ nextOr [y] x d ∈ xs'
  · exact hd
    -- 🎉 no goals
  rw [nextOr]
  -- ⊢ (if x = y then z else nextOr (z :: zs) x d) ∈ xs'
  split_ifs with h
  -- ⊢ z ∈ xs'
  · exact hxs' _ (mem_cons_of_mem _ (mem_cons_self _ _))
    -- 🎉 no goals
  · exact ih fun _ h => hxs' _ (mem_cons_of_mem _ h)
    -- 🎉 no goals
#align list.next_or_mem List.nextOr_mem

/-- Given an element `x : α` of `l : List α` such that `x ∈ l`, get the next
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
  nextOr l x (l.get ⟨0, length_pos_of_mem h⟩)
#align list.next List.next

/-- Given an element `x : α` of `l : List α` such that `x ∈ l`, get the previous
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.

 * `prev [1, 2, 3] 2 _ = 1`
 * `prev [1, 2, 3] 1 _ = 3`
 * `prev [1, 2, 3, 2, 4] 2 _ = 1`
 * `prev [1, 2, 3, 4, 2] 2 _ = 1`
 * `prev [1, 1, 2] 1 _ = 2`
-/
def prev : ∀ (l : List α) (x : α) (_h : x ∈ l), α
  | [], _, h => by simp at h
                   -- 🎉 no goals
  | [y], _, _ => y
  | y :: z :: xs, x, h =>
    if hx : x = y then getLast (z :: xs) (cons_ne_nil _ _)
    else if x = z then y else prev (z :: xs) x (by simpa [hx] using h)
                                                   -- 🎉 no goals
#align list.prev List.prev

variable (l : List α) (x : α)

@[simp]
theorem next_singleton (x y : α) (h : x ∈ [y]) : next [y] x h = y :=
  rfl
#align list.next_singleton List.next_singleton

@[simp]
theorem prev_singleton (x y : α) (h : x ∈ [y]) : prev [y] x h = y :=
  rfl
#align list.prev_singleton List.prev_singleton

theorem next_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
    next (y :: z :: l) x h = z := by rw [next, nextOr, if_pos hx]
                                     -- 🎉 no goals
#align list.next_cons_cons_eq' List.next_cons_cons_eq'

@[simp]
theorem next_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) : next (x :: z :: l) x h = z :=
  next_cons_cons_eq' l x x z h rfl
#align list.next_cons_cons_eq List.next_cons_cons_eq

theorem next_ne_head_ne_getLast (h : x ∈ l) (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x ≠ getLast (y :: l) (cons_ne_nil _ _)) :
    next (y :: l) x h = next l x (by simpa [hy] using h) := by
                                     -- 🎉 no goals
  rw [next, next, nextOr_cons_of_ne _ _ _ _ hy, nextOr_eq_nextOr_of_mem_of_ne]
  -- ⊢ x ∈ l
  · rwa [getLast_cons] at hx
    -- ⊢ l ≠ []
    exact ne_nil_of_mem (by assumption)
    -- 🎉 no goals
  · rwa [getLast_cons] at hx
    -- 🎉 no goals
#align list.next_ne_head_ne_last List.next_ne_head_ne_getLast

theorem next_cons_concat (y : α) (hy : x ≠ y) (hx : x ∉ l)
    (h : x ∈ y :: l ++ [x] := mem_append_right _ (mem_singleton_self x)) :
    next (y :: l ++ [x]) x h = y := by
  rw [next, nextOr_concat]
  -- ⊢ get (y :: l ++ [x]) { val := 0, isLt := (_ : 0 < length (y :: l ++ [x])) } = y
  · rfl
    -- 🎉 no goals
  · simp [hy, hx]
    -- 🎉 no goals
#align list.next_cons_concat List.next_cons_concat

theorem next_getLast_cons (h : x ∈ l) (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x = getLast (y :: l) (cons_ne_nil _ _)) (hl : Nodup l) : next (y :: l) x h = y := by
  rw [next, get, ← dropLast_append_getLast (cons_ne_nil y l), hx, nextOr_concat]
  -- ⊢ ¬getLast (y :: l) (_ : y :: l ≠ []) ∈ dropLast (y :: l)
  subst hx
  -- ⊢ ¬getLast (y :: l) (_ : y :: l ≠ []) ∈ dropLast (y :: l)
  intro H
  -- ⊢ False
  obtain ⟨⟨_ | k, hk⟩, hk'⟩ := get_of_mem H
  -- ⊢ False
  · rw [← Option.some_inj] at hk'
    -- ⊢ False
    rw [← get?_eq_get, dropLast_eq_take, get?_take, get?_zero, head?_cons,
      Option.some_inj] at hk'
    exact hy (Eq.symm hk')
    -- ⊢ Nat.zero < Nat.pred (length (y :: l))
    rw [Nat.zero_eq, length_cons, Nat.pred_succ]
    -- ⊢ 0 < length l
    exact length_pos_of_mem (by assumption)
    -- 🎉 no goals
  suffices k.succ = l.length by simp [this] at hk
  -- ⊢ Nat.succ k = length l
  cases' l with hd tl
  -- ⊢ Nat.succ k = length []
  · simp at hk
    -- 🎉 no goals
  · rw [nodup_iff_injective_get] at hl
    -- ⊢ Nat.succ k = length (hd :: tl)
    rw [length, Nat.succ_inj']
    -- ⊢ k = length tl
    refine' Fin.veq_of_eq (@hl ⟨k, Nat.lt_of_succ_lt <| by simpa using hk⟩ ⟨tl.length, by simp⟩ _)
    -- ⊢ get (hd :: tl) { val := k, isLt := (_ : k < length (hd :: tl)) } = get (hd : …
    rw [← Option.some_inj] at hk'
    -- ⊢ get (hd :: tl) { val := k, isLt := (_ : k < length (hd :: tl)) } = get (hd : …
    rw [← get?_eq_get, dropLast_eq_take, get?_take, get?, get?_eq_get, Option.some_inj] at hk'
    rw [hk']
    -- ⊢ getLast (y :: hd :: tl) (_ : y :: hd :: tl ≠ []) = get (hd :: tl) { val := l …
    simp [getLast_eq_get]
    -- ⊢ Nat.succ k < Nat.pred (length (y :: hd :: tl))
    simpa using hk
    -- 🎉 no goals
#align list.next_last_cons List.next_getLast_cons

theorem prev_getLast_cons' (y : α) (hxy : x ∈ y :: l) (hx : x = y) :
    prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _) := by cases l <;> simp [prev, hx]
                                                                   -- ⊢ prev [y] x hxy = getLast [y] (_ : [y] ≠ [])
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
#align list.prev_last_cons' List.prev_getLast_cons'

@[simp]
theorem prev_getLast_cons (h : x ∈ x :: l) :
    prev (x :: l) x h = getLast (x :: l) (cons_ne_nil _ _) :=
  prev_getLast_cons' l x x h rfl
#align list.prev_last_cons List.prev_getLast_cons

theorem prev_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
    prev (y :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) := by rw [prev, dif_pos hx]
                                                                      -- 🎉 no goals
#align list.prev_cons_cons_eq' List.prev_cons_cons_eq'

--@[simp] Porting note: `simp` can prove it
theorem prev_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) :
    prev (x :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) :=
  prev_cons_cons_eq' l x x z h rfl
#align list.prev_cons_cons_eq List.prev_cons_cons_eq

theorem prev_cons_cons_of_ne' (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x = z) :
    prev (y :: z :: l) x h = y := by
  cases l
  -- ⊢ prev [y, z] x h = y
  · simp [prev, hy, hz]
    -- 🎉 no goals
  · rw [prev, dif_neg hy, if_pos hz]
    -- 🎉 no goals
#align list.prev_cons_cons_of_ne' List.prev_cons_cons_of_ne'

theorem prev_cons_cons_of_ne (y : α) (h : x ∈ y :: x :: l) (hy : x ≠ y) :
    prev (y :: x :: l) x h = y :=
  prev_cons_cons_of_ne' _ _ _ _ _ hy rfl
#align list.prev_cons_cons_of_ne List.prev_cons_cons_of_ne

theorem prev_ne_cons_cons (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x ≠ z) :
    prev (y :: z :: l) x h = prev (z :: l) x (by simpa [hy] using h) := by
                                                 -- 🎉 no goals
  cases l
  -- ⊢ prev [y, z] x h = prev [z] x (_ : x ∈ [z])
  · simp [hy, hz] at h
    -- 🎉 no goals
  · rw [prev, dif_neg hy, if_neg hz]
    -- 🎉 no goals
#align list.prev_ne_cons_cons List.prev_ne_cons_cons

theorem next_mem (h : x ∈ l) : l.next x h ∈ l :=
  nextOr_mem (get_mem _ _ _)
#align list.next_mem List.next_mem

theorem prev_mem (h : x ∈ l) : l.prev x h ∈ l := by
  cases' l with hd tl
  -- ⊢ prev [] x h ∈ []
  · simp at h
    -- 🎉 no goals
  induction' tl with hd' tl hl generalizing hd
  -- ⊢ prev [hd] x h ∈ [hd]
  · simp
    -- 🎉 no goals
  · by_cases hx : x = hd
    -- ⊢ prev (hd :: hd' :: tl) x h ∈ hd :: hd' :: tl
    · simp only [hx, prev_cons_cons_eq]
      -- ⊢ getLast (hd' :: tl) (_ : hd' :: tl ≠ []) ∈ hd :: hd' :: tl
      exact mem_cons_of_mem _ (getLast_mem _)
      -- 🎉 no goals
    · rw [prev, dif_neg hx]
      -- ⊢ (if x = hd' then hd else prev (hd' :: tl) x (_ : x ∈ hd' :: tl)) ∈ hd :: hd' …
      split_ifs with hm
      -- ⊢ hd ∈ hd :: hd' :: tl
      · exact mem_cons_self _ _
        -- 🎉 no goals
      · exact mem_cons_of_mem _ (hl _ _)
        -- 🎉 no goals
#align list.prev_mem List.prev_mem

--Porting note: new theorem
theorem next_get : ∀ (l : List α) (_h : Nodup l) (i : Fin l.length),
    next l (l.get i) (get_mem _ _ _) = l.get ⟨(i + 1) % l.length,
      Nat.mod_lt _ (i.1.zero_le.trans_lt i.2)⟩
  | [], _, i => by simpa using i.2
                   -- 🎉 no goals
  | [_], _, _ => by simp
                    -- 🎉 no goals
  | x::y::l, _h, ⟨0, h0⟩ => by
    have h₁ : get (x :: y :: l) { val := 0, isLt := h0 } = x := by simp
    -- ⊢ next (x :: y :: l) (get (x :: y :: l) { val := 0, isLt := h0 }) (_ : get (x  …
    rw [next_cons_cons_eq' _ _ _ _ _ h₁]
    -- ⊢ y = get (x :: y :: l) { val := (↑{ val := 0, isLt := h0 } + 1) % length (x : …
    simp
    -- 🎉 no goals
  | x::y::l, hn, ⟨i+1, hi⟩ => by
    have hx' : (x :: y :: l).get ⟨i+1, hi⟩ ≠ x := by
      intro H
      suffices (i + 1 : ℕ) = 0 by simpa
      rw [nodup_iff_injective_get] at hn
      refine' Fin.veq_of_eq (@hn ⟨i + 1, hi⟩ ⟨0, by simp⟩ _)
      simpa using H
    have hi' : i ≤ l.length := Nat.le_of_lt_succ (Nat.succ_lt_succ_iff.1 hi)
    -- ⊢ next (x :: y :: l) (get (x :: y :: l) { val := i + 1, isLt := hi }) (_ : get …
    rcases hi'.eq_or_lt with (hi' | hi')
    -- ⊢ next (x :: y :: l) (get (x :: y :: l) { val := i + 1, isLt := hi }) (_ : get …
    · subst hi'
      -- ⊢ next (x :: y :: l) (get (x :: y :: l) { val := length l + 1, isLt := hi }) ( …
      rw [next_getLast_cons]
      · simp [hi', get]
        -- 🎉 no goals
      · rw [get_cons_succ]; exact get_mem _ _ _
        -- ⊢ get (y :: l) { val := length l, isLt := (_ : length l < length (y :: l)) } ∈ …
                            -- 🎉 no goals
      · exact hx'
        -- 🎉 no goals
      · simp [getLast_eq_get]
        -- 🎉 no goals
      · exact hn.of_cons
        -- 🎉 no goals
    · rw [next_ne_head_ne_getLast _ _ _ _ _ hx']
      simp only [get_cons_succ]
      rw [next_get (y::l), ← get_cons_succ (a := x)]
      congr
      dsimp
      rw [Nat.mod_eq_of_lt (Nat.succ_lt_succ_iff.2 hi'),
        Nat.mod_eq_of_lt (Nat.succ_lt_succ_iff.2 (Nat.succ_lt_succ_iff.2 hi'))]
      · simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ_iff.2 hi'), Nat.succ_eq_add_one, hi']
        -- 🎉 no goals
      · exact hn.of_cons
        -- 🎉 no goals
      · rw [getLast_eq_get]
        -- ⊢ get (x :: y :: l) { val := i + 1, isLt := hi } ≠ get (x :: y :: l) { val :=  …
        intro h
        -- ⊢ False
        have := nodup_iff_injective_get.1 hn h
        -- ⊢ False
        simp at this; simp [this] at hi'
        -- ⊢ False
                      -- 🎉 no goals
      · rw [get_cons_succ]; exact get_mem _ _ _
        -- ⊢ get (y :: l) { val := i, isLt := (_ : i < length (y :: l)) } ∈ y :: l
                            -- 🎉 no goals

set_option linter.deprecated false in
@[deprecated next_get]
theorem next_nthLe (l : List α) (h : Nodup l) (n : ℕ) (hn : n < l.length) :
    next l (l.nthLe n hn) (nthLe_mem _ _ _) =
      l.nthLe ((n + 1) % l.length) (Nat.mod_lt _ (n.zero_le.trans_lt hn)) :=
  next_get l h ⟨n, hn⟩
#align list.next_nth_le List.next_nthLe

set_option linter.deprecated false in
theorem prev_nthLe (l : List α) (h : Nodup l) (n : ℕ) (hn : n < l.length) :
    prev l (l.nthLe n hn) (nthLe_mem _ _ _) =
      l.nthLe ((n + (l.length - 1)) % l.length) (Nat.mod_lt _ (n.zero_le.trans_lt hn)) := by
  cases' l with x l
  -- ⊢ prev [] (nthLe [] n hn) (_ : nthLe [] n hn ∈ []) = nthLe [] ((n + (length [] …
  · simp at hn
    -- 🎉 no goals
  induction' l with y l hl generalizing n x
  -- ⊢ prev [x] (nthLe [x] n hn) (_ : nthLe [x] n hn ∈ [x]) = nthLe [x] ((n + (leng …
  · simp
    -- 🎉 no goals
  · rcases n with (_ | _ | n)
    · simp [Nat.add_succ_sub_one, add_zero, List.prev_cons_cons_eq, Nat.zero_eq, List.length,
        List.nthLe, Nat.succ_add_sub_one, zero_add, getLast_eq_get,
        Nat.mod_eq_of_lt (Nat.succ_lt_succ l.length.lt_succ_self)]
    · simp only [mem_cons, nodup_cons] at h
      -- ⊢ prev (x :: y :: l) (nthLe (x :: y :: l) (Nat.succ Nat.zero) hn) (_ : nthLe ( …
      push_neg at h
      -- ⊢ prev (x :: y :: l) (nthLe (x :: y :: l) (Nat.succ Nat.zero) hn) (_ : nthLe ( …
      simp only [List.prev_cons_cons_of_ne _ _ _ _ h.left.left.symm, Nat.zero_eq, List.length,
        List.nthLe, add_comm, eq_self_iff_true, Nat.succ_add_sub_one, Nat.mod_self, zero_add,
        List.get]
    · rw [prev_ne_cons_cons]
      · convert hl n.succ y h.of_cons (Nat.le_of_succ_le_succ hn) using 1
        -- ⊢ nthLe (x :: y :: l) ((Nat.succ (Nat.succ n) + (length (x :: y :: l) - 1)) %  …
        have : ∀ k hk, (y :: l).nthLe k hk = (x :: y :: l).nthLe (k + 1) (Nat.succ_lt_succ hk) := by
          intros
          simp [List.nthLe]
        rw [this]
        -- ⊢ nthLe (x :: y :: l) ((Nat.succ (Nat.succ n) + (length (x :: y :: l) - 1)) %  …
        congr
        -- ⊢ (Nat.succ (Nat.succ n) + (length (x :: y :: l) - 1)) % length (x :: y :: l)  …
        simp only [Nat.add_succ_sub_one, add_zero, length]
        -- ⊢ (Nat.succ (Nat.succ n) + (length l + 1)) % (length l + 1 + 1) = (Nat.succ n  …
        simp only [length, Nat.succ_lt_succ_iff] at hn
        -- ⊢ (Nat.succ (Nat.succ n) + (length l + 1)) % (length l + 1 + 1) = (Nat.succ n  …
        set k := l.length
        -- ⊢ (Nat.succ (Nat.succ n) + (k + 1)) % (k + 1 + 1) = (Nat.succ n + k) % (k + 1) …
        rw [Nat.succ_add, ← Nat.add_succ, Nat.add_mod_right, Nat.succ_add, ← Nat.add_succ _ k,
          Nat.add_mod_right, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
        · exact Nat.lt_succ_of_lt hn
          -- 🎉 no goals
        · exact Nat.succ_lt_succ (Nat.lt_succ_of_lt hn)
          -- 🎉 no goals
      · intro H
        -- ⊢ False
        suffices n.succ.succ = 0 by simpa
        -- ⊢ Nat.succ (Nat.succ n) = 0
        rw [nodup_iff_nthLe_inj] at h
        -- ⊢ Nat.succ (Nat.succ n) = 0
        refine' h _ _ hn Nat.succ_pos' _
        -- ⊢ nthLe (x :: y :: l) (Nat.succ (Nat.succ n)) hn = nthLe (x :: y :: l) 0 (_ :  …
        simpa using H
        -- 🎉 no goals
      · intro H
        -- ⊢ False
        suffices n.succ.succ = 1 by simpa
        -- ⊢ Nat.succ (Nat.succ n) = 1
        rw [nodup_iff_nthLe_inj] at h
        -- ⊢ Nat.succ (Nat.succ n) = 1
        refine' h _ _ hn (Nat.succ_lt_succ Nat.succ_pos') _
        -- ⊢ nthLe (x :: y :: l) (Nat.succ (Nat.succ n)) hn = nthLe (x :: y :: l) 1 (_ :  …
        simpa using H
        -- 🎉 no goals
#align list.prev_nth_le List.prev_nthLe

set_option linter.deprecated false in
theorem pmap_next_eq_rotate_one (h : Nodup l) : (l.pmap l.next fun _ h => h) = l.rotate 1 := by
  apply List.ext_nthLe
  -- ⊢ length (pmap (next l) l (_ : ∀ (x : α), x ∈ l → x ∈ l)) = length (rotate l 1)
  · simp
    -- 🎉 no goals
  · intros
    -- ⊢ nthLe (pmap (next l) l (_ : ∀ (x : α), x ∈ l → x ∈ l)) n✝ h₁✝ = nthLe (rotat …
    rw [nthLe_pmap, nthLe_rotate, next_nthLe _ h]
    -- 🎉 no goals
#align list.pmap_next_eq_rotate_one List.pmap_next_eq_rotate_one

set_option linter.deprecated false in
theorem pmap_prev_eq_rotate_length_sub_one (h : Nodup l) :
    (l.pmap l.prev fun _ h => h) = l.rotate (l.length - 1) := by
  apply List.ext_nthLe
  -- ⊢ length (pmap (prev l) l (_ : ∀ (x : α), x ∈ l → x ∈ l)) = length (rotate l ( …
  · simp
    -- 🎉 no goals
  · intro n hn hn'
    -- ⊢ nthLe (pmap (prev l) l (_ : ∀ (x : α), x ∈ l → x ∈ l)) n hn = nthLe (rotate  …
    rw [nthLe_rotate, nthLe_pmap, prev_nthLe _ h]
    -- 🎉 no goals
#align list.pmap_prev_eq_rotate_length_sub_one List.pmap_prev_eq_rotate_length_sub_one

set_option linter.deprecated false in
theorem prev_next (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    prev l (next l x hx) (next_mem _ _ _) = x := by
  obtain ⟨n, hn, rfl⟩ := nthLe_of_mem hx
  -- ⊢ prev l (next l (nthLe l n hn) hx) (_ : next l (nthLe l n hn) hx ∈ l) = nthLe …
  simp only [next_nthLe, prev_nthLe, h, Nat.mod_add_mod]
  -- ⊢ nthLe l ((n + 1 + (length l - 1)) % length l) (_ : (n + 1 + (length l - 1))  …
  cases' l with hd tl
  -- ⊢ nthLe [] ((n + 1 + (length [] - 1)) % length []) (_ : (n + 1 + (length [] -  …
  · simp at hx
    -- 🎉 no goals
  · have : (n + 1 + length tl) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc, add_comm 1, Nat.add_mod_right, Nat.mod_eq_of_lt hn]
    simp only [length_cons, Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.succ_eq_add_one, this]
    -- 🎉 no goals
#align list.prev_next List.prev_next

set_option linter.deprecated false in
theorem next_prev (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    next l (prev l x hx) (prev_mem _ _ _) = x := by
  obtain ⟨n, hn, rfl⟩ := nthLe_of_mem hx
  -- ⊢ next l (prev l (nthLe l n hn) hx) (_ : prev l (nthLe l n hn) hx ∈ l) = nthLe …
  simp only [next_nthLe, prev_nthLe, h, Nat.mod_add_mod]
  -- ⊢ nthLe l ((n + (length l - 1) + 1) % length l) (_ : (n + (length l - 1) + 1)  …
  cases' l with hd tl
  -- ⊢ nthLe [] ((n + (length [] - 1) + 1) % length []) (_ : (n + (length [] - 1) + …
  · simp at hx
    -- 🎉 no goals
  · have : (n + length tl + 1) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc, Nat.add_mod_right, Nat.mod_eq_of_lt hn]
    simp [this]
    -- 🎉 no goals
#align list.next_prev List.next_prev

set_option linter.deprecated false in
theorem prev_reverse_eq_next (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    prev l.reverse x (mem_reverse.mpr hx) = next l x hx := by
  obtain ⟨k, hk, rfl⟩ := nthLe_of_mem hx
  -- ⊢ prev (reverse l) (nthLe l k hk) (_ : nthLe l k hk ∈ reverse l) = next l (nth …
  have lpos : 0 < l.length := k.zero_le.trans_lt hk
  -- ⊢ prev (reverse l) (nthLe l k hk) (_ : nthLe l k hk ∈ reverse l) = next l (nth …
  have key : l.length - 1 - k < l.length :=
    (Nat.sub_le _ _).trans_lt (tsub_lt_self lpos Nat.succ_pos')
  rw [← nthLe_pmap l.next (fun _ h => h) (by simpa using hk)]
  -- ⊢ prev (reverse l) (nthLe l k hk) (_ : nthLe l k hk ∈ reverse l) = nthLe (pmap …
  simp_rw [← nthLe_reverse l k (key.trans_le (by simp)), pmap_next_eq_rotate_one _ h]
  -- ⊢ prev (reverse l) (nthLe (reverse l) (length l - 1 - k) (_ : length l - 1 - k …
  rw [← nthLe_pmap l.reverse.prev fun _ h => h]
  -- ⊢ nthLe (pmap (prev (reverse l)) (reverse l) (_ : ∀ (x : α), x ∈ reverse l → x …
  · simp_rw [pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), rotate_reverse,
      length_reverse, Nat.mod_eq_of_lt (tsub_lt_self lpos Nat.succ_pos'),
      tsub_tsub_cancel_of_le (Nat.succ_le_of_lt lpos)]
    rw [← nthLe_reverse]
    · simp [tsub_tsub_cancel_of_le (Nat.le_pred_of_lt hk)]
      -- 🎉 no goals
    · simpa using (Nat.sub_le _ _).trans_lt (tsub_lt_self lpos Nat.succ_pos')
      -- 🎉 no goals
    · simpa
      -- 🎉 no goals
#align list.prev_reverse_eq_next List.prev_reverse_eq_next

theorem next_reverse_eq_prev (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    next l.reverse x (mem_reverse.mpr hx) = prev l x hx := by
  convert (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm
  -- ⊢ l = reverse (reverse l)
  exact (reverse_reverse l).symm
  -- 🎉 no goals
#align list.next_reverse_eq_prev List.next_reverse_eq_prev

set_option linter.deprecated false in
theorem isRotated_next_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x ∈ l) :
    l.next x hx = l'.next x (h.mem_iff.mp hx) := by
  obtain ⟨k, hk, rfl⟩ := nthLe_of_mem hx
  -- ⊢ next l (nthLe l k hk) hx = next l' (nthLe l k hk) (_ : nthLe l k hk ∈ l')
  obtain ⟨n, rfl⟩ := id h
  -- ⊢ next l (nthLe l k hk) hx = next (rotate l n) (nthLe l k hk) (_ : nthLe l k h …
  rw [next_nthLe _ hn]
  -- ⊢ nthLe l ((k + 1) % length l) (_ : (k + 1) % length l < length l) = next (rot …
  simp_rw [← nthLe_rotate' _ n k]
  -- ⊢ nthLe l ((k + 1) % length l) (_ : (k + 1) % length l < length l) = next (rot …
  rw [next_nthLe _ (h.nodup_iff.mp hn), ← nthLe_rotate' _ n]
  -- ⊢ nthLe (rotate l n) ((length l - n % length l + (k + 1) % length l) % length  …
  simp [add_assoc]
  -- 🎉 no goals
#align list.is_rotated_next_eq List.isRotated_next_eq

theorem isRotated_prev_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x ∈ l) :
    l.prev x hx = l'.prev x (h.mem_iff.mp hx) := by
  rw [← next_reverse_eq_prev _ hn, ← next_reverse_eq_prev _ (h.nodup_iff.mp hn)]
  -- ⊢ next (reverse l) x (_ : x ∈ reverse l) = next (reverse l') x (_ : x ∈ revers …
  exact isRotated_next_eq h.reverse (nodup_reverse.mpr hn) _
  -- 🎉 no goals
#align list.is_rotated_prev_eq List.isRotated_prev_eq

end List

open List

/-- `Cycle α` is the quotient of `List α` by cyclic permutation.
Duplicates are allowed.
-/
def Cycle (α : Type*) : Type _ :=
  Quotient (IsRotated.setoid α)
#align cycle Cycle

namespace Cycle

variable {α : Type*}

--Porting note: new definition
/-- The coercion from `List α` to `Cycle α` -/
@[coe] def ofList : List α → Cycle α :=
  Quot.mk _

instance : Coe (List α) (Cycle α) :=
  ⟨ofList⟩

@[simp]
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = (l₂ : Cycle α) ↔ l₁ ~r l₂ :=
  @Quotient.eq _ (IsRotated.setoid _) _ _
#align cycle.coe_eq_coe Cycle.coe_eq_coe

@[simp]
theorem mk_eq_coe (l : List α) : Quot.mk _ l = (l : Cycle α) :=
  rfl
#align cycle.mk_eq_coe Cycle.mk_eq_coe

@[simp]
theorem mk''_eq_coe (l : List α) : Quotient.mk'' l = (l : Cycle α) :=
  rfl
#align cycle.mk'_eq_coe Cycle.mk''_eq_coe

theorem coe_cons_eq_coe_append (l : List α) (a : α) :
    (↑(a :: l) : Cycle α) = (↑(l ++ [a]) : Cycle α) :=
  Quot.sound ⟨1, by rw [rotate_cons_succ, rotate_zero]⟩
                    -- 🎉 no goals
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

/-- For consistency with `EmptyCollection (List α)`. -/
instance : EmptyCollection (Cycle α) :=
  ⟨nil⟩

@[simp]
theorem empty_eq : ∅ = @nil α :=
  rfl
#align cycle.empty_eq Cycle.empty_eq

instance : Inhabited (Cycle α) :=
  ⟨nil⟩

/-- An induction principle for `Cycle`. Use as `induction s using Cycle.induction_on`. -/
@[elab_as_elim]
theorem induction_on {C : Cycle α → Prop} (s : Cycle α) (H0 : C nil)
    (HI : ∀ (a) (l : List α), C ↑l → C ↑(a :: l)) : C s :=
  Quotient.inductionOn' s fun l => by
    refine List.recOn l ?_ ?_ <;> simp
    -- ⊢ C (Quotient.mk'' [])
                                  -- ⊢ C nil
                                  -- ⊢ ∀ (head : α) (tail : List α), C ↑tail → C ↑(head :: tail)
    assumption'
    -- 🎉 no goals
#align cycle.induction_on Cycle.induction_on

/-- For `x : α`, `s : Cycle α`, `x ∈ s` indicates that `x` occurs at least once in `s`. -/
def Mem (a : α) (s : Cycle α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun _ _ e => propext <| e.mem_iff
#align cycle.mem Cycle.Mem

instance : Membership α (Cycle α) :=
  ⟨Mem⟩

@[simp]
theorem mem_coe_iff {a : α} {l : List α} : a ∈ (↑l : Cycle α) ↔ a ∈ l :=
  Iff.rfl
#align cycle.mem_coe_iff Cycle.mem_coe_iff

@[simp]
theorem not_mem_nil : ∀ a, a ∉ @nil α :=
  List.not_mem_nil
#align cycle.not_mem_nil Cycle.not_mem_nil

instance [DecidableEq α] : DecidableEq (Cycle α) := fun s₁ s₂ =>
  Quotient.recOnSubsingleton₂' s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq''

instance [DecidableEq α] (x : α) (s : Cycle α) : Decidable (x ∈ s) :=
  Quotient.recOnSubsingleton' s fun l => show Decidable (x ∈ l) from inferInstance

/-- Reverse a `s : Cycle α` by reversing the underlying `List`. -/
nonrec def reverse (s : Cycle α) : Cycle α :=
  Quot.map reverse (fun _ _ => IsRotated.reverse) s
#align cycle.reverse Cycle.reverse

@[simp]
theorem reverse_coe (l : List α) : (l : Cycle α).reverse = l.reverse :=
  rfl
#align cycle.reverse_coe Cycle.reverse_coe

@[simp]
theorem mem_reverse_iff {a : α} {s : Cycle α} : a ∈ s.reverse ↔ a ∈ s :=
  Quot.inductionOn s fun _ => mem_reverse
#align cycle.mem_reverse_iff Cycle.mem_reverse_iff

@[simp]
theorem reverse_reverse (s : Cycle α) : s.reverse.reverse = s :=
  Quot.inductionOn s fun _ => by simp
                                 -- 🎉 no goals
#align cycle.reverse_reverse Cycle.reverse_reverse

@[simp]
theorem reverse_nil : nil.reverse = @nil α :=
  rfl
#align cycle.reverse_nil Cycle.reverse_nil

/-- The length of the `s : Cycle α`, which is the number of elements, counting duplicates. -/
def length (s : Cycle α) : ℕ :=
  Quot.liftOn s List.length fun _ _ e => e.perm.length_eq
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
  Quot.inductionOn s List.length_reverse
#align cycle.length_reverse Cycle.length_reverse

/-- A `s : Cycle α` that is at most one element. -/
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
  -- 🎉 no goals
#align cycle.subsingleton_reverse_iff Cycle.subsingleton_reverse_iff

theorem Subsingleton.congr {s : Cycle α} (h : Subsingleton s) :
    ∀ ⦃x⦄ (_hx : x ∈ s) ⦃y⦄ (_hy : y ∈ s), x = y := by
  induction' s using Quot.inductionOn with l
  -- ⊢ ∀ ⦃x : α⦄, x ∈ Quot.mk Setoid.r l → ∀ ⦃y : α⦄, y ∈ Quot.mk Setoid.r l → x = y
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe, le_iff_lt_or_eq, Nat.lt_add_one_iff,
    length_eq_zero, length_eq_one, Nat.not_lt_zero, false_or_iff] at h
  rcases h with (rfl | ⟨z, rfl⟩) <;> simp
  -- ⊢ ∀ ⦃x : α⦄, x ∈ Quot.mk Setoid.r [] → ∀ ⦃y : α⦄, y ∈ Quot.mk Setoid.r [] → x  …
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align cycle.subsingleton.congr Cycle.Subsingleton.congr

/-- A `s : Cycle α` that is made up of at least two unique elements. -/
def Nontrivial (s : Cycle α) : Prop :=
  ∃ (x y : α) (_h : x ≠ y), x ∈ s ∧ y ∈ s
#align cycle.nontrivial Cycle.Nontrivial

@[simp]
theorem nontrivial_coe_nodup_iff {l : List α} (hl : l.Nodup) :
    Nontrivial (l : Cycle α) ↔ 2 ≤ l.length := by
  rw [Nontrivial]
  -- ⊢ (∃ x y _h, x ∈ ↑l ∧ y ∈ ↑l) ↔ 2 ≤ List.length l
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · simp only [mem_cons, exists_prop, mem_coe_iff, List.length, Ne.def, Nat.succ_le_succ_iff,
      zero_le, iff_true_iff]
    refine' ⟨hd, hd', _, by simp⟩
    -- ⊢ ¬hd = hd'
    simp only [not_or, mem_cons, nodup_cons] at hl
    -- ⊢ ¬hd = hd'
    exact hl.left.left
    -- 🎉 no goals
#align cycle.nontrivial_coe_nodup_iff Cycle.nontrivial_coe_nodup_iff

@[simp]
theorem nontrivial_reverse_iff {s : Cycle α} : s.reverse.Nontrivial ↔ s.Nontrivial := by
  simp [Nontrivial]
  -- 🎉 no goals
#align cycle.nontrivial_reverse_iff Cycle.nontrivial_reverse_iff

theorem length_nontrivial {s : Cycle α} (h : Nontrivial s) : 2 ≤ length s := by
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  -- ⊢ 2 ≤ length s
  induction' s using Quot.inductionOn with l
  -- ⊢ 2 ≤ length (Quot.mk Setoid.r l)
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp at hx
    -- 🎉 no goals
  · simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy
    -- ⊢ 2 ≤ length (Quot.mk Setoid.r [hd])
    simp [hx, hy] at hxy
    -- 🎉 no goals
  · simp [Nat.succ_le_succ_iff]
    -- 🎉 no goals
#align cycle.length_nontrivial Cycle.length_nontrivial

/-- The `s : Cycle α` contains no duplicates. -/
nonrec def Nodup (s : Cycle α) : Prop :=
  Quot.liftOn s Nodup fun _l₁ _l₂ e => propext <| e.nodup_iff
#align cycle.nodup Cycle.Nodup

@[simp]
nonrec theorem nodup_nil : Nodup (@nil α) :=
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

theorem Subsingleton.nodup {s : Cycle α} (h : Subsingleton s) : Nodup s := by
  induction' s using Quot.inductionOn with l
  -- ⊢ Nodup (Quot.mk Setoid.r l)
  cases' l with hd tl
  -- ⊢ Nodup (Quot.mk Setoid.r [])
  · simp
    -- 🎉 no goals
  · have : tl = [] := by simpa [Subsingleton, length_eq_zero, Nat.succ_le_succ_iff] using h
    -- ⊢ Nodup (Quot.mk Setoid.r (hd :: tl))
    simp [this]
    -- 🎉 no goals
#align cycle.subsingleton.nodup Cycle.Subsingleton.nodup

theorem Nodup.nontrivial_iff {s : Cycle α} (h : Nodup s) : Nontrivial s ↔ ¬Subsingleton s := by
  rw [length_subsingleton_iff]
  -- ⊢ Nontrivial s ↔ ¬length s ≤ 1
  induction s using Quotient.inductionOn'
  -- ⊢ Nontrivial (Quotient.mk'' a✝) ↔ ¬length (Quotient.mk'' a✝) ≤ 1
  simp only [mk''_eq_coe, nodup_coe_iff] at h
  -- ⊢ Nontrivial (Quotient.mk'' a✝) ↔ ¬length (Quotient.mk'' a✝) ≤ 1
  simp [h, Nat.succ_le_iff]
  -- 🎉 no goals
#align cycle.nodup.nontrivial_iff Cycle.Nodup.nontrivial_iff

/-- The `s : Cycle α` as a `Multiset α`.
-/
def toMultiset (s : Cycle α) : Multiset α :=
  Quotient.liftOn' s (↑) fun _ _ h => Multiset.coe_eq_coe.mpr h.perm
#align cycle.to_multiset Cycle.toMultiset

@[simp]
theorem coe_toMultiset (l : List α) : (l : Cycle α).toMultiset = l :=
  rfl
#align cycle.coe_to_multiset Cycle.coe_toMultiset

@[simp]
theorem nil_toMultiset : nil.toMultiset = (0 : Multiset α) :=
  rfl
#align cycle.nil_to_multiset Cycle.nil_toMultiset

@[simp]
theorem card_toMultiset (s : Cycle α) : Multiset.card s.toMultiset = s.length :=
  Quotient.inductionOn' s (by simp)
                              -- 🎉 no goals
#align cycle.card_to_multiset Cycle.card_toMultiset

@[simp]
theorem toMultiset_eq_nil {s : Cycle α} : s.toMultiset = 0 ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)
                              -- 🎉 no goals
#align cycle.to_multiset_eq_nil Cycle.toMultiset_eq_nil

/-- The lift of `list.map`. -/
def map {β : Type*} (f : α → β) : Cycle α → Cycle β :=
  Quotient.map' (List.map f) fun _ _ h => h.map _
#align cycle.map Cycle.map

@[simp]
theorem map_nil {β : Type*} (f : α → β) : map f nil = nil :=
  rfl
#align cycle.map_nil Cycle.map_nil

@[simp]
theorem map_coe {β : Type*} (f : α → β) (l : List α) : map f ↑l = List.map f l :=
  rfl
#align cycle.map_coe Cycle.map_coe

@[simp]
theorem map_eq_nil {β : Type*} (f : α → β) (s : Cycle α) : map f s = nil ↔ s = nil :=
  Quotient.inductionOn' s (by simp)
                              -- 🎉 no goals
#align cycle.map_eq_nil Cycle.map_eq_nil

@[simp]
theorem mem_map {β : Type*} {f : α → β} {b : β} {s : Cycle α} :
    b ∈ s.map f ↔ ∃ a, a ∈ s ∧ f a = b :=
  Quotient.inductionOn' s (by simp)
                              -- 🎉 no goals
#align cycle.mem_map Cycle.mem_map

/-- The `Multiset` of lists that can make the cycle. -/
def lists (s : Cycle α) : Multiset (List α) :=
  Quotient.liftOn' s (fun l => (l.cyclicPermutations : Multiset (List α))) fun l₁ l₂ h => by
    simpa using h.cyclicPermutations.perm
    -- 🎉 no goals
#align cycle.lists Cycle.lists

@[simp]
theorem lists_coe (l : List α) : lists (l : Cycle α) = ↑l.cyclicPermutations :=
  rfl
#align cycle.lists_coe Cycle.lists_coe

@[simp]
theorem mem_lists_iff_coe_eq {s : Cycle α} {l : List α} : l ∈ s.lists ↔ (l : Cycle α) = s :=
  Quotient.inductionOn' s fun l => by
    rw [lists, Quotient.liftOn'_mk'']
    -- ⊢ l✝ ∈ ↑(cyclicPermutations l) ↔ ↑l✝ = Quotient.mk'' l
    simp
    -- 🎉 no goals
#align cycle.mem_lists_iff_coe_eq Cycle.mem_lists_iff_coe_eq

@[simp]
theorem lists_nil : lists (@nil α) = [([] : List α)] := by
  rw [nil, lists_coe, cyclicPermutations_nil]
  -- 🎉 no goals
#align cycle.lists_nil Cycle.lists_nil

section Decidable

variable [DecidableEq α]

/-- Auxiliary decidability algorithm for lists that contain at least two unique elements.
-/
def decidableNontrivialCoe : ∀ l : List α, Decidable (Nontrivial (l : Cycle α))
  | [] => isFalse (by simp [Nontrivial])
                      -- 🎉 no goals
  | [x] => isFalse (by simp [Nontrivial])
                       -- 🎉 no goals
  | x :: y :: l =>
    if h : x = y then
      @decidable_of_iff' _ (Nontrivial (x :: l : Cycle α)) (by simp [h, Nontrivial])
                                                               -- 🎉 no goals
        (decidableNontrivialCoe (x :: l))
    else isTrue ⟨x, y, h, by simp, by simp⟩
                             -- 🎉 no goals
                                      -- 🎉 no goals
#align cycle.decidable_nontrivial_coe Cycle.decidableNontrivialCoe

instance {s : Cycle α} : Decidable (Nontrivial s) :=
  Quot.recOnSubsingleton' s decidableNontrivialCoe

instance {s : Cycle α} : Decidable (Nodup s) :=
  Quot.recOnSubsingleton' s List.nodupDecidable

instance fintypeNodupCycle [Fintype α] : Fintype { s : Cycle α // s.Nodup } :=
  Fintype.ofSurjective (fun l : { l : List α // l.Nodup } => ⟨l.val, by simpa using l.prop⟩)
                                                                        -- 🎉 no goals
    fun ⟨s, hs⟩ => by
    induction' s using Quotient.inductionOn' with s hs
    -- ⊢ ∃ a, (fun l => { val := ↑↑l, property := (_ : Nodup ↑↑l) }) a = { val := Quo …
    exact ⟨⟨s, hs⟩, by simp⟩
    -- 🎉 no goals
#align cycle.fintype_nodup_cycle Cycle.fintypeNodupCycle

instance fintypeNodupNontrivialCycle [Fintype α] :
    Fintype { s : Cycle α // s.Nodup ∧ s.Nontrivial } :=
  Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.Nodup }).map (Function.Embedding.subtype _)).filter
      Cycle.Nontrivial)
    (by simp)
        -- 🎉 no goals
#align cycle.fintype_nodup_nontrivial_cycle Cycle.fintypeNodupNontrivialCycle

/-- The `s : Cycle α` as a `Finset α`. -/
def toFinset (s : Cycle α) : Finset α :=
  s.toMultiset.toFinset
#align cycle.to_finset Cycle.toFinset

@[simp]
theorem toFinset_toMultiset (s : Cycle α) : s.toMultiset.toFinset = s.toFinset :=
  rfl
#align cycle.to_finset_to_multiset Cycle.toFinset_toMultiset

@[simp]
theorem coe_toFinset (l : List α) : (l : Cycle α).toFinset = l.toFinset :=
  rfl
#align cycle.coe_to_finset Cycle.coe_toFinset

@[simp]
theorem nil_toFinset : (@nil α).toFinset = ∅ :=
  rfl
#align cycle.nil_to_finset Cycle.nil_toFinset

@[simp]
theorem toFinset_eq_nil {s : Cycle α} : s.toFinset = ∅ ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)
                              -- 🎉 no goals
#align cycle.to_finset_eq_nil Cycle.toFinset_eq_nil

/-- Given a `s : Cycle α` such that `Nodup s`, retrieve the next element after `x ∈ s`. -/
nonrec def next : ∀ (s : Cycle α) (_hs : Nodup s) (x : α) (_hx : x ∈ s), α := fun s =>
  Quot.hrecOn (motive := fun (s : Cycle α) => ∀ (_hs : Cycle.Nodup s) (x : α) (_hx : x ∈ s), α) s
  (fun l _hn x hx => next l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ _he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by rw [eq_of_heq hxy]; simpa [eq_of_heq hxy] using h.mem_iff))
                                      -- ⊢ y ∈ Quot.mk Setoid.r l₁ ↔ y ∈ Quot.mk Setoid.r l₂
                                                          -- 🎉 no goals
  fun hm hm' he' => heq_of_eq
    (by rw [heq_iff_eq] at hxy; subst x; simpa using isRotated_next_eq h h₁ _)
        -- ⊢ (fun l _hn x hx => List.next l x hx) l₁ h₁ x hm = (fun l _hn x hx => List.ne …
                                -- ⊢ (fun l _hn x hx => List.next l x hx) l₁ h₁ y hm = (fun l _hn x hx => List.ne …
                                         -- 🎉 no goals
#align cycle.next Cycle.next

/-- Given a `s : Cycle α` such that `Nodup s`, retrieve the previous element before `x ∈ s`. -/
nonrec def prev : ∀ (s : Cycle α) (_hs : Nodup s) (x : α) (_hx : x ∈ s), α := fun s =>
  Quot.hrecOn (motive := fun (s : Cycle α) => ∀ (_hs : Cycle.Nodup s) (x : α) (_hx : x ∈ s), α) s
  (fun l _hn x hx => prev l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ _he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by rw [eq_of_heq hxy]; simpa [eq_of_heq hxy] using h.mem_iff))
                                      -- ⊢ y ∈ Quot.mk Setoid.r l₁ ↔ y ∈ Quot.mk Setoid.r l₂
                                                          -- 🎉 no goals
  fun hm hm' he' => heq_of_eq
    (by rw [heq_iff_eq] at hxy; subst x; simpa using isRotated_prev_eq h h₁ _)
        -- ⊢ (fun l _hn x hx => List.prev l x hx) l₁ h₁ x hm = (fun l _hn x hx => List.pr …
                                -- ⊢ (fun l _hn x hx => List.prev l x hx) l₁ h₁ y hm = (fun l _hn x hx => List.pr …
                                         -- 🎉 no goals
#align cycle.prev Cycle.prev

--Porting note: removed `simp` and added `prev_reverse_eq_next'` with `simp` attribute
nonrec theorem prev_reverse_eq_next (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.reverse.prev (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.next hs x hx :=
  Quotient.inductionOn' s prev_reverse_eq_next
#align cycle.prev_reverse_eq_next Cycle.prev_reverse_eq_next

--Porting note: new theorem
@[simp]
nonrec theorem prev_reverse_eq_next' (s : Cycle α) (hs : Nodup s.reverse) (x : α)
    (hx : x ∈ s.reverse) :
    s.reverse.prev hs x hx = s.next (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx) :=
  prev_reverse_eq_next s (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx)

--Porting note: removed `simp` and added `next_reverse_eq_prev'` with `simp` attribute
theorem next_reverse_eq_prev (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) :
    s.reverse.next (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.prev hs x hx := by
  simp [← prev_reverse_eq_next]
  -- 🎉 no goals
#align cycle.next_reverse_eq_prev Cycle.next_reverse_eq_prev

--Porting note: new theorem
@[simp]
theorem next_reverse_eq_prev' (s : Cycle α) (hs : Nodup s.reverse) (x : α) (hx : x ∈ s.reverse) :
    s.reverse.next hs x hx = s.prev (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx) := by
  simp [← prev_reverse_eq_next]
  -- 🎉 no goals

@[simp]
nonrec theorem next_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) : s.next hs x hx ∈ s := by
  induction s using Quot.inductionOn
  -- ⊢ next (Quot.mk Setoid.r a✝) hs x hx ∈ Quot.mk Setoid.r a✝
  apply next_mem; assumption
  -- ⊢ x ∈ a✝
                  -- 🎉 no goals
#align cycle.next_mem Cycle.next_mem

theorem prev_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) : s.prev hs x hx ∈ s := by
  rw [← next_reverse_eq_prev, ← mem_reverse_iff]
  -- ⊢ next (reverse s) (_ : Nodup (reverse s)) x (_ : x ∈ reverse s) ∈ reverse s
  apply next_mem
  -- 🎉 no goals
#align cycle.prev_mem Cycle.prev_mem

@[simp]
nonrec theorem prev_next (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.prev hs (s.next hs x hx) (next_mem s hs x hx) = x :=
  Quotient.inductionOn' s prev_next
#align cycle.prev_next Cycle.prev_next

@[simp]
nonrec theorem next_prev (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.next hs (s.prev hs x hx) (prev_mem s hs x hx) = x :=
  Quotient.inductionOn' s next_prev
#align cycle.next_prev Cycle.next_prev

end Decidable

/-- We define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.
-/
unsafe instance [Repr α] : Repr (Cycle α) :=
  ⟨fun s _ => "c[" ++ Std.Format.joinSep (s.map repr).lists.unquot.head! ", " ++ "]"⟩

/-- `chain R s` means that `R` holds between adjacent elements of `s`.

`chain R ([a, b, c] : Cycle α) ↔ R a b ∧ R b c ∧ R c a` -/
nonrec def Chain (r : α → α → Prop) (c : Cycle α) : Prop :=
  Quotient.liftOn' c
    (fun l =>
      match l with
      | [] => True
      | a :: m => Chain r a (m ++ [a]))
    fun a b hab =>
    propext <| by
      cases' a with a l <;> cases' b with b m
      · rfl
        -- 🎉 no goals
      · have := isRotated_nil_iff'.1 hab
        -- ⊢ (fun l =>
        contradiction
        -- 🎉 no goals
      · have := isRotated_nil_iff.1 hab
        -- ⊢ (fun l =>
        contradiction
        -- 🎉 no goals
      · dsimp only
        -- ⊢ List.Chain r a (l ++ [a]) ↔ List.Chain r b (m ++ [b])
        cases' hab with n hn
        -- ⊢ List.Chain r a (l ++ [a]) ↔ List.Chain r b (m ++ [b])
        induction' n with d hd generalizing a b l m
        -- ⊢ List.Chain r a (l ++ [a]) ↔ List.Chain r b (m ++ [b])
        · simp only [Nat.zero_eq, rotate_zero, cons.injEq] at hn
          -- ⊢ List.Chain r a (l ++ [a]) ↔ List.Chain r b (m ++ [b])
          rw [hn.1, hn.2]
          -- 🎉 no goals
        · cases' l with c s
          -- ⊢ List.Chain r a ([] ++ [a]) ↔ List.Chain r b (m ++ [b])
          · simp only [rotate_cons_succ, nil_append, rotate_singleton, cons.injEq] at hn
            -- ⊢ List.Chain r a ([] ++ [a]) ↔ List.Chain r b (m ++ [b])
            rw [hn.1, hn.2]
            -- 🎉 no goals
          · rw [Nat.succ_eq_one_add, ← rotate_rotate, rotate_cons_succ, rotate_zero,
              cons_append] at hn
            rw [← hd c _ _ _ hn]
            -- ⊢ List.Chain r a (c :: s ++ [a]) ↔ List.Chain r c (s ++ [a] ++ [c])
            simp [and_comm]
            -- 🎉 no goals
#align cycle.chain Cycle.Chain

@[simp]
theorem Chain.nil (r : α → α → Prop) : Cycle.Chain r (@nil α) := by trivial
                                                                    -- 🎉 no goals
#align cycle.chain.nil Cycle.Chain.nil

@[simp]
theorem chain_coe_cons (r : α → α → Prop) (a : α) (l : List α) :
    Chain r (a :: l) ↔ List.Chain r a (l ++ [a]) :=
  Iff.rfl
#align cycle.chain_coe_cons Cycle.chain_coe_cons

--@[simp] Porting note: `simp` can prove it
theorem chain_singleton (r : α → α → Prop) (a : α) : Chain r [a] ↔ r a a := by
  rw [chain_coe_cons, nil_append, List.chain_singleton]
  -- 🎉 no goals
#align cycle.chain_singleton Cycle.chain_singleton

theorem chain_ne_nil (r : α → α → Prop) {l : List α} :
    ∀ hl : l ≠ [], Chain r l ↔ List.Chain r (getLast l hl) l :=
  l.reverseRecOn (fun hm => hm.irrefl.elim) (by
    intro m a _H _
    -- ⊢ Chain r ↑(m ++ [a]) ↔ List.Chain r (getLast (m ++ [a]) hl✝) (m ++ [a])
    rw [← coe_cons_eq_coe_append, chain_coe_cons, getLast_append_singleton])
    -- 🎉 no goals
#align cycle.chain_ne_nil Cycle.chain_ne_nil

theorem chain_map {β : Type*} {r : α → α → Prop} (f : β → α) {s : Cycle β} :
    Chain r (s.map f) ↔ Chain (fun a b => r (f a) (f b)) s :=
  Quotient.inductionOn' s fun l => by
    cases' l with a l
    -- ⊢ Chain r (map f (Quotient.mk'' [])) ↔ Chain (fun a b => r (f a) (f b)) (Quoti …
    rfl
    -- ⊢ Chain r (map f (Quotient.mk'' (a :: l))) ↔ Chain (fun a b => r (f a) (f b))  …
    dsimp only [Chain, ← mk''_eq_coe, Quotient.liftOn'_mk'', Cycle.map, Quotient.map', Quot.map,
      Quotient.mk'', Quotient.liftOn', Quotient.liftOn, Quot.liftOn_mk, List.map]
    rw [← concat_eq_append, ← List.map_concat, List.chain_map f]
    -- ⊢ List.Chain (fun a b => r (f a) (f b)) a (concat l a) ↔ List.Chain (fun a b = …
    simp
    -- 🎉 no goals
#align cycle.chain_map Cycle.chain_map

nonrec theorem chain_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    Chain r (List.range n.succ) ↔ r n 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ, ← coe_cons_eq_coe_append, chain_coe_cons, ← range_succ, chain_range_succ]
  -- 🎉 no goals
#align cycle.chain_range_succ Cycle.chain_range_succ

variable {r : α → α → Prop} {s : Cycle α}

theorem Chain.imp {r₁ r₂ : α → α → Prop} (H : ∀ a b, r₁ a b → r₂ a b) (p : Chain r₁ s) :
    Chain r₂ s := by
  induction s using Cycle.induction_on
  -- ⊢ Chain r₂ Cycle.nil
  · triv
    -- 🎉 no goals
  · rw [chain_coe_cons] at p ⊢
    -- ⊢ List.Chain r₂ a✝¹ (l✝ ++ [a✝¹])
    exact p.imp H
    -- 🎉 no goals
#align cycle.chain.imp Cycle.Chain.imp

/-- As a function from a relation to a predicate, `chain` is monotonic. -/
theorem chain_mono : Monotone (Chain : (α → α → Prop) → Cycle α → Prop) := fun _a _b hab _s =>
  Chain.imp hab
#align cycle.chain_mono Cycle.chain_mono

theorem chain_of_pairwise : (∀ a ∈ s, ∀ b ∈ s, r a b) → Chain r s := by
  induction' s using Cycle.induction_on with a l _
  -- ⊢ (∀ (a : α), a ∈ nil → ∀ (b : α), b ∈ nil → r a b) → Chain r nil
  exact fun _ => Cycle.Chain.nil r
  -- ⊢ (∀ (a_1 : α), a_1 ∈ ↑(a :: l) → ∀ (b : α), b ∈ ↑(a :: l) → r a_1 b) → Chain  …
  intro hs
  -- ⊢ Chain r ↑(a :: l)
  have Ha : a ∈ (a :: l : Cycle α) := by simp
  -- ⊢ Chain r ↑(a :: l)
  have Hl : ∀ {b} (_hb : b ∈ l), b ∈ (a :: l : Cycle α) := @fun b hb => by simp [hb]
  -- ⊢ Chain r ↑(a :: l)
  rw [Cycle.chain_coe_cons]
  -- ⊢ List.Chain r a (l ++ [a])
  apply Pairwise.chain
  -- ⊢ List.Pairwise r (a :: (l ++ [a]))
  rw [pairwise_cons]
  -- ⊢ (∀ (a' : α), a' ∈ l ++ [a] → r a a') ∧ List.Pairwise r (l ++ [a])
  refine'
    ⟨fun b hb => _,
      pairwise_append.2
        ⟨pairwise_of_forall_mem_list fun b hb c hc => hs b (Hl hb) c (Hl hc),
          pairwise_singleton r a, fun b hb c hc => _⟩⟩
  · rw [mem_append] at hb
    -- ⊢ r a b
    cases' hb with hb hb
    -- ⊢ r a b
    · exact hs a Ha b (Hl hb)
      -- 🎉 no goals
    · rw [mem_singleton] at hb
      -- ⊢ r a b
      rw [hb]
      -- ⊢ r a a
      exact hs a Ha a Ha
      -- 🎉 no goals
  · rw [mem_singleton] at hc
    -- ⊢ r b c
    rw [hc]
    -- ⊢ r b a
    exact hs b (Hl hb) a Ha
    -- 🎉 no goals
#align cycle.chain_of_pairwise Cycle.chain_of_pairwise

theorem chain_iff_pairwise [IsTrans α r] : Chain r s ↔ ∀ a ∈ s, ∀ b ∈ s, r a b :=
  ⟨by
    induction' s using Cycle.induction_on with a l _
    -- ⊢ Chain r nil → ∀ (a : α), a ∈ nil → ∀ (b : α), b ∈ nil → r a b
    · exact fun _ b hb => (not_mem_nil _ hb).elim
      -- 🎉 no goals
    intro hs b hb c hc
    -- ⊢ r b c
    rw [Cycle.chain_coe_cons, List.chain_iff_pairwise] at hs
    -- ⊢ r b c
    simp only [pairwise_append, pairwise_cons, mem_append, mem_singleton, List.not_mem_nil,
      IsEmpty.forall_iff, imp_true_iff, Pairwise.nil, forall_eq, true_and_iff] at hs
    simp only [mem_coe_iff, mem_cons] at hb hc
    -- ⊢ r b c
    rcases hb with (rfl | hb) <;> rcases hc with (rfl | hc)
    -- ⊢ r b c
                                  -- ⊢ r c c
                                  -- ⊢ r b c
    · exact hs.1 c (Or.inr rfl)
      -- 🎉 no goals
    · exact hs.1 c (Or.inl hc)
      -- 🎉 no goals
    · exact hs.2.2 b hb
      -- 🎉 no goals
    · exact _root_.trans (hs.2.2 b hb) (hs.1 c (Or.inl hc)), Cycle.chain_of_pairwise⟩
      -- 🎉 no goals
#align cycle.chain_iff_pairwise Cycle.chain_iff_pairwise

theorem Chain.eq_nil_of_irrefl [IsTrans α r] [IsIrrefl α r] (h : Chain r s) : s = Cycle.nil := by
  induction' s using Cycle.induction_on with a l _ h
  -- ⊢ Cycle.nil = Cycle.nil
  · rfl
    -- 🎉 no goals
  · have ha := mem_cons_self a l
    -- ⊢ ↑(a :: l) = Cycle.nil
    exact (irrefl_of r a <| chain_iff_pairwise.1 h a ha a ha).elim
    -- 🎉 no goals
#align cycle.chain.eq_nil_of_irrefl Cycle.Chain.eq_nil_of_irrefl

theorem Chain.eq_nil_of_well_founded [IsWellFounded α r] (h : Chain r s) : s = Cycle.nil :=
  Chain.eq_nil_of_irrefl <| h.imp fun _ _ => Relation.TransGen.single
#align cycle.chain.eq_nil_of_well_founded Cycle.Chain.eq_nil_of_well_founded

theorem forall_eq_of_chain [IsTrans α r] [IsAntisymm α r] (hs : Chain r s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : a = b := by
  rw [chain_iff_pairwise] at hs
  -- ⊢ a = b
  exact antisymm (hs a ha b hb) (hs b hb a ha)
  -- 🎉 no goals
#align cycle.forall_eq_of_chain Cycle.forall_eq_of_chain

end Cycle
