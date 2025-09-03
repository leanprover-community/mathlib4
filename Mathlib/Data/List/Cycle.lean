/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.OfMap

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

assert_not_exists MonoidWithZero

namespace List

variable {α : Type*} [DecidableEq α]

/-- Return the `z` such that `x :: z :: _` appears in `xs`, or `default` if there is no such `z`. -/
def nextOr : ∀ (_ : List α) (_ _ : α), α
  | [], _, default => default
  | [_], _, default => default
  -- Handles the not-found and the wraparound case
  | y :: z :: xs, x, default => if x = y then z else nextOr (z :: xs) x default

@[simp]
theorem nextOr_nil (x d : α) : nextOr [] x d = d :=
  rfl

@[simp]
theorem nextOr_singleton (x y d : α) : nextOr [y] x d = d :=
  rfl

@[simp]
theorem nextOr_self_cons_cons (xs : List α) (x y d : α) : nextOr (x :: y :: xs) x d = y :=
  if_pos rfl

theorem nextOr_cons_of_ne (xs : List α) (y x d : α) (h : x ≠ y) :
    nextOr (y :: xs) x d = nextOr xs x d := by
  rcases xs with - | ⟨z, zs⟩
  · rfl
  · exact if_neg h

/-- `nextOr` does not depend on the default value, if the next value appears. -/
theorem nextOr_eq_nextOr_of_mem_of_ne (xs : List α) (x d d' : α) (x_mem : x ∈ xs)
    (x_ne : x ≠ xs.getLast (ne_nil_of_mem x_mem)) : nextOr xs x d = nextOr xs x d' := by
  induction' xs with y ys IH
  · cases x_mem
  rcases ys with - | ⟨z, zs⟩
  · simp at x_mem x_ne
    contradiction
  by_cases h : x = y
  · rw [h, nextOr_self_cons_cons, nextOr_self_cons_cons]
  · rw [nextOr, nextOr, IH]
    · simpa [h] using x_mem
    · simpa using x_ne

theorem mem_of_nextOr_ne {xs : List α} {x d : α} (h : nextOr xs x d ≠ d) : x ∈ xs := by
  induction' xs with y ys IH
  · simp at h
  rcases ys with - | ⟨z, zs⟩
  · simp at h
  · by_cases hx : x = y
    · simp [hx]
    · rw [nextOr_cons_of_ne _ _ _ _ hx] at h
      simpa [hx] using IH h

theorem nextOr_concat {xs : List α} {x : α} (d : α) (h : x ∉ xs) : nextOr (xs ++ [x]) x d = d := by
  induction' xs with z zs IH
  · simp
  · obtain ⟨hz, hzs⟩ := not_or.mp (mt mem_cons.2 h)
    rw [cons_append, nextOr_cons_of_ne _ _ _ _ hz, IH hzs]

theorem nextOr_mem {xs : List α} {x d : α} (hd : d ∈ xs) : nextOr xs x d ∈ xs := by
  revert hd
  suffices ∀ xs' : List α, (∀ x ∈ xs, x ∈ xs') → d ∈ xs' → nextOr xs x d ∈ xs' by
    exact this xs fun _ => id
  intro xs' hxs' hd
  induction' xs with y ys ih
  · exact hd
  rcases ys with - | ⟨z, zs⟩
  · exact hd
  rw [nextOr]
  split_ifs with h
  · exact hxs' _ (mem_cons_of_mem _ mem_cons_self)
  · exact ih fun _ h => hxs' _ (mem_cons_of_mem _ h)

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

/-- Given an element `x : α` of `l : List α` such that `x ∈ l`, get the previous
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.

* `prev [1, 2, 3] 2 _ = 1`
* `prev [1, 2, 3] 1 _ = 3`
* `prev [1, 2, 3, 2, 4] 2 _ = 1`
* `prev [1, 2, 3, 4, 2] 2 _ = 1`
* `prev [1, 1, 2] 1 _ = 2`
-/
def prev : ∀ l : List α, ∀ x ∈ l, α
  | [], _, h => by simp at h
  | [y], _, _ => y
  | y :: z :: xs, x, h =>
    if hx : x = y then getLast (z :: xs) (cons_ne_nil _ _)
    else if x = z then y else prev (z :: xs) x (by simpa [hx] using h)

variable (l : List α) (x : α)

@[simp]
theorem next_singleton (x y : α) (h : x ∈ [y]) : next [y] x h = y :=
  rfl

@[simp]
theorem prev_singleton (x y : α) (h : x ∈ [y]) : prev [y] x h = y :=
  rfl

theorem next_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
    next (y :: z :: l) x h = z := by rw [next, nextOr, if_pos hx]

@[simp]
theorem next_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) : next (x :: z :: l) x h = z :=
  next_cons_cons_eq' l x x z h rfl

theorem next_ne_head_ne_getLast (h : x ∈ l) (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x ≠ getLast (y :: l) (cons_ne_nil _ _)) :
    next (y :: l) x h = next l x (by simpa [hy] using h) := by
  rw [next, next, nextOr_cons_of_ne _ _ _ _ hy, nextOr_eq_nextOr_of_mem_of_ne]
  · assumption
  · rwa [getLast_cons] at hx

theorem next_cons_concat (y : α) (hy : x ≠ y) (hx : x ∉ l)
    (h : x ∈ y :: l ++ [x] := mem_append_right _ (mem_singleton_self x)) :
    next (y :: l ++ [x]) x h = y := by
  rw [next, nextOr_concat]
  · simp
  · simp [hy, hx]

theorem next_getLast_cons (h : x ∈ l) (y : α) (h : x ∈ y :: l) (hy : x ≠ y)
    (hx : x = getLast (y :: l) (cons_ne_nil _ _)) (hl : Nodup l) : next (y :: l) x h = y := by
  rw [next, get, ← dropLast_append_getLast (cons_ne_nil y l), hx, nextOr_concat]
  subst hx
  intro H
  obtain ⟨_ | k, hk, hk'⟩ := getElem_of_mem H
  · rw [← Option.some_inj] at hk'
    rw [← getElem?_eq_getElem, dropLast_eq_take, getElem?_take_of_lt, getElem?_cons_zero,
      Option.some_inj] at hk'
    · exact hy (Eq.symm hk')
    rw [length_cons]
    exact length_pos_of_mem (by assumption)
  suffices k + 1 = l.length by simp [this] at hk
  rcases l with - | ⟨hd, tl⟩
  · simp at hk
  · rw [nodup_iff_injective_get] at hl
    rw [length, Nat.succ_inj]
    refine Fin.val_eq_of_eq <| @hl ⟨k, Nat.lt_of_succ_lt <| by simpa using hk⟩
      ⟨tl.length, by simp⟩ ?_
    rw [← Option.some_inj] at hk'
    rw [← getElem?_eq_getElem, dropLast_eq_take, getElem?_take_of_lt, getElem?_cons_succ,
      getElem?_eq_getElem, Option.some_inj] at hk'
    · rw [get_eq_getElem, hk']
      simp only [getLast_eq_getElem, length_cons, Nat.succ_sub_succ_eq_sub,
        Nat.sub_zero, get_eq_getElem, getElem_cons_succ]
    simpa using hk

theorem prev_getLast_cons' (y : α) (hxy : x ∈ y :: l) (hx : x = y) :
    prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _) := by cases l <;> simp [prev, hx]

@[simp]
theorem prev_getLast_cons (h : x ∈ x :: l) :
    prev (x :: l) x h = getLast (x :: l) (cons_ne_nil _ _) :=
  prev_getLast_cons' l x x h rfl

theorem prev_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
    prev (y :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) := by rw [prev, dif_pos hx]

theorem prev_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) :
    prev (x :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) :=
  prev_cons_cons_eq' l x x z h rfl

theorem prev_cons_cons_of_ne' (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x = z) :
    prev (y :: z :: l) x h = y := by
  cases l
  · simp [prev, hz]
  · rw [prev, dif_neg hy, if_pos hz]

theorem prev_cons_cons_of_ne (y : α) (h : x ∈ y :: x :: l) (hy : x ≠ y) :
    prev (y :: x :: l) x h = y :=
  prev_cons_cons_of_ne' _ _ _ _ _ hy rfl

theorem prev_ne_cons_cons (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x ≠ z) :
    prev (y :: z :: l) x h = prev (z :: l) x (by simpa [hy] using h) := by
  cases l
  · simp [hy, hz] at h
  · rw [prev, dif_neg hy, if_neg hz]

theorem next_mem (h : x ∈ l) : l.next x h ∈ l :=
  nextOr_mem (get_mem _ _)

theorem prev_mem (h : x ∈ l) : l.prev x h ∈ l := by
  rcases l with - | ⟨hd, tl⟩
  · simp at h
  induction' tl with hd' tl hl generalizing hd
  · simp
  · by_cases hx : x = hd
    · simp only [hx, prev_cons_cons_eq]
      exact mem_cons_of_mem _ (getLast_mem _)
    · rw [prev, dif_neg hx]
      split_ifs with hm
      · exact mem_cons_self
      · exact mem_cons_of_mem _ (hl _ _)

theorem next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length) :
    next l l[i] (get_mem _ _) =
      (l[(i + 1) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt hi))) :=
  match l, h, i, hi with
  | [], _, i, hi => by simp at hi
  | [_], _, _, _ => by simp
  | x::y::l, _h, 0, h0 => by
    have h₁ : (x :: y :: l)[0] = x := by simp
    rw [next_cons_cons_eq' _ _ _ _ _ h₁]
    simp
  | x::y::l, hn, i+1, hi => by
    have hx' : (x :: y :: l)[i+1] ≠ x := by
      intro H
      suffices (i + 1 : ℕ) = 0 by simpa
      rw [nodup_iff_injective_get] at hn
      refine Fin.val_eq_of_eq (@hn ⟨i + 1, hi⟩ ⟨0, by simp⟩ ?_)
      simpa using H
    have hi' : i ≤ l.length := Nat.le_of_lt_succ (Nat.succ_lt_succ_iff.1 hi)
    rcases hi'.eq_or_lt with (hi' | hi')
    · subst hi'
      rw [next_getLast_cons]
      · simp
      · rw [getElem_cons_succ]; exact get_mem _ _
      · exact hx'
      · simp [getLast_eq_getElem]
      · exact hn.of_cons
    · rw [next_ne_head_ne_getLast _ _ _ _ _ hx']
      · simp only [getElem_cons_succ]
        rw [next_getElem (y::l), ← getElem_cons_succ (a := x)]
        · congr
          dsimp
          rw [Nat.mod_eq_of_lt (Nat.succ_lt_succ_iff.2 hi'),
            Nat.mod_eq_of_lt (Nat.succ_lt_succ_iff.2 (Nat.succ_lt_succ_iff.2 hi'))]
        · simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ_iff.2 hi'), hi']
        · exact hn.of_cons
      · rw [getLast_eq_getElem]
        intro h
        have := nodup_iff_injective_get.1 hn h
        simp at this; simp [this] at hi'
      · rw [getElem_cons_succ]; exact get_mem _ _

@[deprecated (since := "2025-02-15")] alias next_get := next_getElem

theorem prev_getElem (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length) :
    prev l l[i] (get_mem _ _) =
      (l[(i + (l.length - 1)) % l.length]'(Nat.mod_lt _ (by omega))) :=
  match l with
  | [] => by simp at hi
  | x::l => by
    induction l generalizing i x with
    | nil => simp
    | cons y l hl =>
      rcases i with (_ | _ | i)
      · simp [getLast_eq_getElem]
      · simp only [mem_cons, nodup_cons] at h
        push_neg at h
        simp only [zero_add, getElem_cons_succ, getElem_cons_zero,
          List.prev_cons_cons_of_ne _ _ _ _ h.left.left.symm, length, add_comm,
          Nat.add_sub_cancel_left, Nat.mod_self]
      · rw [prev_ne_cons_cons]
        · convert hl i.succ y h.of_cons (Nat.le_of_succ_le_succ hi) using 1
          have : ∀ k hk, (y :: l)[k] = (x :: y :: l)[k + 1]'(Nat.succ_lt_succ hk) := by
            simp
          rw [this]
          congr
          simp only [Nat.add_succ_sub_one, add_zero, length]
          simp only [length, Nat.succ_lt_succ_iff] at hi
          set k := l.length
          rw [Nat.succ_add, ← Nat.add_succ, Nat.add_mod_right, Nat.succ_add, ← Nat.add_succ _ k,
            Nat.add_mod_right, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
          · exact Nat.lt_succ_of_lt hi
          · exact Nat.succ_lt_succ (Nat.lt_succ_of_lt hi)
        · intro H
          suffices i.succ.succ = 0 by simpa
          suffices Fin.mk _ hi = ⟨0, by omega⟩ by rwa [Fin.mk.inj_iff] at this
          rw [nodup_iff_injective_get] at h
          apply h; rw [← H]; simp
        · intro H
          suffices i.succ.succ = 1 by simpa
          suffices Fin.mk _ hi = ⟨1, by omega⟩ by rwa [Fin.mk.inj_iff] at this
          rw [nodup_iff_injective_get] at h
          apply h; rw [← H]; simp

@[deprecated (since := "2025-02-15")] alias prev_get := prev_getElem

theorem pmap_next_eq_rotate_one (h : Nodup l) : (l.pmap l.next fun _ h => h) = l.rotate 1 := by
  apply List.ext_getElem
  · simp
  · intros
    rw [getElem_pmap, getElem_rotate, next_getElem _ h]

theorem pmap_prev_eq_rotate_length_sub_one (h : Nodup l) :
    (l.pmap l.prev fun _ h => h) = l.rotate (l.length - 1) := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    rw [getElem_rotate, getElem_pmap, prev_getElem _ h]

theorem prev_next (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    prev l (next l x hx) (next_mem _ _ _) = x := by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + 1 + length tl) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc, add_comm 1, Nat.add_mod_right, Nat.mod_eq_of_lt hn]
    simp only [length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, this]

theorem next_prev (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    next l (prev l x hx) (prev_mem _ _ _) = x := by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + length tl + 1) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc, Nat.add_mod_right, Nat.mod_eq_of_lt hn]
    simp [this]

theorem prev_reverse_eq_next (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    prev l.reverse x (mem_reverse.mpr hx) = next l x hx := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  have lpos : 0 < l.length := k.zero_le.trans_lt hk
  have key : l.length - 1 - k < l.length := by omega
  rw [← getElem_pmap l.next (fun _ h => h) (by simpa using hk)]
  simp_rw [getElem_eq_getElem_reverse (l := l), pmap_next_eq_rotate_one _ h]
  rw [← getElem_pmap l.reverse.prev fun _ h => h]
  · simp_rw [pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), rotate_reverse,
      length_reverse, Nat.mod_eq_of_lt (Nat.sub_lt lpos Nat.succ_pos'),
      Nat.sub_sub_self (Nat.succ_le_of_lt lpos)]
    rw [getElem_eq_getElem_reverse]
    · simp [Nat.sub_sub_self (Nat.le_sub_one_of_lt hk)]
  · simpa

theorem next_reverse_eq_prev (l : List α) (h : Nodup l) (x : α) (hx : x ∈ l) :
    next l.reverse x (mem_reverse.mpr hx) = prev l x hx := by
  convert (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm
  exact (reverse_reverse l).symm

theorem isRotated_next_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x ∈ l) :
    l.next x hx = l'.next x (h.mem_iff.mp hx) := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  obtain ⟨n, rfl⟩ := id h
  rw [next_getElem _ hn]
  simp_rw [getElem_eq_getElem_rotate _ n k]
  rw [next_getElem _ (h.nodup_iff.mp hn), getElem_eq_getElem_rotate _ n]
  simp [add_assoc]

theorem isRotated_prev_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x ∈ l) :
    l.prev x hx = l'.prev x (h.mem_iff.mp hx) := by
  rw [← next_reverse_eq_prev _ hn, ← next_reverse_eq_prev _ (h.nodup_iff.mp hn)]
  exact isRotated_next_eq h.reverse (nodup_reverse.mpr hn) _

end List

open List

/-- `Cycle α` is the quotient of `List α` by cyclic permutation.
Duplicates are allowed.
-/
def Cycle (α : Type*) : Type _ :=
  Quotient (IsRotated.setoid α)

namespace Cycle

variable {α : Type*}

/-- The coercion from `List α` to `Cycle α` -/
@[coe] def ofList : List α → Cycle α :=
  Quot.mk _

instance : Coe (List α) (Cycle α) :=
  ⟨ofList⟩

@[simp]
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = (l₂ : Cycle α) ↔ l₁ ~r l₂ :=
  @Quotient.eq _ (IsRotated.setoid _) _ _

@[simp]
theorem mk_eq_coe (l : List α) : Quot.mk _ l = (l : Cycle α) :=
  rfl

@[simp]
theorem mk''_eq_coe (l : List α) : Quotient.mk'' l = (l : Cycle α) :=
  rfl

theorem coe_cons_eq_coe_append (l : List α) (a : α) :
    (↑(a :: l) : Cycle α) = (↑(l ++ [a]) : Cycle α) :=
  Quot.sound ⟨1, by rw [rotate_cons_succ, rotate_zero]⟩

/-- The unique empty cycle. -/
def nil : Cycle α :=
  ([] : List α)

@[simp]
theorem coe_nil : ↑([] : List α) = @nil α :=
  rfl

@[simp]
theorem coe_eq_nil (l : List α) : (l : Cycle α) = nil ↔ l = [] :=
  coe_eq_coe.trans isRotated_nil_iff

/-- For consistency with `EmptyCollection (List α)`. -/
instance : EmptyCollection (Cycle α) :=
  ⟨nil⟩

@[simp]
theorem empty_eq : ∅ = @nil α :=
  rfl

instance : Inhabited (Cycle α) :=
  ⟨nil⟩

/-- An induction principle for `Cycle`. Use as `induction s`. -/
@[elab_as_elim, induction_eliminator]
theorem induction_on {motive : Cycle α → Prop} (s : Cycle α) (nil : motive nil)
    (cons : ∀ (a) (l : List α), motive ↑l → motive ↑(a :: l)) : motive s :=
  Quotient.inductionOn' s fun l => by
    refine List.recOn l ?_ ?_ <;> simp only [mk''_eq_coe, coe_nil]
    assumption'

/-- For `x : α`, `s : Cycle α`, `x ∈ s` indicates that `x` occurs at least once in `s`. -/
def Mem (s : Cycle α) (a : α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun _ _ e => propext <| e.mem_iff

instance : Membership α (Cycle α) :=
  ⟨Mem⟩

@[simp]
theorem mem_coe_iff {a : α} {l : List α} : a ∈ (↑l : Cycle α) ↔ a ∈ l :=
  Iff.rfl

@[simp]
theorem notMem_nil (a : α) : a ∉ nil :=
  List.not_mem_nil

@[deprecated (since := "2025-05-23")] alias not_mem_nil := notMem_nil

instance [DecidableEq α] : DecidableEq (Cycle α) := fun s₁ s₂ =>
  Quotient.recOnSubsingleton₂' s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq''

instance [DecidableEq α] (x : α) (s : Cycle α) : Decidable (x ∈ s) :=
  Quotient.recOnSubsingleton' s fun l => show Decidable (x ∈ l) from inferInstance

/-- Reverse a `s : Cycle α` by reversing the underlying `List`. -/
nonrec def reverse (s : Cycle α) : Cycle α :=
  Quot.map reverse (fun _ _ => IsRotated.reverse) s

@[simp]
theorem reverse_coe (l : List α) : (l : Cycle α).reverse = l.reverse :=
  rfl

@[simp]
theorem mem_reverse_iff {a : α} {s : Cycle α} : a ∈ s.reverse ↔ a ∈ s :=
  Quot.inductionOn s fun _ => mem_reverse

@[simp]
theorem reverse_reverse (s : Cycle α) : s.reverse.reverse = s :=
  Quot.inductionOn s fun _ => by simp

@[simp]
theorem reverse_nil : nil.reverse = @nil α :=
  rfl

/-- The length of the `s : Cycle α`, which is the number of elements, counting duplicates. -/
def length (s : Cycle α) : ℕ :=
  Quot.liftOn s List.length fun _ _ e => e.perm.length_eq

@[simp]
theorem length_coe (l : List α) : length (l : Cycle α) = l.length :=
  rfl

@[simp]
theorem length_nil : length (@nil α) = 0 :=
  rfl

@[simp]
theorem length_reverse (s : Cycle α) : s.reverse.length = s.length :=
  Quot.inductionOn s fun _ => List.length_reverse

/-- A `s : Cycle α` that is at most one element. -/
def Subsingleton (s : Cycle α) : Prop :=
  s.length ≤ 1

theorem subsingleton_nil : Subsingleton (@nil α) := Nat.zero_le _

theorem length_subsingleton_iff {s : Cycle α} : Subsingleton s ↔ length s ≤ 1 :=
  Iff.rfl

@[simp]
theorem subsingleton_reverse_iff {s : Cycle α} : s.reverse.Subsingleton ↔ s.Subsingleton := by
  simp [length_subsingleton_iff]

theorem Subsingleton.congr {s : Cycle α} (h : Subsingleton s) :
    ∀ ⦃x⦄ (_hx : x ∈ s) ⦃y⦄ (_hy : y ∈ s), x = y := by
  induction' s using Quot.inductionOn with l
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe, le_iff_lt_or_eq, Nat.lt_add_one_iff,
    length_eq_zero_iff, length_eq_one_iff, Nat.not_lt_zero, false_or] at h
  rcases h with (rfl | ⟨z, rfl⟩) <;> simp

/-- A `s : Cycle α` that is made up of at least two unique elements. -/
def Nontrivial (s : Cycle α) : Prop :=
  ∃ x y : α, x ≠ y ∧ x ∈ s ∧ y ∈ s

@[simp]
theorem nontrivial_coe_nodup_iff {l : List α} (hl : l.Nodup) :
    Nontrivial (l : Cycle α) ↔ 2 ≤ l.length := by
  rw [Nontrivial]
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp
  · simp
  · simp only [mem_cons, mem_coe_iff, List.length, Ne, Nat.succ_le_succ_iff,
      Nat.zero_le, iff_true]
    refine ⟨hd, hd', ?_, by simp⟩
    simp only [not_or, mem_cons, nodup_cons] at hl
    exact hl.left.left

@[simp]
theorem nontrivial_reverse_iff {s : Cycle α} : s.reverse.Nontrivial ↔ s.Nontrivial := by
  simp [Nontrivial]

theorem length_nontrivial {s : Cycle α} (h : Nontrivial s) : 2 ≤ length s := by
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  induction' s using Quot.inductionOn with l
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp at hx
  · simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy
    simp [hx, hy] at hxy
  · simp [Nat.succ_le_succ_iff]

/-- The `s : Cycle α` contains no duplicates. -/
nonrec def Nodup (s : Cycle α) : Prop :=
  Quot.liftOn s Nodup fun _l₁ _l₂ e => propext <| e.nodup_iff

@[simp]
nonrec theorem nodup_nil : Nodup (@nil α) :=
  nodup_nil

@[simp]
theorem nodup_coe_iff {l : List α} : Nodup (l : Cycle α) ↔ l.Nodup :=
  Iff.rfl

@[simp]
theorem nodup_reverse_iff {s : Cycle α} : s.reverse.Nodup ↔ s.Nodup :=
  Quot.inductionOn s fun _ => nodup_reverse

theorem Subsingleton.nodup {s : Cycle α} (h : Subsingleton s) : Nodup s := by
  induction' s using Quot.inductionOn with l
  obtain - | ⟨hd, tl⟩ := l
  · simp
  · have : tl = [] := by simpa [Subsingleton, length_eq_zero_iff, Nat.succ_le_succ_iff] using h
    simp [this]

theorem Nodup.nontrivial_iff {s : Cycle α} (h : Nodup s) : Nontrivial s ↔ ¬Subsingleton s := by
  rw [length_subsingleton_iff]
  induction s using Quotient.inductionOn'
  simp only [mk''_eq_coe, nodup_coe_iff] at h
  simp [h, Nat.succ_le_iff]

/-- The `s : Cycle α` as a `Multiset α`.
-/
def toMultiset (s : Cycle α) : Multiset α :=
  Quotient.liftOn' s (↑) fun _ _ h => Multiset.coe_eq_coe.mpr h.perm

@[simp]
theorem coe_toMultiset (l : List α) : (l : Cycle α).toMultiset = l :=
  rfl

@[simp]
theorem nil_toMultiset : nil.toMultiset = (0 : Multiset α) :=
  rfl

@[simp]
theorem card_toMultiset (s : Cycle α) : Multiset.card s.toMultiset = s.length :=
  Quotient.inductionOn' s (by simp)

@[simp]
theorem toMultiset_eq_nil {s : Cycle α} : s.toMultiset = 0 ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)

/-- The lift of `list.map`. -/
def map {β : Type*} (f : α → β) : Cycle α → Cycle β :=
  Quotient.map' (List.map f) fun _ _ h => h.map _

@[simp]
theorem map_nil {β : Type*} (f : α → β) : map f nil = nil :=
  rfl

@[simp]
theorem map_coe {β : Type*} (f : α → β) (l : List α) : map f ↑l = List.map f l :=
  rfl

@[simp]
theorem map_eq_nil {β : Type*} (f : α → β) (s : Cycle α) : map f s = nil ↔ s = nil :=
  Quotient.inductionOn' s (by simp)

@[simp]
theorem mem_map {β : Type*} {f : α → β} {b : β} {s : Cycle α} :
    b ∈ s.map f ↔ ∃ a, a ∈ s ∧ f a = b :=
  Quotient.inductionOn' s (by simp)

/-- The `Multiset` of lists that can make the cycle. -/
def lists (s : Cycle α) : Multiset (List α) :=
  Quotient.liftOn' s (fun l => (l.cyclicPermutations : Multiset (List α))) fun l₁ l₂ h => by
    simpa using h.cyclicPermutations.perm

@[simp]
theorem lists_coe (l : List α) : lists (l : Cycle α) = ↑l.cyclicPermutations :=
  rfl

@[simp]
theorem mem_lists_iff_coe_eq {s : Cycle α} {l : List α} : l ∈ s.lists ↔ (l : Cycle α) = s :=
  Quotient.inductionOn' s fun l => by
    rw [lists, Quotient.liftOn'_mk'']
    simp

@[simp]
theorem lists_nil : lists (@nil α) = {([] : List α)} := by
  rw [nil, lists_coe, cyclicPermutations_nil, Multiset.coe_singleton]

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
        (decidableNontrivialCoe (x :: l))
    else isTrue ⟨x, y, h, by simp, by simp⟩

instance {s : Cycle α} : Decidable (Nontrivial s) :=
  Quot.recOnSubsingleton s decidableNontrivialCoe

instance {s : Cycle α} : Decidable (Nodup s) :=
  Quot.recOnSubsingleton s List.nodupDecidable

instance fintypeNodupCycle [Fintype α] : Fintype { s : Cycle α // s.Nodup } :=
  Fintype.ofSurjective (fun l : { l : List α // l.Nodup } => ⟨l.val, by simpa using l.prop⟩)
    fun ⟨s, hs⟩ => by
    induction' s using Quotient.inductionOn' with s hs
    exact ⟨⟨s, hs⟩, by simp⟩

instance fintypeNodupNontrivialCycle [Fintype α] :
    Fintype { s : Cycle α // s.Nodup ∧ s.Nontrivial } :=
  Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.Nodup }).map (Function.Embedding.subtype _)).filter
      Cycle.Nontrivial)
    (by simp)

/-- The `s : Cycle α` as a `Finset α`. -/
def toFinset (s : Cycle α) : Finset α :=
  s.toMultiset.toFinset

@[simp]
theorem toFinset_toMultiset (s : Cycle α) : s.toMultiset.toFinset = s.toFinset :=
  rfl

@[simp]
theorem coe_toFinset (l : List α) : (l : Cycle α).toFinset = l.toFinset :=
  rfl

@[simp]
theorem nil_toFinset : (@nil α).toFinset = ∅ :=
  rfl

@[simp]
theorem toFinset_eq_nil {s : Cycle α} : s.toFinset = ∅ ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)

/-- Given a `s : Cycle α` such that `Nodup s`, retrieve the next element after `x ∈ s`. -/
nonrec def next : ∀ (s : Cycle α) (_hs : Nodup s) (x : α) (_hx : x ∈ s), α := fun s =>
  Quot.hrecOn (motive := fun (s : Cycle α) => ∀ (_hs : Cycle.Nodup s) (x : α) (_hx : x ∈ s), α) s
  (fun l _hn x hx => next l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ _he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by rw [eq_of_heq hxy]; simpa [eq_of_heq hxy] using h.mem_iff))
  fun hm hm' he' => heq_of_eq
    (by rw [heq_iff_eq] at hxy; subst x; simpa using isRotated_next_eq h h₁ _)

/-- Given a `s : Cycle α` such that `Nodup s`, retrieve the previous element before `x ∈ s`. -/
nonrec def prev : ∀ (s : Cycle α) (_hs : Nodup s) (x : α) (_hx : x ∈ s), α := fun s =>
  Quot.hrecOn (motive := fun (s : Cycle α) => ∀ (_hs : Cycle.Nodup s) (x : α) (_hx : x ∈ s), α) s
  (fun l _hn x hx => prev l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ _he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by rw [eq_of_heq hxy]; simpa [eq_of_heq hxy] using h.mem_iff))
  fun hm hm' he' => heq_of_eq
    (by rw [heq_iff_eq] at hxy; subst x; simpa using isRotated_prev_eq h h₁ _)

-- `simp` cannot infer the proofs: see `prev_reverse_eq_next'` for `@[simp]` lemma.
nonrec theorem prev_reverse_eq_next (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.reverse.prev (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.next hs x hx :=
  Quotient.inductionOn' s prev_reverse_eq_next

@[simp]
nonrec theorem prev_reverse_eq_next' (s : Cycle α) (hs : Nodup s.reverse) (x : α)
    (hx : x ∈ s.reverse) :
    s.reverse.prev hs x hx = s.next (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx) :=
  prev_reverse_eq_next s (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx)

-- `simp` cannot infer the proofs: see `next_reverse_eq_prev'` for `@[simp]` lemma.
theorem next_reverse_eq_prev (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) :
    s.reverse.next (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.prev hs x hx := by
  simp [← prev_reverse_eq_next]

@[simp]
theorem next_reverse_eq_prev' (s : Cycle α) (hs : Nodup s.reverse) (x : α) (hx : x ∈ s.reverse) :
    s.reverse.next hs x hx = s.prev (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx) := by
  simp [← prev_reverse_eq_next]

@[simp]
nonrec theorem next_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) : s.next hs x hx ∈ s := by
  induction s using Quot.inductionOn
  apply next_mem; assumption

theorem prev_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x ∈ s) : s.prev hs x hx ∈ s := by
  rw [← next_reverse_eq_prev, ← mem_reverse_iff]
  apply next_mem

@[simp]
nonrec theorem prev_next (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.prev hs (s.next hs x hx) (next_mem s hs x hx) = x :=
  Quotient.inductionOn' s prev_next

@[simp]
nonrec theorem next_prev (s : Cycle α) : ∀ (hs : Nodup s) (x : α) (hx : x ∈ s),
    s.next hs (s.prev hs x hx) (prev_mem s hs x hx) = x :=
  Quotient.inductionOn' s next_prev

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
      rcases a with - | ⟨a, l⟩ <;> rcases b with - | ⟨b, m⟩
      · rfl
      · have := isRotated_nil_iff'.1 hab
        contradiction
      · have := isRotated_nil_iff.1 hab
        contradiction
      · dsimp only
        obtain ⟨n, hn⟩ := hab
        induction' n with d hd generalizing a b l m
        · simp only [rotate_zero, cons.injEq] at hn
          rw [hn.1, hn.2]
        · rcases l with - | ⟨c, s⟩
          · simp only [rotate_cons_succ, nil_append, rotate_singleton, cons.injEq] at hn
            rw [hn.1, hn.2]
          · rw [Nat.add_comm, ← rotate_rotate, rotate_cons_succ, rotate_zero, cons_append] at hn
            rw [← hd c _ _ _ hn]
            simp [and_comm]

@[simp]
theorem Chain.nil (r : α → α → Prop) : Cycle.Chain r (@nil α) := by trivial

@[simp]
theorem chain_coe_cons (r : α → α → Prop) (a : α) (l : List α) :
    Chain r (a :: l) ↔ List.Chain r a (l ++ [a]) :=
  Iff.rfl

theorem chain_singleton (r : α → α → Prop) (a : α) : Chain r [a] ↔ r a a := by
  rw [chain_coe_cons, nil_append, List.chain_singleton]

theorem chain_ne_nil (r : α → α → Prop) {l : List α} :
    ∀ hl : l ≠ [], Chain r l ↔ List.Chain r (getLast l hl) l :=
  l.reverseRecOn (fun hm => hm.irrefl.elim) (by
    intro m a _H _
    rw [← coe_cons_eq_coe_append, chain_coe_cons, getLast_append_singleton])

theorem chain_map {β : Type*} {r : α → α → Prop} (f : β → α) {s : Cycle β} :
    Chain r (s.map f) ↔ Chain (fun a b => r (f a) (f b)) s :=
  Quotient.inductionOn s fun l => by
    rcases l with - | ⟨a, l⟩
    · rfl
    · simp [← concat_eq_append, ← List.map_concat, List.chain_map f]

nonrec theorem chain_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    Chain r (List.range n.succ) ↔ r n 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ, ← coe_cons_eq_coe_append, chain_coe_cons, ← range_succ, chain_range_succ]

variable {r : α → α → Prop} {s : Cycle α}

theorem Chain.imp {r₁ r₂ : α → α → Prop} (H : ∀ a b, r₁ a b → r₂ a b) (p : Chain r₁ s) :
    Chain r₂ s := by
  induction s
  · trivial
  · rw [chain_coe_cons] at p ⊢
    exact p.imp H

/-- As a function from a relation to a predicate, `chain` is monotonic. -/
theorem chain_mono : Monotone (Chain : (α → α → Prop) → Cycle α → Prop) := fun _a _b hab _s =>
  Chain.imp hab

theorem chain_of_pairwise : (∀ a ∈ s, ∀ b ∈ s, r a b) → Chain r s := by
  induction s with
  | nil => exact fun _ ↦ Cycle.Chain.nil r
  | cons a l => ?_
  intro hs
  have Ha : a ∈ (a :: l : Cycle α) := by simp
  have Hl : ∀ {b} (_hb : b ∈ l), b ∈ (a :: l : Cycle α) := @fun b hb => by simp [hb]
  rw [Cycle.chain_coe_cons]
  apply Pairwise.chain
  rw [pairwise_cons]
  refine
    ⟨fun b hb => ?_,
      pairwise_append.2
        ⟨pairwise_of_forall_mem_list fun b hb c hc => hs b (Hl hb) c (Hl hc),
          pairwise_singleton r a, fun b hb c hc => ?_⟩⟩
  · rw [mem_append] at hb
    rcases hb with hb | hb
    · exact hs a Ha b (Hl hb)
    · rw [mem_singleton] at hb
      rw [hb]
      exact hs a Ha a Ha
  · rw [mem_singleton] at hc
    rw [hc]
    exact hs b (Hl hb) a Ha

theorem chain_iff_pairwise [IsTrans α r] : Chain r s ↔ ∀ a ∈ s, ∀ b ∈ s, r a b :=
  ⟨by
    induction s with
    | nil => exact fun _ b hb ↦ (notMem_nil _ hb).elim
    | cons a l => ?_
    intro hs b hb c hc
    rw [Cycle.chain_coe_cons, List.chain_iff_pairwise] at hs
    simp only [pairwise_append, pairwise_cons, mem_append, mem_singleton, List.not_mem_nil,
      IsEmpty.forall_iff, imp_true_iff, Pairwise.nil, forall_eq, true_and] at hs
    simp only [mem_coe_iff, mem_cons] at hb hc
    rcases hb with (rfl | hb) <;> rcases hc with (rfl | hc)
    · exact hs.1 c (Or.inr rfl)
    · exact hs.1 c (Or.inl hc)
    · exact hs.2.2 b hb
    · exact _root_.trans (hs.2.2 b hb) (hs.1 c (Or.inl hc)), Cycle.chain_of_pairwise⟩

theorem Chain.eq_nil_of_irrefl [IsTrans α r] [IsIrrefl α r] (h : Chain r s) : s = Cycle.nil := by
  induction s with
  | nil => rfl
  | cons a l h =>
    have ha : a ∈ a :: l := mem_cons_self
    exact (irrefl_of r a <| chain_iff_pairwise.1 h a ha a ha).elim

theorem Chain.eq_nil_of_well_founded [IsWellFounded α r] (h : Chain r s) : s = Cycle.nil :=
  Chain.eq_nil_of_irrefl <| h.imp fun _ _ => Relation.TransGen.single

theorem forall_eq_of_chain [IsTrans α r] [IsAntisymm α r] (hs : Chain r s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : a = b := by
  rw [chain_iff_pairwise] at hs
  exact antisymm (hs a ha b hb) (hs b hb a ha)

end Cycle
