/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Infix

#align_import data.list.sort from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Sorting algorithms on lists

In this file we define `List.Sorted r l` to be an alias for `List.Pairwise r l`.
This alias is preferred in the case that `r` is a `<` or `≤`-like relation.
Then we define two sorting algorithms:
`List.insertionSort` and `List.mergeSort`, and prove their correctness.
-/


open List.Perm

universe uu

namespace List

/-!
### The predicate `List.Sorted`
-/


section Sorted

variable {α : Type uu} {r : α → α → Prop} {a : α} {l : List α}

/-- `Sorted r l` is the same as `List.Pairwise r l`, preferred in the case that `r`
  is a `<` or `≤`-like relation (transitive and antisymmetric or asymmetric) -/
def Sorted :=
  @Pairwise
#align list.sorted List.Sorted

instance decidableSorted [DecidableRel r] (l : List α) : Decidable (Sorted r l) :=
  List.instDecidablePairwise _
#align list.decidable_sorted List.decidableSorted

protected theorem Sorted.le_of_lt [Preorder α] {l : List α} (h : l.Sorted (· < ·)) :
    l.Sorted (· ≤ ·) :=
  h.imp le_of_lt

protected theorem Sorted.lt_of_le [PartialOrder α] {l : List α} (h₁ : l.Sorted (· ≤ ·))
    (h₂ : l.Nodup) : l.Sorted (· < ·) :=
  h₁.imp₂ (fun _ _ => lt_of_le_of_ne) h₂

protected theorem Sorted.ge_of_gt [Preorder α] {l : List α} (h : l.Sorted (· > ·)) :
    l.Sorted (· ≥ ·) :=
  h.imp le_of_lt

protected theorem Sorted.gt_of_ge [PartialOrder α] {l : List α} (h₁ : l.Sorted (· ≥ ·))
    (h₂ : l.Nodup) : l.Sorted (· > ·) :=
  h₁.imp₂ (fun _ _ => lt_of_le_of_ne) <| by simp_rw [ne_comm]; exact h₂

@[simp]
theorem sorted_nil : Sorted r [] :=
  Pairwise.nil
#align list.sorted_nil List.sorted_nil

theorem Sorted.of_cons : Sorted r (a :: l) → Sorted r l :=
  Pairwise.of_cons
#align list.sorted.of_cons List.Sorted.of_cons

theorem Sorted.tail {r : α → α → Prop} {l : List α} (h : Sorted r l) : Sorted r l.tail :=
  Pairwise.tail h
#align list.sorted.tail List.Sorted.tail

theorem rel_of_sorted_cons {a : α} {l : List α} : Sorted r (a :: l) → ∀ b ∈ l, r a b :=
  rel_of_pairwise_cons
#align list.rel_of_sorted_cons List.rel_of_sorted_cons

theorem Sorted.head!_le [Inhabited α] [Preorder α] {a : α} {l : List α} (h : Sorted (· < ·) l)
    (ha : a ∈ l) : l.head! ≤ a := by
  rw [← List.cons_head!_tail (List.ne_nil_of_mem ha)] at h ha
  cases ha
  · exact le_rfl
  · exact le_of_lt (rel_of_sorted_cons h a (by assumption))

theorem Sorted.le_head! [Inhabited α] [Preorder α] {a : α} {l : List α} (h : Sorted (· > ·) l)
    (ha : a ∈ l) : a ≤ l.head! := by
  rw [← List.cons_head!_tail (List.ne_nil_of_mem ha)] at h ha
  cases ha
  · exact le_rfl
  · exact le_of_lt (rel_of_sorted_cons h a (by assumption))

@[simp]
theorem sorted_cons {a : α} {l : List α} : Sorted r (a :: l) ↔ (∀ b ∈ l, r a b) ∧ Sorted r l :=
  pairwise_cons
#align list.sorted_cons List.sorted_cons

protected theorem Sorted.nodup {r : α → α → Prop} [IsIrrefl α r] {l : List α} (h : Sorted r l) :
    Nodup l :=
  Pairwise.nodup h
#align list.sorted.nodup List.Sorted.nodup

theorem eq_of_perm_of_sorted [IsAntisymm α r] {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hs₁ : Sorted r l₁)
    (hs₂ : Sorted r l₂) : l₁ = l₂ := by
  induction' hs₁ with a l₁ h₁ hs₁ IH generalizing l₂
  · exact hp.nil_eq
  · have : a ∈ l₂ := hp.subset (mem_cons_self _ _)
    rcases append_of_mem this with ⟨u₂, v₂, rfl⟩
    have hp' := (perm_cons a).1 (hp.trans perm_middle)
    obtain rfl := IH hp' (hs₂.sublist <| by simp)
    change a :: u₂ ++ v₂ = u₂ ++ ([a] ++ v₂)
    rw [← append_assoc]
    congr
    have : ∀ x ∈ u₂, x = a := fun x m =>
      antisymm ((pairwise_append.1 hs₂).2.2 _ m a (mem_cons_self _ _)) (h₁ _ (by simp [m]))
    rw [(@eq_replicate _ a (length u₂ + 1) (a :: u₂)).2,
        (@eq_replicate _ a (length u₂ + 1) (u₂ ++ [a])).2] <;>
        constructor <;>
      simp [iff_true_intro this, or_comm]
#align list.eq_of_perm_of_sorted List.eq_of_perm_of_sorted

theorem sublist_of_subperm_of_sorted [IsAntisymm α r] {l₁ l₂ : List α} (hp : l₁ <+~ l₂)
    (hs₁ : l₁.Sorted r) (hs₂ : l₂.Sorted r) : l₁ <+ l₂ := by
  let ⟨_, h, h'⟩ := hp
  rwa [← eq_of_perm_of_sorted h (hs₂.sublist h') hs₁]
#align list.sublist_of_subperm_of_sorted List.sublist_of_subperm_of_sorted

@[simp 1100] -- Porting note: higher priority for linter
theorem sorted_singleton (a : α) : Sorted r [a] :=
  pairwise_singleton _ _
#align list.sorted_singleton List.sorted_singleton

theorem Sorted.rel_get_of_lt {l : List α} (h : l.Sorted r) {a b : Fin l.length} (hab : a < b) :
    r (l.get a) (l.get b) :=
  List.pairwise_iff_get.1 h _ _ hab

set_option linter.deprecated false in
@[deprecated Sorted.rel_get_of_lt (since := "2024-05-08")]
theorem Sorted.rel_nthLe_of_lt {l : List α} (h : l.Sorted r) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a < b) : r (l.nthLe a ha) (l.nthLe b hb) :=
  List.pairwise_iff_get.1 h ⟨a, ha⟩ ⟨b, hb⟩ hab
#align list.sorted.rel_nth_le_of_lt List.Sorted.rel_nthLe_of_lt

theorem Sorted.rel_get_of_le [IsRefl α r] {l : List α} (h : l.Sorted r) {a b : Fin l.length}
    (hab : a ≤ b) : r (l.get a) (l.get b) := by
  rcases hab.eq_or_lt with (rfl | hlt)
  exacts [refl _, h.rel_get_of_lt hlt]

set_option linter.deprecated false in
@[deprecated Sorted.rel_get_of_le (since := "2024-05-08")]
theorem Sorted.rel_nthLe_of_le [IsRefl α r] {l : List α} (h : l.Sorted r) {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a ≤ b) : r (l.nthLe a ha) (l.nthLe b hb) :=
  h.rel_get_of_le hab
#align list.sorted.rel_nth_le_of_le List.Sorted.rel_nthLe_of_le

theorem Sorted.rel_of_mem_take_of_mem_drop {l : List α} (h : List.Sorted r l) {k : ℕ} {x y : α}
    (hx : x ∈ List.take k l) (hy : y ∈ List.drop k l) : r x y := by
  obtain ⟨⟨iy, hiy⟩, rfl⟩ := get_of_mem hy
  obtain ⟨⟨ix, hix⟩, rfl⟩ := get_of_mem hx
  rw [get_take', get_drop']
  rw [length_take] at hix
  exact h.rel_get_of_lt (Nat.lt_add_right _ (lt_min_iff.mp hix).left)
#align list.sorted.rel_of_mem_take_of_mem_drop List.Sorted.rel_of_mem_take_of_mem_drop

end Sorted

section Monotone

variable {n : ℕ} {α : Type uu} [Preorder α] {f : Fin n → α}

theorem sorted_ofFn_iff {r : α → α → Prop} : (ofFn f).Sorted r ↔ ((· < ·) ⇒ r) f f := by
  simp_rw [Sorted, pairwise_iff_get, get_ofFn, Relator.LiftFun]
  exact Iff.symm (Fin.rightInverse_cast _).surjective.forall₂

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≤ ·)` if and only if `f` is
strictly monotone. -/
@[simp] theorem sorted_lt_ofFn_iff : (ofFn f).Sorted (· < ·) ↔ StrictMono f := sorted_ofFn_iff

/-- The list `List.ofFn f` is sorted with respect to `(· ≤ ·)` if and only if `f` is monotone. -/
@[simp] theorem sorted_le_ofFn_iff : (ofFn f).Sorted (· ≤ ·) ↔ Monotone f :=
  sorted_ofFn_iff.trans monotone_iff_forall_lt.symm

/-- A tuple is monotone if and only if the list obtained from it is sorted. -/
@[deprecated sorted_le_ofFn_iff] -- 2023-01-10
theorem monotone_iff_ofFn_sorted : Monotone f ↔ (ofFn f).Sorted (· ≤ ·) := sorted_le_ofFn_iff.symm
#align list.monotone_iff_of_fn_sorted List.monotone_iff_ofFn_sorted

/-- The list obtained from a monotone tuple is sorted. -/
alias ⟨_, _root_.Monotone.ofFn_sorted⟩ := sorted_le_ofFn_iff
#align list.monotone.of_fn_sorted Monotone.ofFn_sorted

end Monotone

section sort

variable {α : Type uu} (r : α → α → Prop) [DecidableRel r]

local infixl:50 " ≼ " => r

/-! ### Insertion sort -/


section InsertionSort

/-- `orderedInsert a l` inserts `a` into `l` at such that
  `orderedInsert a l` is sorted if `l` is. -/
@[simp]
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l
#align list.ordered_insert List.orderedInsert

/-- `insertionSort l` returns `l` sorted using the insertion sort algorithm. -/
@[simp]
def insertionSort : List α → List α
  | [] => []
  | b :: l => orderedInsert r b (insertionSort l)
#align list.insertion_sort List.insertionSort

@[simp]
theorem orderedInsert_nil (a : α) : [].orderedInsert r a = [a] :=
  rfl
#align list.ordered_insert_nil List.orderedInsert_nil

theorem orderedInsert_length : ∀ (L : List α) (a : α), (L.orderedInsert r a).length = L.length + 1
  | [], a => rfl
  | hd :: tl, a => by
    dsimp [orderedInsert]
    split_ifs <;> simp [orderedInsert_length tl]
#align list.ordered_insert_length List.orderedInsert_length

/-- An alternative definition of `orderedInsert` using `takeWhile` and `dropWhile`. -/
theorem orderedInsert_eq_take_drop (a : α) :
    ∀ l : List α,
      l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b
  | [] => rfl
  | b :: l => by
    dsimp only [orderedInsert]
    split_ifs with h <;> simp [takeWhile, dropWhile, *, orderedInsert_eq_take_drop a l]
#align list.ordered_insert_eq_take_drop List.orderedInsert_eq_take_drop

theorem insertionSort_cons_eq_take_drop (a : α) (l : List α) :
    insertionSort r (a :: l) =
      ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++
        a :: (insertionSort r l).dropWhile fun b => ¬a ≼ b :=
  orderedInsert_eq_take_drop r a _
#align list.insertion_sort_cons_eq_take_drop List.insertionSort_cons_eq_take_drop

@[simp]
theorem mem_orderedInsert {a b : α} {l : List α} :
    a ∈ orderedInsert r b l ↔ a = b ∨ a ∈ l :=
  match l with
  | [] => by simp [orderedInsert]
  | x :: xs => by
    rw [orderedInsert]
    split_ifs
    · simp [orderedInsert]
    · rw [mem_cons, mem_cons, mem_orderedInsert, or_left_comm]

section Correctness

open Perm

theorem perm_orderedInsert (a) : ∀ l : List α, orderedInsert r a l ~ a :: l
  | [] => Perm.refl _
  | b :: l => by
    by_cases h : a ≼ b
    · simp [orderedInsert, h]
    · simpa [orderedInsert, h] using ((perm_orderedInsert a l).cons _).trans (Perm.swap _ _ _)
#align list.perm_ordered_insert List.perm_orderedInsert

theorem orderedInsert_count [DecidableEq α] (L : List α) (a b : α) :
    count a (L.orderedInsert r b) = count a L + if a = b then 1 else 0 := by
  rw [(L.perm_orderedInsert r b).count_eq, count_cons]
#align list.ordered_insert_count List.orderedInsert_count

theorem perm_insertionSort : ∀ l : List α, insertionSort r l ~ l
  | [] => Perm.nil
  | b :: l => by
    simpa [insertionSort] using (perm_orderedInsert _ _ _).trans ((perm_insertionSort l).cons b)
#align list.perm_insertion_sort List.perm_insertionSort

variable {r}

/-- If `l` is already `List.Sorted` with respect to `r`, then `insertionSort` does not change
it. -/
theorem Sorted.insertionSort_eq : ∀ {l : List α}, Sorted r l → insertionSort r l = l
  | [], _ => rfl
  | [a], _ => rfl
  | a :: b :: l, h => by
    rw [insertionSort, Sorted.insertionSort_eq, orderedInsert, if_pos]
    exacts [rel_of_sorted_cons h _ (mem_cons_self _ _), h.tail]
#align list.sorted.insertion_sort_eq List.Sorted.insertionSort_eq

/-- For a reflexive relation, insert then erasing is the identity. -/
theorem erase_orderedInsert [DecidableEq α] [IsRefl α r] (x : α) (xs : List α) :
    (xs.orderedInsert r x).erase x = xs := by
  rw [orderedInsert_eq_take_drop, erase_append_right, List.erase_cons_head,
    takeWhile_append_dropWhile]
  intro h
  replace h := mem_takeWhile_imp h
  simp [refl x] at h

/-- Inserting then erasing an element that is absent is the identity. -/
theorem erase_orderedInsert_of_not_mem [DecidableEq α]
    {x : α} {xs : List α} (hx : x ∉ xs) :
    (xs.orderedInsert r x).erase x = xs := by
  rw [orderedInsert_eq_take_drop, erase_append_right, List.erase_cons_head,
    takeWhile_append_dropWhile]
  exact mt ((takeWhile_prefix _).sublist.subset ·) hx

/-- For an antisymmetric relation, erasing then inserting is the identity. -/
theorem orderedInsert_erase [DecidableEq α] [IsAntisymm α r] (x : α) (xs : List α) (hx : x ∈ xs)
    (hxs : Sorted r xs) :
    (xs.erase x).orderedInsert r x = xs := by
  induction xs generalizing x with
  | nil => cases hx
  | cons y ys ih =>
    rw [sorted_cons] at hxs
    obtain rfl | hxy := Decidable.eq_or_ne x y
    · rw [erase_cons_head]
      cases ys with
      | nil => rfl
      | cons z zs =>
        rw [orderedInsert, if_pos (hxs.1 _ (.head zs))]
    · rw [mem_cons] at hx
      replace hx := hx.resolve_left hxy
      rw [erase_cons_tail _ (not_beq_of_ne hxy.symm), orderedInsert, ih _ hx hxs.2, if_neg]
      refine mt (fun hrxy => ?_) hxy
      exact antisymm hrxy (hxs.1 _ hx)

theorem sublist_orderedInsert (x : α) (xs : List α) : xs <+ xs.orderedInsert r x := by
  rw [orderedInsert_eq_take_drop]
  refine Sublist.trans ?_ (.append_left (.cons _ (.refl _)) _)
  rw [takeWhile_append_dropWhile]

section TotalAndTransitive

variable [IsTotal α r] [IsTrans α r]

theorem Sorted.orderedInsert (a : α) : ∀ l, Sorted r l → Sorted r (orderedInsert r a l)
  | [], _ => sorted_singleton a
  | b :: l, h => by
    by_cases h' : a ≼ b
    · -- Porting note: was
      -- `simpa [orderedInsert, h', h] using fun b' bm => trans h' (rel_of_sorted_cons h _ bm)`
      rw [List.orderedInsert, if_pos h', sorted_cons]
      exact ⟨forall_mem_cons.2 ⟨h', fun c hc => _root_.trans h' (rel_of_sorted_cons h _ hc)⟩, h⟩
    · suffices ∀ b' : α, b' ∈ List.orderedInsert r a l → r b b' by
        simpa [orderedInsert, h', h.of_cons.orderedInsert a l]
      intro b' bm
      cases' (mem_orderedInsert r).mp bm with be bm
      · subst b'
        exact (total_of r _ _).resolve_left h'
      · exact rel_of_sorted_cons h _ bm
#align list.sorted.ordered_insert List.Sorted.orderedInsert

variable (r)

/-- The list `List.insertionSort r l` is `List.Sorted` with respect to `r`. -/
theorem sorted_insertionSort : ∀ l, Sorted r (insertionSort r l)
  | [] => sorted_nil
  | a :: l => (sorted_insertionSort l).orderedInsert a _
#align list.sorted_insertion_sort List.sorted_insertionSort

end TotalAndTransitive

end Correctness

end InsertionSort

/-! ### Merge sort -/


section MergeSort

-- TODO(Jeremy): observation: if instead we write (a :: (split l).1, b :: (split l).2), the
-- equation compiler can't prove the third equation
/-- Split `l` into two lists of approximately equal length.

     split [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) -/
@[simp]
def split : List α → List α × List α
  | [] => ([], [])
  | a :: l =>
    let (l₁, l₂) := split l
    (a :: l₂, l₁)
#align list.split List.split

theorem split_cons_of_eq (a : α) {l l₁ l₂ : List α} (h : split l = (l₁, l₂)) :
    split (a :: l) = (a :: l₂, l₁) := by rw [split, h]
#align list.split_cons_of_eq List.split_cons_of_eq

theorem length_split_le :
    ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → length l₁ ≤ length l ∧ length l₂ ≤ length l
  | [], _, _, rfl => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | a :: l, l₁', l₂', h => by
    cases' e : split l with l₁ l₂
    injection (split_cons_of_eq _ e).symm.trans h; substs l₁' l₂'
    cases' length_split_le e with h₁ h₂
    exact ⟨Nat.succ_le_succ h₂, Nat.le_succ_of_le h₁⟩
#align list.length_split_le List.length_split_le

theorem length_split_fst_le (l : List α) : length (split l).1 ≤ length l :=
  (length_split_le rfl).1

theorem length_split_snd_le (l : List α) : length (split l).2 ≤ length l :=
  (length_split_le rfl).2

theorem length_split_lt {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    length l₁ < length (a :: b :: l) ∧ length l₂ < length (a :: b :: l) := by
  cases' e : split l with l₁' l₂'
  injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h; substs l₁ l₂
  cases' length_split_le e with h₁ h₂
  exact ⟨Nat.succ_le_succ (Nat.succ_le_succ h₁), Nat.succ_le_succ (Nat.succ_le_succ h₂)⟩
#align list.length_split_lt List.length_split_lt

theorem perm_split : ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → l ~ l₁ ++ l₂
  | [], _, _, rfl => Perm.refl _
  | a :: l, l₁', l₂', h => by
    cases' e : split l with l₁ l₂
    injection (split_cons_of_eq _ e).symm.trans h; substs l₁' l₂'
    exact ((perm_split e).trans perm_append_comm).cons a
#align list.perm_split List.perm_split

#align list.merge List.merge

/-- Implementation of a merge sort algorithm to sort a list. -/
def mergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => by
    -- Porting note: rewrote to make `mergeSort_cons_cons` proof easier
    let ls := (split (a :: b :: l))
    have := length_split_fst_le l
    have := length_split_snd_le l
    exact merge (r · ·) (mergeSort ls.1) (mergeSort ls.2)
  termination_by l => length l
#align list.merge_sort List.mergeSort

@[nolint unusedHavesSuffices] -- Porting note: false positive
theorem mergeSort_cons_cons {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    mergeSort r (a :: b :: l) = merge (r · ·) (mergeSort r l₁) (mergeSort r l₂) := by
  simp only [mergeSort, h]
#align list.merge_sort_cons_cons List.mergeSort_cons_cons

section Correctness

#align list.perm_merge List.perm_merge

theorem perm_mergeSort : ∀ l : List α, mergeSort r l ~ l
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: l => by
    cases' e : split (a :: b :: l) with l₁ l₂
    cases' length_split_lt e with h₁ h₂
    rw [mergeSort_cons_cons r e]
    apply (perm_merge (r · ·) _ _).trans
    exact
      ((perm_mergeSort l₁).append (perm_mergeSort l₂)).trans (perm_split e).symm
  termination_by l => length l
#align list.perm_merge_sort List.perm_mergeSort

@[simp]
theorem length_mergeSort (l : List α) : (mergeSort r l).length = l.length :=
  (perm_mergeSort r _).length_eq
#align list.length_merge_sort List.length_mergeSort

section TotalAndTransitive

variable {r} [IsTotal α r] [IsTrans α r]

theorem Sorted.merge : ∀ {l l' : List α}, Sorted r l → Sorted r l' → Sorted r (merge (r · ·) l l')
  | [], [], _, _ => by simp
  | [], b :: l', _, h₂ => by simpa using h₂
  | a :: l, [], h₁, _ => by simpa using h₁
  | a :: l, b :: l', h₁, h₂ => by
    by_cases h : a ≼ b
    · suffices ∀ b' ∈ List.merge (r · ·) l (b :: l'), r a b' by
        simpa [h, h₁.of_cons.merge h₂]
      intro b' bm
      rcases show b' = b ∨ b' ∈ l ∨ b' ∈ l' by
          simpa [or_left_comm] using (perm_merge _ _ _).subset bm with
        (be | bl | bl')
      · subst b'
        assumption
      · exact rel_of_sorted_cons h₁ _ bl
      · exact _root_.trans h (rel_of_sorted_cons h₂ _ bl')
    · suffices ∀ b' ∈ List.merge (r · ·) (a :: l) l', r b b' by
        simpa [h, h₁.merge h₂.of_cons]
      intro b' bm
      have ba : b ≼ a := (total_of r _ _).resolve_left h
      have : b' = a ∨ b' ∈ l ∨ b' ∈ l' := by simpa using (perm_merge _ _ _).subset bm
      rcases this with (be | bl | bl')
      · subst b'
        assumption
      · exact _root_.trans ba (rel_of_sorted_cons h₁ _ bl)
      · exact rel_of_sorted_cons h₂ _ bl'
#align list.sorted.merge List.Sorted.merge

variable (r)

theorem sorted_mergeSort : ∀ l : List α, Sorted r (mergeSort r l)
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: l => by
    cases' e : split (a :: b :: l) with l₁ l₂
    cases' length_split_lt e with h₁ h₂
    rw [mergeSort_cons_cons r e]
    exact (sorted_mergeSort l₁).merge (sorted_mergeSort l₂)
  termination_by l => length l
#align list.sorted_merge_sort List.sorted_mergeSort

theorem mergeSort_eq_self [IsAntisymm α r] {l : List α} : Sorted r l → mergeSort r l = l :=
  eq_of_perm_of_sorted (perm_mergeSort _ _) (sorted_mergeSort _ _)
#align list.merge_sort_eq_self List.mergeSort_eq_self

theorem mergeSort_eq_insertionSort [IsAntisymm α r] (l : List α) :
    mergeSort r l = insertionSort r l :=
  eq_of_perm_of_sorted ((perm_mergeSort r l).trans (perm_insertionSort r l).symm)
    (sorted_mergeSort r l) (sorted_insertionSort r l)
#align list.merge_sort_eq_insertion_sort List.mergeSort_eq_insertionSort

end TotalAndTransitive

end Correctness

@[simp]
theorem mergeSort_nil : [].mergeSort r = [] := by rw [List.mergeSort]
#align list.merge_sort_nil List.mergeSort_nil

@[simp]
theorem mergeSort_singleton (a : α) : [a].mergeSort r = [a] := by rw [List.mergeSort]
#align list.merge_sort_singleton List.mergeSort_singleton

end MergeSort

end sort

-- try them out!
--#eval insertionSort (fun m n : ℕ => m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]
--#eval mergeSort     (fun m n : ℕ => m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]
end List
