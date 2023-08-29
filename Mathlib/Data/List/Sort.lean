/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm

#align_import data.list.sort from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Sorting algorithms on lists

In this file we define `List.Sorted r l` to be an alias for `Pairwise r l`. This alias is preferred
in the case that `r` is a `<` or `≤`-like relation. Then we define two sorting algorithms:
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

/-- `Sorted r l` is the same as `Pairwise r l`, preferred in the case that `r`
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

@[simp]
theorem sorted_cons {a : α} {l : List α} : Sorted r (a :: l) ↔ (∀ b ∈ l, r a b) ∧ Sorted r l :=
  pairwise_cons
#align list.sorted_cons List.sorted_cons

protected theorem Sorted.nodup {r : α → α → Prop} [IsIrrefl α r] {l : List α} (h : Sorted r l) :
    Nodup l :=
  Pairwise.nodup h
#align list.sorted.nodup List.Sorted.nodup

theorem eq_of_perm_of_sorted [IsAntisymm α r] {l₁ l₂ : List α} (p : l₁ ~ l₂) (s₁ : Sorted r l₁)
    (s₂ : Sorted r l₂) : l₁ = l₂ := by
  induction' s₁ with a l₁ h₁ s₁ IH generalizing l₂
  -- ⊢ [] = l₂
  · exact p.nil_eq
    -- 🎉 no goals
  · have : a ∈ l₂ := p.subset (mem_cons_self _ _)
    -- ⊢ a :: l₁ = l₂
    rcases mem_split this with ⟨u₂, v₂, rfl⟩
    -- ⊢ a :: l₁ = u₂ ++ a :: v₂
    have p' := (perm_cons a).1 (p.trans perm_middle)
    -- ⊢ a :: l₁ = u₂ ++ a :: v₂
    obtain rfl := IH p' (s₂.sublist <| by simp)
    -- ⊢ a :: (u₂ ++ v₂) = u₂ ++ a :: v₂
    change a :: u₂ ++ v₂ = u₂ ++ ([a] ++ v₂)
    -- ⊢ a :: u₂ ++ v₂ = u₂ ++ ([a] ++ v₂)
    rw [← append_assoc]
    -- ⊢ a :: u₂ ++ v₂ = u₂ ++ [a] ++ v₂
    congr
    -- ⊢ a :: u₂ = u₂ ++ [a]
    have : ∀ (x : α) (_ : x ∈ u₂), x = a := fun x m =>
      antisymm ((pairwise_append.1 s₂).2.2 _ m a (mem_cons_self _ _)) (h₁ _ (by simp [m]))
    rw [(@eq_replicate _ a (length u₂ + 1) (a :: u₂)).2,
          (@eq_replicate _ a (length u₂ + 1) (u₂ ++ [a])).2] <;>
        constructor <;>
        -- ⊢ length (u₂ ++ [a]) = length u₂ + 1
        -- ⊢ length (a :: u₂) = length u₂ + 1
      simp [iff_true_intro this, or_comm]
      -- 🎉 no goals
      -- 🎉 no goals
      -- 🎉 no goals
      -- 🎉 no goals
#align list.eq_of_perm_of_sorted List.eq_of_perm_of_sorted

theorem sublist_of_subperm_of_sorted [IsAntisymm α r] {l₁ l₂ : List α} (p : l₁ <+~ l₂)
    (s₁ : l₁.Sorted r) (s₂ : l₂.Sorted r) : l₁ <+ l₂ := by
  let ⟨_, h, h'⟩ := p
  -- ⊢ l₁ <+ l₂
  rwa [← eq_of_perm_of_sorted h (s₂.sublist h') s₁]
  -- 🎉 no goals
#align list.sublist_of_subperm_of_sorted List.sublist_of_subperm_of_sorted

@[simp 1100] --Porting note: higher priority for linter
theorem sorted_singleton (a : α) : Sorted r [a] :=
  pairwise_singleton _ _
#align list.sorted_singleton List.sorted_singleton

theorem Sorted.rel_get_of_lt {l : List α} (h : l.Sorted r) {a b : Fin l.length} (hab : a < b) :
    r (l.get a) (l.get b) :=
  List.pairwise_iff_get.1 h _ _ hab

theorem Sorted.rel_nthLe_of_lt {l : List α} (h : l.Sorted r) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a < b) : r (l.nthLe a ha) (l.nthLe b hb) :=
  List.pairwise_iff_get.1 h ⟨a, ha⟩ ⟨b, hb⟩ hab
#align list.sorted.rel_nth_le_of_lt List.Sorted.rel_nthLe_of_lt

theorem Sorted.rel_get_of_le [IsRefl α r] {l : List α} (h : l.Sorted r) {a b : Fin l.length}
    (hab : a ≤ b) : r (l.get a) (l.get b) := by
  rcases hab.eq_or_lt with (rfl | hlt)
  -- ⊢ r (get l a) (get l a)
  exacts [refl _, h.rel_get_of_lt hlt]
  -- 🎉 no goals

theorem Sorted.rel_nthLe_of_le [IsRefl α r] {l : List α} (h : l.Sorted r) {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a ≤ b) : r (l.nthLe a ha) (l.nthLe b hb) :=
  h.rel_get_of_le hab
#align list.sorted.rel_nth_le_of_le List.Sorted.rel_nthLe_of_le

theorem Sorted.rel_of_mem_take_of_mem_drop {l : List α} (h : List.Sorted r l) {k : ℕ} {x y : α}
    (hx : x ∈ List.take k l) (hy : y ∈ List.drop k l) : r x y := by
  obtain ⟨⟨iy, hiy⟩, rfl⟩ := get_of_mem hy
  -- ⊢ r x (get (drop k l) { val := iy, isLt := hiy })
  obtain ⟨⟨ix, hix⟩, rfl⟩ := get_of_mem hx
  -- ⊢ r (get (take k l) { val := ix, isLt := hix }) (get (drop k l) { val := iy, i …
  rw [get_take', get_drop']
  -- ⊢ r (get l { val := ↑{ val := ix, isLt := hix }, isLt := (_ : ↑{ val := ix, is …
  rw [length_take] at hix
  -- ⊢ r (get l { val := ↑{ val := ix, isLt := hix✝ }, isLt := (_ : ↑{ val := ix, i …
  exact h.rel_nthLe_of_lt _ _ (ix.lt_add_right _ _ (lt_min_iff.mp hix).left)
  -- 🎉 no goals
#align list.sorted.rel_of_mem_take_of_mem_drop List.Sorted.rel_of_mem_take_of_mem_drop

end Sorted

section Monotone

variable {n : ℕ} {α : Type uu} [Preorder α] {f : Fin n → α}

theorem sorted_ofFn_iff {r : α → α → Prop} : (ofFn f).Sorted r ↔ ((· < ·) ⇒ r) f f := by
  simp_rw [Sorted, pairwise_iff_get, get_ofFn, Relator.LiftFun]
  -- ⊢ (∀ (i j : Fin (length (ofFn f))), i < j → r (f (↑(Fin.castIso (_ : length (o …
  exact Iff.symm (Fin.castIso _).surjective.forall₂
  -- 🎉 no goals

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≤ ·)` if and only if `f` is
strictly monotone. -/
@[simp] theorem sorted_lt_ofFn_iff : (ofFn f).Sorted (· < ·) ↔ StrictMono f := sorted_ofFn_iff

/-- The list `List.ofFn f` is sorted with respect to `(· ≤ ·)` if and only if `f` is monotone. -/
@[simp] theorem sorted_le_ofFn_iff : (ofFn f).Sorted (· ≤ ·) ↔ Monotone f :=
  sorted_ofFn_iff.trans monotone_iff_forall_lt.symm

/-- A tuple is monotone if and only if the list obtained from it is sorted. -/
@[deprecated sorted_le_ofFn_iff]
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
    -- ⊢ length (if r a hd then a :: hd :: tl else hd :: orderedInsert r a tl) = Nat. …
    split_ifs <;> simp [orderedInsert_length tl]
    -- ⊢ length (a :: hd :: tl) = Nat.succ (length tl) + 1
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.ordered_insert_length List.orderedInsert_length

/-- An alternative definition of `orderedInsert` using `takeWhile` and `dropWhile`. -/
theorem orderedInsert_eq_take_drop (a : α) :
    ∀ l : List α,
      l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b
  | [] => rfl
  | b :: l => by
    dsimp only [orderedInsert]
    -- ⊢ (if r a b then a :: b :: l else b :: orderedInsert r a l) = takeWhile (fun b …
    split_ifs with h <;> simp [takeWhile, dropWhile, *, orderedInsert_eq_take_drop a l]
    -- ⊢ a :: b :: l = takeWhile (fun b => decide ¬r a b) (b :: l) ++ a :: dropWhile  …
                         -- 🎉 no goals
                         -- 🎉 no goals
#align list.ordered_insert_eq_take_drop List.orderedInsert_eq_take_drop

theorem insertionSort_cons_eq_take_drop (a : α) (l : List α) :
    insertionSort r (a :: l) =
      ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++
        a :: (insertionSort r l).dropWhile fun b => ¬a ≼ b :=
  orderedInsert_eq_take_drop r a _
#align list.insertion_sort_cons_eq_take_drop List.insertionSort_cons_eq_take_drop

section Correctness

open Perm

theorem perm_orderedInsert (a) : ∀ l : List α, orderedInsert r a l ~ a :: l
  | [] => Perm.refl _
  | b :: l => by
    by_cases h : a ≼ b
    -- ⊢ orderedInsert r a (b :: l) ~ a :: b :: l
    · simp [orderedInsert, h]
      -- 🎉 no goals
    · simpa [orderedInsert, h] using ((perm_orderedInsert a l).cons _).trans (Perm.swap _ _ _)
      -- 🎉 no goals
#align list.perm_ordered_insert List.perm_orderedInsert

theorem orderedInsert_count [DecidableEq α] (L : List α) (a b : α) :
    count a (L.orderedInsert r b) = count a L + if a = b then 1 else 0 := by
  rw [(L.perm_orderedInsert r b).count_eq, count_cons]
  -- 🎉 no goals
#align list.ordered_insert_count List.orderedInsert_count

theorem perm_insertionSort : ∀ l : List α, insertionSort r l ~ l
  | [] => Perm.nil
  | b :: l => by
    simpa [insertionSort] using (perm_orderedInsert _ _ _).trans ((perm_insertionSort l).cons b)
    -- 🎉 no goals
#align list.perm_insertion_sort List.perm_insertionSort

variable {r}

/-- If `l` is already `List.Sorted` with respect to `r`, then `insertionSort` does not change
it. -/
theorem Sorted.insertionSort_eq : ∀ {l : List α} (_ : Sorted r l), insertionSort r l = l
  | [], _ => rfl
  | [a], _ => rfl
  | a :: b :: l, h => by
    rw [insertionSort, Sorted.insertionSort_eq, orderedInsert, if_pos]
    -- ⊢ r a b
    exacts [rel_of_sorted_cons h _ (mem_cons_self _ _), h.tail]
    -- 🎉 no goals
#align list.sorted.insertion_sort_eq List.Sorted.insertionSort_eq

section TotalAndTransitive

variable [IsTotal α r] [IsTrans α r]

theorem Sorted.orderedInsert (a : α) : ∀ l, Sorted r l → Sorted r (orderedInsert r a l)
  | [], _ => sorted_singleton a
  | b :: l, h => by
    by_cases h' : a ≼ b
    -- ⊢ Sorted r (List.orderedInsert r a (b :: l))
    · -- Porting note: was
      -- `simpa [orderedInsert, h', h] using fun b' bm => trans h' (rel_of_sorted_cons h _ bm)`
      rw [List.orderedInsert, if_pos h', sorted_cons]
      -- ⊢ (∀ (b_1 : α), b_1 ∈ b :: l → r a b_1) ∧ Sorted r (b :: l)
      exact ⟨forall_mem_cons.2 ⟨h', fun c hc => _root_.trans h' (rel_of_sorted_cons h _ hc)⟩, h⟩
      -- 🎉 no goals
    · suffices ∀ b' : α, b' ∈ List.orderedInsert r a l → r b b' by
        simpa [orderedInsert, h', h.of_cons.orderedInsert a l]
      intro b' bm
      -- ⊢ r b b'
      cases' show b' = a ∨ b' ∈ l by simpa using (perm_orderedInsert _ _ _).subset bm with be bm
      -- ⊢ r b b'
      · subst b'
        -- ⊢ r b a
        exact (total_of r _ _).resolve_left h'
        -- 🎉 no goals
      · exact rel_of_sorted_cons h _ bm
        -- 🎉 no goals
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
                                         -- 🎉 no goals
#align list.split_cons_of_eq List.split_cons_of_eq

theorem length_split_le :
    ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → length l₁ ≤ length l ∧ length l₂ ≤ length l
  | [], _, _, rfl => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | a :: l, l₁', l₂', h => by
    cases' e : split l with l₁ l₂
    -- ⊢ length l₁' ≤ length (a :: l) ∧ length l₂' ≤ length (a :: l)
    injection (split_cons_of_eq _ e).symm.trans h; substs l₁' l₂'
    -- ⊢ length l₁' ≤ length (a :: l) ∧ length l₂' ≤ length (a :: l)
                                                   -- ⊢ length (a :: l₂) ≤ length (a :: l) ∧ length l₁ ≤ length (a :: l)
    cases' length_split_le e with h₁ h₂
    -- ⊢ length (a :: l₂) ≤ length (a :: l) ∧ length l₁ ≤ length (a :: l)
    exact ⟨Nat.succ_le_succ h₂, Nat.le_succ_of_le h₁⟩
    -- 🎉 no goals
#align list.length_split_le List.length_split_le

theorem length_split_lt {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    length l₁ < length (a :: b :: l) ∧ length l₂ < length (a :: b :: l) := by
  cases' e : split l with l₁' l₂'
  -- ⊢ length l₁ < length (a :: b :: l) ∧ length l₂ < length (a :: b :: l)
  injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h; substs l₁ l₂
  -- ⊢ length l₁ < length (a :: b :: l) ∧ length l₂ < length (a :: b :: l)
                                                                      -- ⊢ length (a :: l₁') < length (a :: b :: l) ∧ length (b :: l₂') < length (a ::  …
  cases' length_split_le e with h₁ h₂
  -- ⊢ length (a :: l₁') < length (a :: b :: l) ∧ length (b :: l₂') < length (a ::  …
  exact ⟨Nat.succ_le_succ (Nat.succ_le_succ h₁), Nat.succ_le_succ (Nat.succ_le_succ h₂)⟩
  -- 🎉 no goals
#align list.length_split_lt List.length_split_lt

theorem perm_split : ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → l ~ l₁ ++ l₂
  | [], _, _, rfl => Perm.refl _
  | a :: l, l₁', l₂', h => by
    cases' e : split l with l₁ l₂
    -- ⊢ a :: l ~ l₁' ++ l₂'
    injection (split_cons_of_eq _ e).symm.trans h; substs l₁' l₂'
    -- ⊢ a :: l ~ l₁' ++ l₂'
                                                   -- ⊢ a :: l ~ a :: l₂ ++ l₁
    exact ((perm_split e).trans perm_append_comm).cons a
    -- 🎉 no goals
#align list.perm_split List.perm_split

/-- Merge two sorted lists into one in linear time.

     merge [1, 2, 4, 5] [0, 1, 3, 4] = [0, 1, 1, 2, 3, 4, 4, 5] -/
def merge : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if a ≼ b then a :: merge l (b :: l') else b :: merge (a :: l) l'
  termination_by merge l₁ l₂ => length l₁ + length l₂
#align list.merge List.merge

/-- Implementation of a merge sort algorithm to sort a list. -/
def mergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => by
    -- Porting note: rewrote to make `mergeSort_cons_cons` proof easier
    let ls := (split (a :: b :: l))
    -- ⊢ List α
    have e : split (a :: b :: l) = ⟨ls.1, ls.2⟩ := rfl
    -- ⊢ List α
    have h := length_split_lt e
    -- ⊢ List α
    have := h.1
    -- ⊢ List α
    have := h.2
    -- ⊢ List α
    exact merge r (mergeSort ls.1) (mergeSort ls.2)
    -- 🎉 no goals
  termination_by mergeSort l => length l
#align list.merge_sort List.mergeSort

@[nolint unusedHavesSuffices] --Porting note: false positive
theorem mergeSort_cons_cons {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    mergeSort r (a :: b :: l) = merge r (mergeSort r l₁) (mergeSort r l₂) := by
  simp only [mergeSort, h]
  -- 🎉 no goals
#align list.merge_sort_cons_cons List.mergeSort_cons_cons

section Correctness

theorem perm_merge : ∀ l l' : List α, merge r l l' ~ l ++ l'
  | [], [] => by simp [merge]
                 -- 🎉 no goals
  | [], b :: l' => by simp [merge]
                      -- 🎉 no goals
  | a :: l, [] => by simp [merge]
                     -- 🎉 no goals
  | a :: l, b :: l' => by
    by_cases h : a ≼ b
    -- ⊢ merge r (a :: l) (b :: l') ~ a :: l ++ b :: l'
    · simpa [merge, h] using perm_merge _ _
      -- 🎉 no goals
    · suffices b :: merge r (a :: l) l' ~ a :: (l ++ b :: l') by simpa [merge, h]
      -- ⊢ b :: merge r (a :: l) l' ~ a :: (l ++ b :: l')
      exact ((perm_merge _ _).cons _).trans ((swap _ _ _).trans (perm_middle.symm.cons _))
      -- 🎉 no goals
  termination_by perm_merge l₁ l₂ => length l₁ + length l₂
#align list.perm_merge List.perm_merge

theorem perm_mergeSort : ∀ l : List α, mergeSort r l ~ l
  | [] => by simp [mergeSort]
             -- 🎉 no goals
  | [a] => by simp [mergeSort]
              -- 🎉 no goals
  | a :: b :: l => by
    cases' e : split (a :: b :: l) with l₁ l₂
    -- ⊢ mergeSort r (a :: b :: l) ~ a :: b :: l
    cases' length_split_lt e with h₁ h₂
    -- ⊢ mergeSort r (a :: b :: l) ~ a :: b :: l
    rw [mergeSort_cons_cons r e]
    -- ⊢ merge r (mergeSort r l₁) (mergeSort r l₂) ~ a :: b :: l
    apply (perm_merge r _ _).trans
    -- ⊢ mergeSort r l₁ ++ mergeSort r l₂ ~ a :: b :: l
    exact
      ((perm_mergeSort l₁).append (perm_mergeSort l₂)).trans (perm_split e).symm
  termination_by perm_mergeSort l => length l
#align list.perm_merge_sort List.perm_mergeSort

@[simp]
theorem length_mergeSort (l : List α) : (mergeSort r l).length = l.length :=
  (perm_mergeSort r _).length_eq
#align list.length_merge_sort List.length_mergeSort

section TotalAndTransitive

variable {r} [IsTotal α r] [IsTrans α r]

theorem Sorted.merge : ∀ {l l' : List α}, Sorted r l → Sorted r l' → Sorted r (merge r l l')
  | [], [], _, _ => by simp [List.merge]
                       -- 🎉 no goals
  | [], b :: l', _, h₂ => by simpa [List.merge] using h₂
                             -- 🎉 no goals
  | a :: l, [], h₁, _ => by simpa [List.merge] using h₁
                            -- 🎉 no goals
  | a :: l, b :: l', h₁, h₂ => by
    by_cases h : a ≼ b
    -- ⊢ Sorted r (List.merge r (a :: l) (b :: l'))
    · suffices ∀ (b' : α) (_ : b' ∈ List.merge r l (b :: l')), r a b' by
        simpa [List.merge, h, h₁.of_cons.merge h₂]
      intro b' bm
      -- ⊢ r a b'
      rcases show b' = b ∨ b' ∈ l ∨ b' ∈ l' by
          simpa [or_left_comm] using (perm_merge _ _ _).subset bm with
        (be | bl | bl')
      · subst b'
        -- ⊢ r a b
        assumption
        -- 🎉 no goals
      · exact rel_of_sorted_cons h₁ _ bl
        -- 🎉 no goals
      · exact _root_.trans h (rel_of_sorted_cons h₂ _ bl')
        -- 🎉 no goals
    · suffices ∀ (b' : α) (_ : b' ∈ List.merge r (a :: l) l'), r b b' by
        simpa [List.merge, h, h₁.merge h₂.of_cons]
      intro b' bm
      -- ⊢ r b b'
      have ba : b ≼ a := (total_of r _ _).resolve_left h
      -- ⊢ r b b'
      have : b' = a ∨ b' ∈ l ∨ b' ∈ l' := by simpa using (perm_merge _ _ _).subset bm
      -- ⊢ r b b'
      rcases this with (be | bl | bl')
      · subst b'
        -- ⊢ r b a
        assumption
        -- 🎉 no goals
      · exact _root_.trans ba (rel_of_sorted_cons h₁ _ bl)
        -- 🎉 no goals
      · exact rel_of_sorted_cons h₂ _ bl'
        -- 🎉 no goals
  termination_by Sorted.merge l₁ l₂ _ _ => length l₁ + length l₂
#align list.sorted.merge List.Sorted.merge

variable (r)

theorem sorted_mergeSort : ∀ l : List α, Sorted r (mergeSort r l)
  | [] => by simp [mergeSort]
             -- 🎉 no goals
  | [a] => by simp [mergeSort]
              -- 🎉 no goals
  | a :: b :: l => by
    cases' e : split (a :: b :: l) with l₁ l₂
    -- ⊢ Sorted r (mergeSort r (a :: b :: l))
    cases' length_split_lt e with h₁ h₂
    -- ⊢ Sorted r (mergeSort r (a :: b :: l))
    rw [mergeSort_cons_cons r e]
    -- ⊢ Sorted r (merge r (mergeSort r l₁) (mergeSort r l₂))
    exact (sorted_mergeSort l₁).merge (sorted_mergeSort l₂)
    -- 🎉 no goals
  termination_by sorted_mergeSort l => length l
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
                                                  -- 🎉 no goals
#align list.merge_sort_nil List.mergeSort_nil

@[simp]
theorem mergeSort_singleton (a : α) : [a].mergeSort r = [a] := by rw [List.mergeSort]
                                                                  -- 🎉 no goals
#align list.merge_sort_singleton List.mergeSort_singleton

end MergeSort

end sort

-- try them out!
--#eval insertionSort (fun m n : ℕ => m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]
--#eval mergeSort     (fun m n : ℕ => m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]
end List
