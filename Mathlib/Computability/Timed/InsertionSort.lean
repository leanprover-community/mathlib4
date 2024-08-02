/-
Copyright (c) 2024 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
/-!
# Timed Insertion Sort
  This file defines a new version of Insertion Sort that, besides sorting the input list, counts the
  number of comparisons made through the execution of the algorithm. Also, it presents proofs of
  its time complexity and its equivalence to the one defined in Data/List/Sort.lean
 ## Main Definition
  - Timed.insertion_sort : list α → (list α × ℕ)
## Main Results
  - Timed.insertion_sort_complexity :
      ∀ l : list α, (Timed.insertionSort r l).snd ≤ l.length * l.length
  - Timed.insertion_sort_equivalence :
      ∀ l : list α, (Timed.insertionSort r l).fst = List.insertionSort r l
-/

namespace Timed

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]
local infixl:50 " ≼ " => r

@[simp] def orderedInsert (a : α) : List α → (List α × Nat)
  | []      => ([a], 0)
  | b :: l => if a ≼ b then (a :: b :: l, 1)
              else let (l', n) := orderedInsert a l
                   (b :: l', n + 1)

@[simp] def insertionSort : List α → (List α × Nat)
  | [] => ([], 0)
  | (h :: t) => let (l', n)  := insertionSort t
                let (l'', m) := orderedInsert r h l'
                (l'', n + m)

theorem orderedInsert_complexity (a : α) :
    ∀ l : List α, (orderedInsert r a l).snd ≤ l.length
  | []     => by simp
  | b :: l' => by
    simp
    split_ifs with h
    · simp
    · simp [orderedInsert_complexity a l']

theorem orderedInsert_equivalence (a : α) : ∀ l : List α,
    (orderedInsert r a l).fst = List.orderedInsert r a l
  | [] => by simp
  | b :: l' => by
    simp
    split_ifs with h
    · rfl
    · simp [orderedInsert_equivalence a l']

theorem orderedInsert_increases_length (a : α) : ∀ l : List α,
    (orderedInsert r a l).fst.length = l.length + 1
  | [] => by simp
  | b :: l' => by
    simp
    split_ifs with h
    · rfl
    · simp [orderedInsert_increases_length a l']

theorem insertionSort_preserves_length : ∀ l : List α,
    (insertionSort r l).fst.length = l.length := fun l =>
  match l with
  | [] => by simp
  | a :: l' => by
    simp
    rw [orderedInsert_increases_length r a (insertionSort r l').fst]
    simp [insertionSort_preserves_length l']

theorem insertionSort_complexity :
    ∀ l : List α, (insertionSort r l).snd ≤ l.length * l.length
  | [] => by simp
  | a :: l' => by
    have same_lengths := insertionSort_preserves_length r l'
    have mid :
      (insertionSort r l').snd + (orderedInsert r a (insertionSort r l').fst).snd ≤
      l'.length * l'.length + (orderedInsert r a (insertionSort r l').fst).snd :=
        add_le_add (insertionSort_complexity l') le_rfl
    have mid₂ :
      l'.length * l'.length + (orderedInsert r a (insertionSort r l').fst).snd ≤
      l'.length * l'.length + l'.length := by
        apply add_le_add le_rfl
        have orderedInsert_compl :=
          orderedInsert_complexity r a (insertionSort r l').fst
        rw [same_lengths] at orderedInsert_compl
        exact orderedInsert_compl
    simp
    linarith

theorem insertionSort_equivalence : ∀ l : List α,
    (insertionSort r l).fst = List.insertionSort r l
  | [] => by simp
  | _ :: l' => by
    simp [orderedInsert_equivalence, insertionSort_equivalence l']

end Timed
