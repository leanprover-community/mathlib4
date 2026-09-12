/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring

/-!
# Shuffles of two words

A Lean 4 port of `theories/Combi/shuffle.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The *shuffle* of two words `u` and `v` is the list of all the words obtained by
interleaving `u` and `v`, keeping the letters of `u` and the letters of `v` in
their relative order.  As in the Coq development the shuffle is a *list* of
words, listing every interleaving pattern separately: repetitions do occur when
`u` and `v` share letters, and the total number of entries is the binomial
coefficient `(|u| + |v|).choose |u|`.

## Main definitions

* `List.shuffle u v` : the list of the shuffles of `u` and `v` (Coq `shuffle`).
* `List.IsShuffle u v w` : `w` is an interleaving of `u` and `v`.

## Main results

* `List.mem_shuffle_iff` : membership in `shuffle u v` is exactly `IsShuffle u v w`
  (Coq `mem_shuffle`).
* `List.length_shuffle` : `shuffle u v` has `(|u| + |v|).choose |u|` entries
  (Coq `size_shuffle`).
* `List.shuffle_perm_comm` : `shuffle u v` and `shuffle v u` are permutations of
  each other (Coq `perm_eq_shuffle`).
* `List.perm_append_of_mem_shuffle` : a shuffle of `u` and `v` is a permutation of
  `u ++ v` (Coq `perm_eq_shuffle_append`).
* `List.sublist_left_of_mem_shuffle`, `List.sublist_right_of_mem_shuffle` : both
  `u` and `v` are subwords of any of their shuffles.
* `List.isShuffle_filter`, `List.IsShuffle.filter_eq_left`,
  `List.IsShuffle.filter_eq_right` : a word is the shuffle of the subword of the letters
  satisfying a predicate and of the subword of the other letters, and this decomposition
  is the only one of this form.
-/

@[expose] public section

namespace List

open List

variable {T : Type*}

/-! ### The shuffle of two words -/

/-- The list of all the interleavings of the words `u` and `v` (Coq `shuffle`). -/
def shuffle : List T → List T → List (List T)
  | [], v => [v]
  | u@(_ :: _), [] => [u]
  | a :: u, b :: v =>
      (shuffle u (b :: v)).map (a :: ·) ++ (shuffle (a :: u) v).map (b :: ·)
  termination_by u v => u.length + v.length

@[simp] lemma shuffle_nil_left (v : List T) : shuffle [] v = [v] := by
  cases v <;> rw [shuffle]

@[simp] lemma shuffle_nil_right (u : List T) : shuffle u [] = [u] := by
  cases u <;> rw [shuffle]

lemma shuffle_cons_cons (a b : T) (u v : List T) :
    shuffle (a :: u) (b :: v) =
      (shuffle u (b :: v)).map (a :: ·) ++ (shuffle (a :: u) v).map (b :: ·) := by
  rw [shuffle]

/-! ### The predicate describing the shuffles -/

/-- `IsShuffle u v w` states that the word `w` is obtained by interleaving the
words `u` and `v`, keeping the letters of each of them in order. -/
inductive IsShuffle : List T → List T → List T → Prop
  /-- The empty word is the only shuffle of two empty words. -/
  | nil : IsShuffle [] [] []
  /-- Take the next letter from the left word. -/
  | left {a : T} {u v w : List T} : IsShuffle u v w → IsShuffle (a :: u) v (a :: w)
  /-- Take the next letter from the right word. -/
  | right {b : T} {u v w : List T} : IsShuffle u v w → IsShuffle u (b :: v) (b :: w)

lemma isShuffle_nil_left (v : List T) : IsShuffle [] v v := by
  induction v with
  | nil => exact IsShuffle.nil
  | cons b v ih => exact ih.right

lemma isShuffle_nil_right (u : List T) : IsShuffle u [] u := by
  induction u with
  | nil => exact IsShuffle.nil
  | cons a u ih => exact ih.left

@[simp] lemma isShuffle_nil_left_iff {v w : List T} : IsShuffle [] v w ↔ w = v := by
  refine ⟨fun h ↦ ?_, by rintro rfl; exact isShuffle_nil_left _⟩
  induction v generalizing w with
  | nil => cases h; rfl
  | cons b v ih =>
    cases h with
    | right h => rw [ih h]

@[simp] lemma isShuffle_nil_right_iff {u w : List T} : IsShuffle u [] w ↔ w = u := by
  refine ⟨fun h ↦ ?_, by rintro rfl; exact isShuffle_nil_right _⟩
  induction u generalizing w with
  | nil => cases h; rfl
  | cons a u ih =>
    cases h with
    | left h => rw [ih h]

/-- Membership in `shuffle u v` is described by `IsShuffle` (Coq `mem_shuffle`). -/
theorem mem_shuffle_iff : ∀ (u v w : List T), w ∈ shuffle u v ↔ IsShuffle u v w
  | [], v, w => by simp
  | a :: u, [], w => by simp
  | a :: u, b :: v, w => by
    rw [shuffle_cons_cons, List.mem_append, List.mem_map, List.mem_map]
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro (⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩)
      · exact (((mem_shuffle_iff u (b :: v) w').mp hw').left)
      · exact (((mem_shuffle_iff (a :: u) v w').mp hw').right)
    · cases h with
      | left h =>
        exact Or.inl ⟨_, (mem_shuffle_iff u (b :: v) _).mpr h, rfl⟩
      | right h =>
        exact Or.inr ⟨_, (mem_shuffle_iff (a :: u) v _).mpr h, rfl⟩
  termination_by u v _ => u.length + v.length

/-! ### Counting the shuffles -/

/-- There are `(|u| + |v|).choose |u|` shuffles of `u` and `v` (Coq `size_shuffle`). -/
theorem length_shuffle : ∀ u v : List T,
    (shuffle u v).length = (u.length + v.length).choose u.length
  | [], v => by simp
  | a :: u, [] => by simp
  | a :: u, b :: v => by
    simp [shuffle_cons_cons, length_shuffle u (b :: v), length_shuffle (a :: u) v,
      show u.length + (v.length + 1) = u.length + v.length + 1 by ring,
      show u.length + 1 + v.length = u.length + v.length + 1 by ring,
      show u.length + 1 + (v.length + 1) = (u.length + v.length + 1) + 1 by ring,
      Nat.choose_succ_succ']
  termination_by u v => u.length + v.length

/-! ### Basic properties of the shuffles -/

/-- A shuffle of `u` and `v` is a permutation of `u ++ v`. -/
theorem perm_append_of_isShuffle {u v w : List T} (h : IsShuffle u v w) : w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact List.Perm.trans (ih.cons _) (List.perm_middle).symm

theorem perm_append_of_mem_shuffle {u v w : List T} (h : w ∈ shuffle u v) :
    w.Perm (u ++ v) :=
  perm_append_of_isShuffle ((mem_shuffle_iff u v w).mp h)

/-- Both words are subwords of any of their shuffles. -/
theorem sublist_left_of_isShuffle {u v w : List T} (h : IsShuffle u v w) : u.Sublist w := by
  induction h with
  | nil => exact List.Sublist.refl _
  | left _ ih => exact ih.cons_cons _
  | right _ ih => exact ih.cons _

theorem sublist_right_of_isShuffle {u v w : List T} (h : IsShuffle u v w) : v.Sublist w := by
  induction h with
  | nil => exact List.Sublist.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact ih.cons_cons _

theorem sublist_left_of_mem_shuffle {u v w : List T} (h : w ∈ shuffle u v) : u.Sublist w :=
  sublist_left_of_isShuffle ((mem_shuffle_iff u v w).mp h)

theorem sublist_right_of_mem_shuffle {u v w : List T} (h : w ∈ shuffle u v) : v.Sublist w :=
  sublist_right_of_isShuffle ((mem_shuffle_iff u v w).mp h)

theorem length_of_isShuffle {u v w : List T} (h : IsShuffle u v w) :
    w.length = u.length + v.length := by
  simpa using (perm_append_of_isShuffle h).length_eq

/-- The concatenation `u ++ v` is one of the shuffles of `u` and `v`. -/
theorem isShuffle_append (u v : List T) : IsShuffle u v (u ++ v) := by
  induction u with
  | nil => exact isShuffle_nil_left v
  | cons a u ih => exact ih.left

theorem append_mem_shuffle (u v : List T) : u ++ v ∈ shuffle u v :=
  (mem_shuffle_iff u v _).mpr (isShuffle_append u v)

/-- Shuffling is commutative on the level of the predicate. -/
theorem IsShuffle.symm {u v w : List T} (h : IsShuffle u v w) : IsShuffle v u w := by
  induction h with
  | nil => exact IsShuffle.nil
  | left _ ih => exact ih.right
  | right _ ih => exact ih.left

/-- `shuffle u v` and `shuffle v u` list the same words, with the same multiplicities
(Coq `perm_eq_shuffle`). -/
theorem shuffle_perm_comm : ∀ u v : List T, (shuffle u v).Perm (shuffle v u)
  | [], v => by simp
  | a :: u, [] => by simp
  | a :: u, b :: v => by
    rw [shuffle_cons_cons, shuffle_cons_cons]
    exact List.Perm.trans (List.Perm.append ((shuffle_perm_comm u (b :: v)).map _)
      ((shuffle_perm_comm (a :: u) v).map _)) (List.perm_append_comm)
  termination_by u v => u.length + v.length

theorem mem_shuffle_comm {u v w : List T} : w ∈ shuffle u v ↔ w ∈ shuffle v u :=
  ⟨fun h => (mem_shuffle_iff v u w).mpr ((mem_shuffle_iff u v w).mp h).symm,
   fun h => (mem_shuffle_iff u v w).mpr ((mem_shuffle_iff v u w).mp h).symm⟩

/-! ### Shuffles and filtering -/

/-- A word is the shuffle of the subword of the letters satisfying a predicate and of the
subword of the letters not satisfying it. -/
theorem isShuffle_filter (p : T → Bool) (w : List T) :
    IsShuffle (w.filter p) (w.filter fun x => !p x) w := by
  induction w with
  | nil => exact IsShuffle.nil
  | cons a w ih =>
    by_cases ha : p a
    · rw [List.filter_cons_of_pos ha, List.filter_cons_of_neg (by simp [ha])]
      exact ih.left
    · rw [List.filter_cons_of_neg (by simpa using ha),
        List.filter_cons_of_pos (by simp [Bool.not_eq_true] at ha ⊢; simp [ha])]
      exact ih.right

/-- If all the letters of `u` satisfy `p` and none of the letters of `v` does, then the
letters of a shuffle of `u` and `v` satisfying `p` are exactly `u`. -/
theorem IsShuffle.filter_eq_left {p : T → Bool} {u v w : List T} (h : IsShuffle u v w)
    (hu : ∀ x ∈ u, p x = true) (hv : ∀ x ∈ v, p x = false) : w.filter p = u := by
  induction h with
  | nil => rfl
  | @left a u v w _ ih =>
    rw [List.filter_cons_of_pos (hu a (by simp))]
    exact congrArg (a :: ·) (ih (fun x hx => hu x (by simp [hx])) hv)
  | @right b u v w _ ih =>
    rw [List.filter_cons_of_neg (by simp [hv b (by simp)])]
    exact ih hu fun x hx => hv x (by simp [hx])

/-- If all the letters of `u` satisfy `p` and none of the letters of `v` does, then the
letters of a shuffle of `u` and `v` not satisfying `p` are exactly `v`. -/
theorem IsShuffle.filter_eq_right {p : T → Bool} {u v w : List T} (h : IsShuffle u v w)
    (hu : ∀ x ∈ u, p x = true) (hv : ∀ x ∈ v, p x = false) :
    (w.filter fun x => !p x) = v := by
  induction h with
  | nil => rfl
  | @left a u v w _ ih =>
    rw [List.filter_cons_of_neg (by simp [hu a (by simp)])]
    exact ih (fun x hx => hu x (by simp [hx])) hv
  | @right b u v w _ ih =>
    rw [List.filter_cons_of_pos (by simp [hv b (by simp)])]
    exact congrArg (b :: ·) (ih hu fun x hx => hv x (by simp [hx]))

end List
