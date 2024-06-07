/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.List.EditDistance.Bounds
import Mathlib.Order.Estimator

/-!
# `Estimator` for Levenshtein distance.

The usual algorithm for computing Levenshtein distances
provides successively better lower bounds for the Levenshtein distance as it runs,
as proved in `Mathlib.Data.List.EditDistance.Bounds`.

In this file we package that fact as an instance of
```
Estimator (Thunk.mk fun _ => levenshtein C xs ys) (LevenshteinEstimator C xs ys)
```
allowing us to use the `Estimator` framework for Levenshtein distances.

This is then used in the implementation of `rewrite_search`
to avoid needing the entire edit distance calculation in unlikely search paths.
-/

set_option autoImplicit true

variable {α β δ : Type} [CanonicallyLinearOrderedAddCommMonoid δ]
    (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β)

/--
Data showing that the Levenshtein distance from `xs` to `ys`
is bounded below by the minimum Levenshtein distance between some suffix of `xs`
and a particular suffix of `ys`.

This bound is (non-strict) monotone as we take longer suffixes of `ys`.

This is an auxiliary definition for the later `LevenshteinEstimator`:
this variant constructs a lower bound for the pair consisting of
the Levenshtein distance from `xs` to `ys`,
along with the length of `ys`.
-/
structure LevenshteinEstimator' : Type where
  /-- The prefix of `ys` that is not is not involved in the bound, in reverse order. -/
  pre_rev : List β
  /-- The suffix of `ys`, such that the distance from `xs` to `ys` is bounded below
  by the minimum distance from any suffix of `xs` to this suffix. -/
  suff : List β
  /-- Witness that `ys` has been decomposed into a prefix and suffix. -/
  split : pre_rev.reverse ++ suff = ys
  /-- The distances from each suffix of `xs` to `suff`. -/
  distances : {r : List δ // 0 < r.length}
  /-- Witness that `distances` are correct. -/
  distances_eq : distances = suffixLevenshtein C xs suff
  /-- The current bound on the pair (distance from `xs` to `ys`, length of `ys`). -/
  bound : δ × ℕ
  /-- Predicate describing the current bound. -/
  bound_eq : bound = match pre_rev with
    | [] => (distances.1[0]'(distances.2), ys.length)
    | _ => (List.minimum_of_length_pos distances.2, suff.length)

instance : EstimatorData (Thunk.mk fun _ => (levenshtein C xs ys, ys.length))
    (LevenshteinEstimator' C xs ys) where
  bound e := e.bound
  improve e := match e.pre_rev, e.split with
    | [], _ => none
    | y :: ys, split => some
      { pre_rev := ys
        suff := y :: e.suff
        split := by simpa using split
        distances := Levenshtein.impl C xs y e.distances
        distances_eq := e.distances_eq ▸ suffixLevenshtein_eq xs y e.suff
        bound := _
        bound_eq := rfl }

instance estimator' :
    Estimator (Thunk.mk fun _ => (levenshtein C xs ys, ys.length))
      (LevenshteinEstimator' C xs ys) where
  bound_le e := match e.pre_rev, e.split, e.bound_eq with
  | [], split, eq => by
    simp only [List.reverse_nil, List.nil_append] at split
    rw [e.distances_eq] at eq
    simp only [List.getElem_eq_get] at eq
    rw [split] at eq
    exact eq.le
  | y :: t, split, eq => by
    rw [e.distances_eq] at eq
    simp only at eq
    dsimp [EstimatorData.bound]
    rw [eq]
    simp only [← split]
    constructor
    · simp only [List.minimum_of_length_pos_le_iff]
      exact suffixLevenshtein_minimum_le_levenshtein_append _ _ _
    · exact List.length_le_of_sublist (List.sublist_append_right _ _)
  improve_spec e := by
    dsimp [EstimatorData.improve]
    match e.pre_rev, e.split, e.bound_eq, e.distances_eq with
    | [], split, eq, _ =>
      simp only [List.reverse_nil, List.nil_append] at split
      rw [e.distances_eq] at eq
      simp only [List.getElem_eq_get] at eq
      rw [split] at eq
      exact eq
    | [y], split, b_eq, d_eq =>
      simp only [EstimatorData.bound, Prod.lt_iff, List.reverse_nil, List.nil_append]
      right
      have b_eq :
          e.bound = (List.minimum_of_length_pos e.distances.property, List.length e.suff) := by
        simpa using b_eq
      rw [b_eq]
      constructor
      · refine (?_ : _ ≤ _).trans (List.minimum_of_length_pos_le_getElem _)
        simp only [List.minimum_of_length_pos_le_iff, List.coe_minimum_of_length_pos, d_eq]
        apply le_suffixLevenshtein_cons_minimum
      · simp [← split]
    | y₁ :: y₂ :: t, split, b_eq, d_eq =>
      simp only [EstimatorData.bound, Prod.lt_iff]
      right
      have b_eq :
          e.bound = (List.minimum_of_length_pos e.distances.property, List.length e.suff) := by
        simpa using b_eq
      rw [b_eq]
      constructor
      · simp only [d_eq, List.minimum_of_length_pos_le_iff, List.coe_minimum_of_length_pos]
        apply le_suffixLevenshtein_cons_minimum
      · exact Nat.lt.base _

/-- An estimator for Levenshtein distances. -/
def LevenshteinEstimator : Type _ :=
  Estimator.fst (Thunk.mk fun _ => (levenshtein C xs ys, ys.length)) (LevenshteinEstimator' C xs ys)

instance [∀ a : δ × ℕ, WellFoundedGT { x // x ≤ a }] :
    Estimator (Thunk.mk fun _ => levenshtein C xs ys) (LevenshteinEstimator C xs ys) :=
  Estimator.fstInst (Thunk.mk fun _ => _) (Thunk.mk fun _ => _) (estimator' C xs ys)

/-- The initial estimator for Levenshtein distances. -/
instance (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β) :
    Bot (LevenshteinEstimator C xs ys) where
  bot :=
  { inner :=
    { pre_rev := ys.reverse
      suff := []
      split := by simp
      distances_eq := rfl
      bound_eq := rfl } }
