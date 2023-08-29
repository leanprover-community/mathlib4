/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.Nat.Basic

/-!
# Levenshtein distances

We define the Levenshtein edit distance `levenshtein C xy ys` between two `List α`,
with a customizable cost structure `C` for the `delete`, `insert`, and `substitute` operations.

As an auxiliary function, we define `suffixLevenshtein C xs ys`, which gives the list of distances
from each suffix of `xs` to `ys`.
This is defined by recursion on `ys`, using the internal function `Levenshtein.impl`,
which computes `suffixLevenshtein C xs (y :: ys)` using `xs`, `y`, and `suffixLevenshtein C xs ys`.
(This corresponds to the usual algorithm
using the last two rows of the matrix of distances between suffixes.)

After setting up these definitions, we prove lemmas specifying their behaviour,
particularly

```
theorem suffixLevenshtein_eq_tails_map :
  (suffixLevenshtein C xs ys).1 = xs.tails.map fun xs' => levenshtein C xs' ys := ...
```

and

```
theorem levenshtein_cons_cons :
  levenshtein C (x :: xs) (y :: ys) =
    min (C.delete x + levenshtein C xs (y :: ys))
      (min (C.insert y + levenshtein C (x :: xs) ys)
        (C.substitute x y + levenshtein C xs ys)) := ...
```
-/

variable {α β δ : Type _} [AddZeroClass δ] [Min δ]

namespace Levenshtein

/-- A cost structure for Levenshtein edit distance. -/
structure Cost (α β : Type _) (δ : Type _) where
  /-- Cost to delete an element from a list. -/
  delete : α → δ
  /-- Cost in insert an element into a list. -/
  insert : β → δ
  /-- Cost to substitute one elemenet for another in a list. -/
  substitute : α → β → δ

/-- The default cost structure, for which all operations cost `1`. -/
@[simps]
def defaultCost [DecidableEq α] : Cost α α ℕ where
  delete _ := 1
  insert _ := 1
  substitute a b := if a = b then 0 else 1

instance [DecidableEq α] : Inhabited (Cost α α ℕ) := ⟨defaultCost⟩

variable (C : Cost α β δ)

/--
(Implementation detail for `levenshtein`)

Given a list `xs` and the Levenshtein distances from each suffix of `xs` to some other list `ys`,
compute the Levenshtein distances from each suffix of `xs` to `y :: ys`.

(Note that we don't actually need to know `ys` itself here, so it is not an argument.)

The return value is a list of length `x.length + 1`,
and it is convenient for the recursive calls that we bundle this list
with a proof that it is non-empty.
-/
def impl
    (xs : List α) (y : β) (d : {r : List δ // 0 < r.length}) : {r : List δ // 0 < r.length} :=
  let ⟨ds, w⟩ := d
  xs.zip (ds.zip ds.tail) |>.foldr
    (init := ⟨[C.insert y + ds.getLast (List.length_pos.mp w)], by simp⟩)
                                                                   -- 🎉 no goals
    (fun ⟨x, d₀, d₁⟩ ⟨r, w⟩ =>
                                                                                        -- 🎉 no goals
      ⟨min (C.delete x + r[0]) (min (C.insert y + d₀) (C.substitute x y + d₁)) :: r, by simp⟩)

variable {C}
variable (x : α) (xs : List α) (y : β) (d : δ) (ds : List δ) (w : 0 < (d :: ds).length)

-- Note this lemma has an unspecified proof `w'` on the right-hand-side,
-- which will become an extra goal when rewriting.
theorem impl_cons (w' : 0 < List.length ds) :
    impl C (x :: xs) y ⟨d :: ds, w⟩ =
      let ⟨r, w⟩ := impl C xs y ⟨ds, w'⟩
      ⟨min (C.delete x + r[0]) (min (C.insert y + d) (C.substitute x y + ds[0])) :: r, by simp⟩ :=
                                                                                          -- 🎉 no goals
  match ds, w' with | _ :: _, _ => rfl

-- Note this lemma has two unspecified proofs: `h` appears on the left-hand-side
-- and should be found by matching, but `w'` will become an extra goal when rewriting.
theorem impl_cons_fst_zero (h) (w' : 0 < List.length ds) :
    (impl C (x :: xs) y ⟨d :: ds, w⟩).1[0] =
      let ⟨r, w⟩ := impl C xs y ⟨ds, w'⟩
      min (C.delete x + r[0]) (min (C.insert y + d) (C.substitute x y + ds[0])) :=
  match ds, w' with | _ :: _, _ => rfl

theorem impl_length (d : {r : List δ // 0 < r.length}) (w : d.1.length = xs.length + 1) :
    (impl C xs y d).1.length = xs.length + 1 := by
  induction xs generalizing d
  -- ⊢ List.length ↑(impl C [] y d) = List.length [] + 1
  · case nil =>
    rfl
  · case cons x xs ih =>
    dsimp [impl]
    match d, w with
    | ⟨d₁ :: d₂ :: ds, _⟩, w =>
      dsimp
      congr 1
      refine ih ⟨d₂ :: ds, (by simp)⟩ (by simpa using w)

end Levenshtein

open Levenshtein

variable (C : Cost α β δ)

/--
`suffixLevenshtein C xs ys` computes the Levenshtein distance
(using the cost functions provided by a `C : Cost α β δ`)
from each suffix of the list `xs` to the list `ys`.

The first element of this list is the Levenshtein distance from `xs` to `ys`.

Note that if the cost functions do not satisfy the inequalities
* `C.delete a + C.insert b ≥ C.substitute a b`
* `C.substitute a b + C.substitute b c ≥ C.substitute a c`
(or if any values are negative)
then the edit distances calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def suffixLevenshtein (xs : List α) (ys : List β) : {r : List δ // 0 < r.length} :=
  ys.foldr
    (impl C xs)
    (xs.foldr (init := ⟨[0], by simp⟩) (fun a ⟨r, w⟩ => ⟨(C.delete a + r[0]) :: r, by simp⟩))
                                                                                      -- 🎉 no goals
                                -- 🎉 no goals

variable {C}

theorem suffixLevenshtein_length (xs : List α) (ys : List β) :
    (suffixLevenshtein C xs ys).1.length = xs.length + 1 := by
  induction ys
  -- ⊢ List.length ↑(suffixLevenshtein C xs []) = List.length xs + 1
  · case nil =>
    dsimp [suffixLevenshtein]
    induction xs
    · case nil => rfl
    · case cons _ xs ih =>
      simp_all
  · case cons y ys ih =>
    dsimp [suffixLevenshtein]
    rw [impl_length]
    exact ih

-- This is only used in keeping track of estimates.
theorem suffixLevenshtein_eq (xs : List α) (y ys) :
    impl C xs y (suffixLevenshtein C xs ys) = suffixLevenshtein C xs (y :: ys) := by
  rfl
  -- 🎉 no goals

variable (C)

/--
`levenshtein C xs ys` computes the Levenshtein distance
(using the cost functions provided by a `C : Cost α β δ`)
from the list `xs` to the list `ys`.

Note that if the cost functions do not satisfy the inequalities
* `C.delete a + C.insert b ≥ C.substitute a b`
* `C.substitute a b + C.substitute b c ≥ C.substitute a c`
(or if any values are negative)
then the edit distance calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def levenshtein (xs : List α) (ys : List β) : δ :=
  let ⟨r, w⟩ := suffixLevenshtein C xs ys
  r[0]

variable {C}

theorem suffixLevenshtein_nil_nil : (suffixLevenshtein C [] []).1 = [0] := by
  rfl
  -- 🎉 no goals

-- Not sure if this belongs in the main `List` API, or can stay local.
theorem List.eq_of_length_one (x : List α) (w : x.length = 1) :
    have : 0 < x.length := (lt_of_lt_of_eq Nat.zero_lt_one w.symm)
    x = [x[0]] := by
  match x, w with
  | [r], _ => rfl

theorem suffixLevenshtein_nil' (ys : List β) :
    (suffixLevenshtein C [] ys).1 = [levenshtein C [] ys] :=
  List.eq_of_length_one _ (suffixLevenshtein_length [] _)

theorem suffixLevenshtein_cons₂ (xs : List α) (y ys) :
    suffixLevenshtein C xs (y :: ys) = (impl C xs) y (suffixLevenshtein C xs ys) :=
  rfl

theorem suffixLevenshtein_cons₁_aux {x y : {r : List δ // 0 < r.length}}
    (w₀ : x.1[0]'x.2 = y.1[0]'y.2) (w : x.1.tail = y.1.tail) : x = y := by
  match x, y with
  | ⟨hx :: tx, _⟩, ⟨hy :: ty, _⟩ => simp_all

theorem suffixLevenshtein_cons₁
    (x : α) (xs ys) :
    suffixLevenshtein C (x :: xs) ys =
      ⟨levenshtein C (x :: xs) ys ::
        (suffixLevenshtein C xs ys).1, by simp⟩ := by
                                          -- 🎉 no goals
  induction ys
  -- ⊢ suffixLevenshtein C (x :: xs) [] = { val := levenshtein C (x :: xs) [] :: ↑( …
  · case nil =>
    dsimp [levenshtein, suffixLevenshtein]
  · case cons y ys ih =>
    apply suffixLevenshtein_cons₁_aux
    · rfl
    · rw [suffixLevenshtein_cons₂ (x :: xs), ih, impl_cons]
      · rfl
      · simp [suffixLevenshtein_length]

theorem suffixLevenshtein_cons₁_fst (x : α) (xs ys) :
    (suffixLevenshtein C (x :: xs) ys).1 =
      levenshtein C (x :: xs) ys ::
        (suffixLevenshtein C xs ys).1 := by
  simp [suffixLevenshtein_cons₁]
  -- 🎉 no goals

theorem suffixLevenshtein_cons_cons_fst_get_zero
    (x : α) (xs y ys) (w) :
    (suffixLevenshtein C (x :: xs) (y :: ys)).1[0] =
      let ⟨dx, _⟩ := suffixLevenshtein C xs (y :: ys)
      let ⟨dy, _⟩ := suffixLevenshtein C (x :: xs) ys
      let ⟨dxy, _⟩ := suffixLevenshtein C xs ys
      min
        (C.delete x + dx[0])
        (min
          (C.insert y + dy[0])
          (C.substitute x y + dxy[0])) := by
  conv =>
    lhs
    dsimp only [suffixLevenshtein_cons₂]
  simp only [suffixLevenshtein_cons₁]
  -- ⊢ (↑(impl C (x :: xs) y { val := levenshtein C (x :: xs) ys :: ↑(suffixLevensh …
  rw [impl_cons_fst_zero]
  -- ⊢ (match impl C xs y { val := ↑(suffixLevenshtein C xs ys), property := ?w' }  …
  rfl
  -- 🎉 no goals

theorem suffixLevenshtein_eq_tails_map (xs ys) :
    (suffixLevenshtein C xs ys).1 = xs.tails.map fun xs' => levenshtein C xs' ys := by
  induction xs
  -- ⊢ ↑(suffixLevenshtein C [] ys) = List.map (fun xs' => levenshtein C xs' ys) (L …
  · case nil =>
    simp only [List.map, suffixLevenshtein_nil']
  · case cons x xs ih =>
    simp only [List.map, suffixLevenshtein_cons₁, ih]

@[simp]
theorem levenshtein_nil_nil : levenshtein C [] [] = 0 := by
  simp [levenshtein]
  -- 🎉 no goals

@[simp]
theorem levenshtein_nil_cons (y) (ys) :
    levenshtein C [] (y :: ys) = C.insert y + levenshtein C [] ys := by
  dsimp [levenshtein]
  -- ⊢ Cost.insert C y + List.getLast ↑(List.foldr (impl C []) { val := [0], proper …
  congr
  -- ⊢ List.getLast ↑(List.foldr (impl C []) { val := [0], property := suffixLevens …
  rw [List.getLast_eq_get]
  -- ⊢ List.get ↑(List.foldr (impl C []) { val := [0], property := suffixLevenshtei …
  congr
  -- ⊢ List.length ↑(List.foldr (impl C []) { val := [0], property := suffixLevensh …
  rw [show (List.length _) = 1 from _]
  -- ⊢ List.length ↑(List.foldr (impl C []) { val := [0], property := suffixLevensh …
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldr]
    rw [impl_length] <;> simp [ih]

@[simp]
theorem levenshtein_cons_nil (x : α) (xs : List α) :
    levenshtein C (x :: xs) [] = C.delete x + levenshtein C xs [] :=
  rfl

@[simp]
theorem levenshtein_cons_cons
    (x : α) (xs : List α) (y : β) (ys : List β) :
    levenshtein C (x :: xs) (y :: ys) =
      min (C.delete x + levenshtein C xs (y :: ys))
        (min (C.insert y + levenshtein C (x :: xs) ys)
          (C.substitute x y + levenshtein C xs ys)) :=
  suffixLevenshtein_cons_cons_fst_get_zero _ _ _ _ _

#guard
  (suffixLevenshtein Levenshtein.defaultCost "kitten".toList "sitting".toList).1 =
    [3, 3, 4, 5, 6, 6, 7]

#guard levenshtein Levenshtein.defaultCost
  "but our fish said, 'no! no!'".toList
  "'put me down!' said the fish.".toList = 21
