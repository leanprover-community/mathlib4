/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.Vector.Basic

/-!
  This file establishes a `snoc : Vector α n → α → Vector α (n+1)` operation, that appends a single
  element to the back of a vector.

  It provides a collection of lemmas that show how different `Vector` operations reduce when their
  argument is `snoc xs x`.

  Also, an alternative, reverse, induction principle is added, that breaks down a vector into
  `snoc xs x` for its inductive case. Effectively doing induction from right-to-left
-/

set_option autoImplicit true

namespace Vector

/-- Append a single element to the end of a vector -/
def snoc : Vector α n → α → Vector α (n+1) :=
  fun xs x => append xs (x ::ᵥ Vector.nil)

/-!
## Simplification lemmas
-/
section Simp
  variable (xs : Vector α n)

@[simp]
theorem snoc_cons : (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y) :=
  rfl

@[simp]
theorem snoc_nil : (nil.snoc x) = x ::ᵥ nil :=
  rfl

@[simp]
theorem reverse_cons : reverse (x ::ᵥ xs) = (reverse xs).snoc x := by
  cases xs
  -- ⊢ reverse (x ::ᵥ { val := val✝, property := property✝ }) = snoc (reverse { val …
  simp only [reverse, cons, toList_mk, List.reverse_cons, snoc]
  -- ⊢ { val := List.reverse val✝ ++ [x], property := (_ : (fun l => List.length l  …
  congr
  -- 🎉 no goals

@[simp]
theorem reverse_snoc : reverse (xs.snoc x) = x ::ᵥ (reverse xs) := by
  cases xs
  -- ⊢ reverse (snoc { val := val✝, property := property✝ } x) = x ::ᵥ reverse { va …
  simp only [reverse, snoc, cons, toList_mk]
  -- ⊢ { val := List.reverse (toList (append { val := val✝, property := property✝ } …
  congr
  -- ⊢ List.reverse (toList (append { val := val✝, property := property✝ } { val := …
  simp [toList, (·++·), Vector.append, Append.append]
  -- ⊢ [] ++ [x] ++ List.reverse val✝ = x :: List.reverse val✝
  rfl
  -- 🎉 no goals

theorem replicate_succ_to_snoc (val : α) :
    replicate (n+1) val = (replicate n val).snoc val := by
  clear xs
  -- ⊢ replicate (n + 1) val = snoc (replicate n val) val
  induction n
  -- ⊢ replicate (Nat.zero + 1) val = snoc (replicate Nat.zero val) val
  case zero => rfl
  -- ⊢ replicate (Nat.succ n✝ + 1) val = snoc (replicate (Nat.succ n✝) val) val
  -- 🎉 no goals
  case succ n ih =>
    rw [replicate_succ]
    conv => {
      rhs; rw [replicate_succ]
    }
    rw[snoc_cons, ih]

end Simp

/-!
## Reverse induction principle
-/
section Induction

/-- Define `C v` by *reverse* induction on `v : Vector α n`.
    That is, break the vector down starting from the right-most element, using `snoc`

    This function has two arguments: `nil` handles the base case on `C nil`,
    and `snoc` defines the inductive step using `∀ x : α, C xs → C (xs.snoc x)`.

    This can be used as `induction v using Vector.revInductionOn`. -/
@[elab_as_elim]
def revInductionOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (x : α), C xs → C (xs.snoc x)) :
    C v :=
  cast (by simp) <| inductionOn
           -- 🎉 no goals
    (C := fun v => C v.reverse)
    v.reverse
    nil
    (@fun n x xs (r : C xs.reverse) => cast (by simp) <| snoc xs.reverse x r)
                                                -- 🎉 no goals

/-- Define `C v w` by *reverse* induction on a pair of vectors `v : Vector α n` and
    `w : Vector β n`. -/
@[elab_as_elim]
def revInductionOn₂ {C : ∀ {n : ℕ}, Vector α n → Vector β n → Sort*} {n : ℕ}
    (v : Vector α n) (w : Vector β n)
    (nil : C nil nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (ys : Vector β n) (x : α) (y : β),
      C xs ys → C (xs.snoc x) (ys.snoc y)) :
    C v w :=
  cast (by simp) <| inductionOn₂
           -- 🎉 no goals
    (C := fun v w => C v.reverse w.reverse)
    v.reverse
    w.reverse
    nil
    (@fun n x y xs ys (r : C xs.reverse ys.reverse) =>
      cast (by simp) <| snoc xs.reverse ys.reverse x y r)
               -- 🎉 no goals

/-- Define `C v` by *reverse* case analysis, i.e. by handling the cases `nil` and `xs.snoc x`
    separately -/
@[elab_as_elim]
def revCasesOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (x : α), C (xs.snoc x)) :
    C v :=
  revInductionOn v nil fun xs x _ => snoc xs x

end Induction

/-!
## More simplification lemmas
-/

section Simp

variable (xs : Vector α n)

@[simp]
theorem map_snoc : map f (xs.snoc x) = (map f xs).snoc (f x) := by
  induction xs using Vector.inductionOn <;> simp_all
  -- ⊢ map f (snoc nil x) = snoc (map f nil) (f x)
                                            -- 🎉 no goals
                                            -- 🎉 no goals

@[simp]
theorem mapAccumr_nil : mapAccumr f Vector.nil s = (s, Vector.nil) :=
  rfl

@[simp]
theorem mapAccumr_snoc :
    mapAccumr f (xs.snoc x) s
    = let q := f x s
      let r := mapAccumr f xs q.1
      (r.1, r.2.snoc q.2) := by
  induction xs using Vector.inductionOn
  · rfl
    -- 🎉 no goals
  · simp[*]
    -- 🎉 no goals

variable (ys : Vector β n)

@[simp]
theorem map₂_snoc : map₂ f (xs.snoc x) (ys.snoc y) = (map₂ f xs ys).snoc (f x y) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all
  -- ⊢ map₂ f (snoc nil x) (snoc nil y) = snoc (map₂ f nil nil) (f x y)
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals

@[simp]
theorem mapAccumr₂_nil : mapAccumr₂ f Vector.nil Vector.nil s = (s, Vector.nil) :=
  rfl

@[simp]
theorem mapAccumr₂_snoc (f : α → β → σ → σ × φ) (x : α) (y : β) :
    mapAccumr₂ f (xs.snoc x) (ys.snoc y) c
    = let q := f x y c
      let r := mapAccumr₂ f xs ys q.1
      (r.1, r.2.snoc q.2) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals

end Simp
end Vector
