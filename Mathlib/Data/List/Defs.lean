/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Lean
import Std.Data.List.Basic
import Mathlib.Init.Data.Nat.Basic

/-!
## Definitions on Lists

This file contains various definitions on `List`. It does not contain
proofs about these definitions, those are contained in other files in `Mathlib.Data.List`.
-/

namespace List

def mmap [Monad m] (f : α → m β) (xs : List α) : m (List β) := xs.mapM f

def mmap' [Monad m] (f : α → m β) (xs : List α) : m Unit := xs.forM (discard ∘ f)

/-- Filters and maps elements of a list -/
def mmapFilter {m : Type → Type v} [Monad m] {α β} (f : α → m (Option β)) : List α → m (List β)
| [] => pure []
| h :: t => do
  let b ← f h
  let t' ← t.mmapFilter f
  pure $ match b with
  | none => t'
  | some x => x :: t'

/--
`mmapUpperTriangle f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.
```
mmapUpperTriangle f [1, 2, 3] =
  return [← f 1 1, ← f 1 2, ← f 1 3, ← f 2 2, ← f 2 3, ← f 3 3]
``` -/
def mmapUpperTriangle {m} [Monad m] {α β : Type u} (f : α → α → m β) : List α → m (List β)
| [] => pure []
| h :: t => return (← f h h) :: (← t.mmap (f h)) ++ (← t.mmapUpperTriangle f)

/--
`mmap'Diag f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.
```
mmap'Diag f [1, 2, 3] = do f 1 1; f 1 2; f 1 3; f 2 2; f 2 3; f 3 3
``` -/
def mmap'Diag {m} [Monad m] {α} (f : α → α → m Unit) : List α → m Unit
| [] => return ()
| h :: t => do f h h; t.mmap' (f h); t.mmap'Diag f

protected def traverse {F : Type u → Type v} [Applicative F] {α β} (f : α → F β) : List α → F (List β)
| [] => pure []
| x :: xs => cons <$> f x <*> List.traverse f xs

/--
`List.slice n m xs` removes a slice of length `m` at index `n` in list `xs`.
-/
def slice {α} : ℕ → ℕ → List α → List α
| 0, n, xs => xs.drop n
| _+1, _, [] => []
| n+1, m, x :: xs => x :: slice n m xs

/--
Left-biased version of `List.map₂`. `map₂Left' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.
```
map₂Left' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])
map₂Left' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
@[simp]
def map₂Left' (f : α → Option β → γ) : List α → List β → List γ × List β
| [], bs => ([], bs)
| a :: as, [] => ((a :: as).map fun a => f a none, [])
| a :: as, b :: bs => let r := map₂Left' f as bs; (f a (some b) :: r.1, r.2)

/--
Right-biased version of `List.map₂`. `map₂Right' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.
```
map₂Right' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])
map₂Right' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
def map₂Right' (f : Option α → β → γ) (as : List α) (bs : List β) : List γ × List α :=
  map₂Left' (flip f) bs as

/--
Left-biased version of `List.map₂`. `map₂Left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.
```
map₂Left prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]
map₂Left prod.mk [1] ['a', 'b'] = [(1, some 'a')]
map₂Left f as bs = (map₂Left' f as bs).fst
```
-/
@[simp]
def map₂Left (f : α → Option β → γ) : List α → List β → List γ
| [], _ => []
| a :: as, [] => (a :: as).map fun a => f a none
| a :: as, b :: bs => f a (some b) :: map₂Left f as bs

/--
Right-biased version of `List.map₂`. `map₂Right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.
```
map₂Right prod.mk [1, 2] ['a'] = [(some 1, 'a')]
map₂Right prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]
map₂Right f as bs = (map₂Right' f as bs).fst
```
-/
def map₂Right (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  map₂Left (flip f) bs as

end List
