/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.ListM.Basic
import Mathlib.Data.ULift

/-!
# Functions for splitting monadic lazy lists.
-/

namespace ListM

variable {α β : Type u} {m : Type u → Type u} [Monad m]

/--
Extract the prefix of a lazy list consisting of elements up to and including
the first element satisfying a monadic predicate.
Return (in the monad) the prefix as a `List`, along with the remaining elements as a `ListM`.
-/
partial def getUpToFirstM (L : ListM m α) (p : α → m (ULift Bool)) : m (List α × ListM m α) := do
  match ← L.uncons with
  | none => return ([], nil)
  | some (x, xs) => (if (← p x).down then
      return ([x], xs)
    else do
      let (acc, R) ← getUpToFirstM xs p
      return (x :: acc, R))

/--
Extract the prefix of a lazy list consisting of elements up to and including
the first element satisfying a predicate.
Return (in the monad) the prefix as a `List`, along with the remaining elements as a `ListM`.
-/
def getUpToFirst (L : ListM m α) (p : α → Bool) : m (List α × ListM m α) :=
  L.getUpToFirstM fun a => pure (.up (p a))

/--
Extract a maximal prefix of a lazy list consisting of elements
satisfying a monadic predicate.
Return (in the monad) the prefix as a `List`, along with the remaining elements as a `ListM`.

(Note that the first element *not* satisfying the predicate will be generated,
and pushed back on to the remaining lazy list.)
-/
partial def splitWhileM (L : ListM m α) (p : α → m (ULift Bool)) :
    m (List α × ListM m α) := do
  match ← L.uncons with
  | none => return ([], nil)
  | some (x, xs) => (if (← p x).down then do
      let (acc, R) ← splitWhileM xs p
      return (x :: acc, R)
    else
      return ([], cons do pure (some x, xs)))

/--
Extract a maximal prefix of a lazy list consisting of elements
satisfying a predicate.
Return (in the monad) the prefix as a `List`, along with the remaining elements as a `ListM`.

(Note that the first element *not* satisfying the predicate will be generated,
and pushed back on to the remaining lazy list.)
-/
def splitWhile (L : ListM m α) (p : α → Bool) : m (List α × ListM m α) :=
  L.splitWhileM fun a => pure (.up (p a))

/--
Splits a lazy list into contiguous sublists of elements with the same value under
a monadic function.
Return a lazy lists of pairs, consisting of a value under that function,
and a maximal list of elements having that value.
-/
partial def groupByM [DecidableEq β] (L : ListM m α) (f : α → m β) : ListM m (β × List α) :=
  L.cases' nil fun a t => squash do
    let b ← f a
    let (l, t') ← t.splitWhileM (fun a => do return .up ((← f a) = b))
    return cons do pure (some (b, a :: l), t'.groupByM f)

/--
Splits a lazy list into contiguous sublists of elements with the same value under a function.
Return a lazy lists of pairs, consisting of a value under that function,
and a maximal list of elements having that value.
-/
def groupBy [DecidableEq β] (L : ListM m α) (f : α → β) : ListM m (β × List α) :=
  L.groupByM fun a => pure (f a)

-- local instance : DecidableEq (ULift Bool) := fun a b => by
--   cases' a with a; cases' b with b; cases a <;> cases b <;>

/--
Split a lazy list into contiguous sublists,
starting a new sublist each time a monadic predicate changes from `false` to `true`.
-/
partial def splitAtBecomesTrueM (L : ListM m α) (p : α → m (ULift Bool)) : ListM m (List α) :=
  aux (L.groupByM p)
where aux (M : ListM m (ULift.{u} Bool × List α)) : ListM m (List α) :=
  M.cases' nil fun (b, l) t => (if b.down then
    t.cases' (cons do pure (some l, nil)) fun (_, l') t' => cons do pure (some (l ++ l'), aux t')
  else
    cons do pure (some l, aux t))

/--
Split a lazy list into contiguous sublists,
starting a new sublist each time a predicate changes from `false` to `true`.
-/
def splitAtBecomesTrue (L : ListM m α) (p : α → Bool) : ListM m (List α) :=
  L.splitAtBecomesTrueM fun a => pure (.up (p a))
