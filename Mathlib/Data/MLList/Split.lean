/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.MLList.Basic
import Mathlib.Data.ULift

/-!
# Functions for splitting monadic lazy lists.

## Deprecation

This material has been moved out of Mathlib to https://github.com/semorrison/lean-monadic-list.
-/

set_option linter.deprecated false

namespace MLList

universe u
variable {α β : Type u} {m : Type u → Type u} [Monad m]

/--
Extract the prefix of a lazy list consisting of elements up to and including
the first element satisfying a monadic predicate.
Return (in the monad) the prefix as a `List`, along with the remaining elements as a `MLList`.
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def getUpToFirstM (L : MLList m α) (p : α → m (ULift Bool)) : m (List α × MLList m α) := do
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
Return (in the monad) the prefix as a `List`, along with the remaining elements as a `MLList`.
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def getUpToFirst (L : MLList m α) (p : α → Bool) : m (List α × MLList m α) :=
  L.getUpToFirstM fun a => pure (.up (p a))

/--
Extract a maximal prefix of a lazy list consisting of elements
satisfying a monadic predicate.
Return (in the monad) the prefix as a `List`, along with the remaining elements as a `MLList`.

(Note that the first element *not* satisfying the predicate will be generated,
and pushed back on to the remaining lazy list.)
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def splitWhileM (L : MLList m α) (p : α → m (ULift Bool)) :
    m (List α × MLList m α) := do
  match ← L.uncons with
  | none => return ([], nil)
  | some (x, xs) => (if (← p x).down then do
      let (acc, R) ← splitWhileM xs p
      return (x :: acc, R)
    else
      return ([], cons x xs))

/--
Extract a maximal prefix of a lazy list consisting of elements
satisfying a predicate.
Return (in the monad) the prefix as a `List`, along with the remaining elements as a `MLList`.

(Note that the first element *not* satisfying the predicate will be generated,
and pushed back on to the remaining lazy list.)
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def splitWhile (L : MLList m α) (p : α → Bool) : m (List α × MLList m α) :=
  L.splitWhileM fun a => pure (.up (p a))

/--
Splits a lazy list into contiguous sublists of elements with the same value under
a monadic function.
Return a lazy lists of pairs, consisting of a value under that function,
and a maximal list of elements having that value.
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def groupByM [DecidableEq β] (L : MLList m α) (f : α → m β) : MLList m (β × List α) :=
  L.cases (fun _ => nil) fun a t => squash fun _ => do
    let b ← f a
    let (l, t') ← t.splitWhileM (fun a => do return .up ((← f a) = b))
    return cons (b, a :: l) (t'.groupByM f)

/--
Splits a lazy list into contiguous sublists of elements with the same value under a function.
Return a lazy lists of pairs, consisting of a value under that function,
and a maximal list of elements having that value.
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def groupBy [DecidableEq β] (L : MLList m α) (f : α → β) : MLList m (β × List α) :=
  L.groupByM fun a => pure (f a)

-- local instance : DecidableEq (ULift Bool) := fun a b => by
--   cases' a with a; cases' b with b; cases a <;> cases b <;>

/--
Split a lazy list into contiguous sublists,
starting a new sublist each time a monadic predicate changes from `false` to `true`.
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def splitAtBecomesTrueM (L : MLList m α) (p : α → m (ULift Bool)) : MLList m (List α) :=
  aux (L.groupByM p)
where aux (M : MLList m (ULift.{u} Bool × List α)) : MLList m (List α) :=
  M.cases (fun _ => nil) fun (b, l) t => (if b.down then
    t.cases (fun _ => cons l nil)
      fun (_, l') t' => cons (l ++ l') (aux t')
  else
    cons l (aux t))

/--
Split a lazy list into contiguous sublists,
starting a new sublist each time a predicate changes from `false` to `true`.
-/
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def splitAtBecomesTrue (L : MLList m α) (p : α → Bool) : MLList m (List α) :=
  L.splitAtBecomesTrueM fun a => pure (.up (p a))

end MLList
