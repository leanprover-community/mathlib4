/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.BigOperators.Multiset.Basic

/-!

This file makes infoview display:
* `List.take n l` as `l.take n`
* `List.drop n l` as `l.drop n`
* `List.takeWhile p l` as `l.takeWhile p`
* `List.dropWhile p l` as `l.dropWhile n`
* `List.map f l` as `l.map f`
* `Multiset.map f s` as `s.map f`

-/

/-- Given `n : ℕ` and `l : List α`, print `List.take n l` as `l.take n` in Infoview. -/
@[app_unexpander List.take]
def List.take.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `take) $n)
  | _ => throw ()

/-- Given `n : ℕ` and `l : List α`, print `List.drop n l` as `l.drop n` in Infoview. -/
@[app_unexpander List.drop]
def List.drop.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `drop) $n)
  | _ => throw ()

/-- Given `p : α → Bool` and `l : List α`, print `List.takeWhile p l` as `l.takeWhile p` in
Infoview. -/
@[app_unexpander List.takeWhile]
def List.takeWhile.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $p $l) => `($(l).$(Lean.mkIdent `takeWhile) $p)
  | _ => throw ()

/-- Given `p : α → Bool` and `l : List α`, print `List.dropWhile p l` as `l.dropWhile p` in
Infoview. -/
@[app_unexpander List.dropWhile]
def List.dropWhile.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $p $l) => `($(l).$(Lean.mkIdent `dropWhile) $p)
  | _ => throw ()

/-- Given `f : α → β` and `l : List α`, print `List.map f l` as `l.map f` in Infoview. -/
@[app_unexpander List.map]
def List.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `map) $f)
  | _ => throw ()

/-- Given `f : α → β` and `s : Multiset α`, print `Multiset.map f s` as `s.map f` in Infoview. -/
@[app_unexpander Multiset.map]
def Multiset.map.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $s) => `($(s).$(Lean.mkIdent `map) $f)
  | _ => throw ()

-- Do we also want these?
-- attribute [pp_dot] List.get List.length List.sum Multiset.sum Sigma.fst Sigma.snd

example (l : List ℕ) : l.take l.length = l.takeWhile (fun _ => true) := by
  rw [List.take_length]
  induction l <;> congr

example (l : List ℕ) : l.drop 0 = l.dropWhile (fun _ => false) := by
  cases l <;> rfl

example (l : List ℕ) : (Multiset.ofList l).map Nat.succ = Multiset.ofList (l.map Nat.succ) := by
  simp
