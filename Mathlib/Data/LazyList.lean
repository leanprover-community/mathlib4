/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename

#align_import data.lazy_list from "leanprover-community/mathlib"@"41cf0cc2f528dd40a8f2db167ea4fb37b8fde7f3"
/-!
# Lazy lists

The type `LazyList α` is a lazy list with elements of type `α`.
In the VM, these are potentially infinite lists
where all elements after the first are computed on-demand.
(This is only useful for execution in the VM,
logically we can prove that `LazyList α` is isomorphic to `List α`.)
-/


universe u v w


/-- Lazy list.
All elements (except the first) are computed lazily.
-/
inductive LazyList (α : Type u) : Type u
  | nil : LazyList α
  | cons (hd : α) (tl : Thunk <| LazyList α) : LazyList α

namespace LazyList

variable {α : Type u} {β : Type v} {δ : Type w}

instance : Inhabited (LazyList α) :=
  ⟨nil⟩

/-- The singleton lazy list.  -/
def singleton : α → LazyList α
  | a => cons a <| Thunk.pure nil

/-- Constructs a lazy list from a list. -/
def ofList : List α → LazyList α
  | [] => nil
  | h :: t => cons h (ofList t)

/-- Converts a lazy list to a list.
If the lazy list is infinite,
then this function does not terminate.
-/
def toList : LazyList α → List α
  | nil => []
  | cons h t => h :: toList (t.get)

/-- Returns the first element of the lazy list,
or `default` if the lazy list is empty.
-/
def headI [Inhabited α] : LazyList α → α
  | nil => default
  | cons h _ => h

/-- Removes the first element of the lazy list.
-/
def tail : LazyList α → LazyList α
  | nil => nil
  | cons _ t => t.get

/-- Appends two lazy lists.  -/
def append : LazyList α → Thunk (LazyList α) → LazyList α
  | nil, l => l.get
  | cons h t, l => cons h (@append (t.get) l)

/-- Maps a function over a lazy list. -/
def map (f : α → β) : LazyList α → LazyList β
  | nil => nil
  | cons h t => cons (f h) (map f t.get)

/-- Maps a binary function over two lazy list.
Like `LazyList.zip`, the result is only as long as the smaller input.
-/
def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
  | nil, _ => nil
  | _, nil => nil
  | cons h₁ t₁, cons h₂ t₂ => cons (f h₁ h₂) (map₂ f t₁.get t₂.get)

/-- Zips two lazy lists. -/
def zip : LazyList α → LazyList β → LazyList (α × β) :=
  map₂ Prod.mk

/-- The monadic join operation for lazy lists. -/
def join : LazyList (LazyList α) → LazyList α
  | nil => nil
  | cons h t => append h (join (t.get))

/-- Maps a function over a lazy list.
Same as `LazyList.map`, but with swapped arguments.
-/
def «for» (l : LazyList α) (f : α → β) : LazyList β :=
  map f l

/-- The list containing the first `n` elements of a lazy list.  -/
def approx : Nat → LazyList α → List α
  | 0, _ => []
  | _, nil => []
  | a + 1, cons h t => h :: approx a (t.get)

/-- The lazy list of all elements satisfying the predicate.
If the lazy list is infinite and none of the elements satisfy the predicate,
then this function will not terminate.
-/
def filter (p : α → Prop) [DecidablePred p] : LazyList α → LazyList α
  | nil => nil
  | cons h t => if p h then cons h (filter p t.get) else filter p (t.get)

/-- The nth element of a lazy list as an option (like `List.get?`). -/
def nth : LazyList α → Nat → Option α
  | nil, _ => none
  | cons a _, 0 => some a
  | cons _ l, n + 1 => nth (l.get) n

/-- The infinite lazy list `[x, f x, f (f x), ...]` of iterates of a function.
This definition is meta because it creates an infinite list.
-/
unsafe def iterates (f : α → α) : α → LazyList α
  | x => cons x (iterates f (f x))

/-- The infinite lazy list `[i, i+1, i+2, ...]` -/
unsafe def iota (i : Nat) : LazyList Nat :=
  iterates Nat.succ i

end LazyList
