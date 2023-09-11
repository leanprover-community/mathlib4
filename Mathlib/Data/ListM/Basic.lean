/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Keeley Hoek, Simon Hudon, Scott Morrison
-/
import Mathlib.Data.Option.Defs
import Mathlib.Control.Basic

#align_import data.mllist from "leanprover-community/mathlib"@"8f6fd1b69096c6a587f745d354306c0d46396915"

/-! # Monadic lazy lists.

Lazy lists with "laziness" controlled by an arbitrary monad.
-/

section UnsafeWrapper
variable (m : Type u → Type u)

private structure ListMApi where
  listM : Type u → Type u
  nil : listM α
  cons' : α → listM α → listM α
  squash : m (listM α) → listM α
  uncons : [Monad m] → listM α → m (Option (α × listM α))

instance : Nonempty (ListMApi m) := .intro {
  listM := fun _ => PUnit
  nil := ⟨⟩
  cons' := fun _ _ => ⟨⟩
  squash := fun _ => ⟨⟩
  uncons := fun _ => pure none
}

private unsafe inductive ListMImpl (α : Type u) : Type u
  | nil : ListMImpl α
  | cons' : α → ListMImpl α → ListMImpl α
  | squash : m (ListMImpl α) → ListMImpl α

private unsafe def unconsImpl [Monad m] :
    ListMImpl m α → m (Option (α × ListMImpl m α))
  | .nil => pure none
  | .squash t => t >>= unconsImpl
  | .cons' x xs => return (x, xs)

@[inline] private unsafe def listMApiImpl : ListMApi.{u} m where
  listM := ListMImpl m
  nil := .nil
  cons' := .cons'
  squash := .squash
  uncons := unconsImpl m

@[implemented_by listMApiImpl]
private opaque listMApi : ListMApi m
end UnsafeWrapper

/-- A monadic lazy list, controlled by an arbitrary monad. -/
def ListM (m : Type u → Type u) (α : Type u) : Type u := (listMApi m).listM α
#align tactic.mllist ListM

namespace ListM

variable {α β : Type u} {m : Type u → Type u}

/-- The empty `ListM`. -/
@[inline] def nil : ListM m α := (listMApi m).nil

/--
Constructs a `ListM` from head and tail.
-/
@[inline] def cons' : α → ListM m α → ListM m α := (listMApi m).cons'

/-- Lift a monadic lazy list inside the monad to a monadic lazy list. -/
def squash : m (ListM m α) → ListM m α := (listMApi m).squash
#align tactic.mllist.squash ListM.squash

/--
Constructs a `ListM` by providing a monadic value computing both the head and tail of the list.
The head is an `Option`, when `none` it is skipped and the list is only the tail.
-/
@[inline] -- inline because the compiler can usually optimize away the intermediate Option
def cons [Monad m] : m (Option α × ListM m α) → ListM m α :=
  fun x => squash do match ← x with
    | (none, xs) => pure xs
    | (some x, xs) => return cons' x xs

/-- Deconstruct a `ListM`, returning inside the monad an optional pair `α × ListM m α`
representing the head and tail of the list. -/
@[inline]
def uncons [Monad m] : ListM m α → m (Option (α × ListM m α)) := (listMApi m).uncons
#align tactic.mllist.uncons ListM.uncons

instance : EmptyCollection (ListM m α) := ⟨nil⟩
instance : Inhabited (ListM m α) := ⟨nil⟩

private local instance [Monad n] : Inhabited (δ → (α → δ → n (ForInStep δ)) → n δ) where
  default d _ := pure d in

/-- The implementation of `ForIn`, which enables `for a in L do ...` notation. -/
@[specialize] protected partial def forIn [Monad m] [Monad n] [MonadLiftT m n]
    (as : ListM m α) (init : δ) (f : α → δ → n (ForInStep δ)) : n δ := do
  match ← (as.uncons :) with
  | none => pure init
  | some (a, t) => match (← f a init) with
      | ForInStep.done d  => pure d
      | ForInStep.yield d => t.forIn d f

instance [Monad m] [MonadLiftT m n] : ForIn n (ListM m α) α where
  forIn := ListM.forIn

/-- Construct a `ListM` recursively. Failures from `f` will result in `uncons` failing.  -/
partial def fix [Monad m] (f : α → m α) (x : α) : ListM m α :=
  cons' x <| squash <| fix f <$> f x
#align tactic.mllist.fix ListM.fix

/-- Construct a `ListM` recursively. If `f` returns `none` the list will terminate. -/
partial def fix? [Monad m] (f : α → m (Option α)) (x : α) : ListM m α :=
  cons' x <| squash <| do
    match ← f x with
    | none => return .nil
    | some x' => return fix? f x'

variable [Monad m]

/-- Construct a `ListM` by iteration. (`m` must be a stateful monad for this to be useful.) -/
partial def iterate (f : m α) : ListM m α :=
  squash do return cons' (← f) (iterate f)

/-- Repeatedly apply a function `f : α → m (α × List β)` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list.

(This variant allows starting with a specified `List β` of elements, as well. )-/
partial def fixl_with (f : α → m (α × List β)) : α → List β → ListM m β
  | s, b :: rest => cons' b (fixl_with f s rest)
  | s, [] => cons <| do
    let (s', l) ← f s
    match l with
      | b :: rest => pure (some b, fixl_with f s' rest)
      | [] => pure (none, fixl_with f s' [])
#align tactic.mllist.fixl_with ListM.fixl_with

/-- Repeatedly apply a function `f : α → m (α × List β)` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list. -/
def fixl (f : α → m (α × List β)) (s : α) : ListM m β :=
  fixl_with f s []
#align tactic.mllist.fixl ListM.fixl

/-- Compute, inside the monad, whether a `ListM` is empty. -/
def isEmpty (xs : ListM m α) : m (ULift Bool) :=
  (ULift.up ∘ Option.isSome) <$> uncons xs
#align tactic.mllist.empty ListM.isEmpty

/-- Convert a `List` to a `ListM`. -/
def ofList : List α → ListM m α
  | [] => nil
  | h :: t => cons' h (ofList t)
#align tactic.mllist.of_list ListM.ofList

/-- The empty `ListM`. -/
abbrev empty : ListM m α := nil

/-- Convert a `List` of values inside the monad into a `ListM`. -/
def ofListM : List (m α) → ListM m α
  | [] => nil
  | h :: t => cons ((fun x => (x, ofListM t)) <$> some <$> h)
#align tactic.mllist.m_of_list ListM.ofListM

/-- Extract a list inside the monad from a `ListM`. -/
partial def force (L : ListM m α) : m (List α) := do
  match ← L.uncons with
  | none => pure []
  | some (x, xs) => return x :: (← xs.force)
#align tactic.mllist.force ListM.force

/-- Extract an array inside the monad from a `ListM`. -/
def asArray (L : ListM m α) : m (Array α) := do
  let mut r := #[]
  for a in L do
    r := r.push a
  return r

/--
Performs a case distinction on a `ListM` when the motive is a `ListM` as well.
(We need to be in a monadic context to distinguish a nil from a cons.)
-/
@[specialize]
def cases' (xs : ListM m α) (hnil : ListM m β) (hcons : α → ListM m α → ListM m β) : ListM m β :=
  squash do return match ← xs.uncons with
    | none => hnil
    | some (x, xs) => hcons x xs

/-- Gives the monadic lazy list consisting all of folds of a function on a given initial element.
Thus `[a₀, a₁, ...].foldsM f b` will give `[b, ← f b a₀, ← f (← f b a₀) a₁, ...]`. -/
partial def foldsM (f : β → α → m β) (init : β) (L : ListM m α) : ListM m β :=
  cons' init <| squash do match ← L.uncons with
    | none => return {}
    | some (x, xs) => return foldsM f (← f init x) xs

/-- Gives the monadic lazy list consisting all of folds of a function on a given initial element.
Thus `[a₀, a₁, ...].foldsM f b` will give `[b, f b a₀, f (f b a₀) a₁, ...]`. -/
def folds (f : β → α → β) (init : β) (L : ListM m α) : ListM m β :=
  L.foldsM (fun b a => pure (f b a)) init

/-- Take the first `n` elements, as a list inside the monad. -/
partial def takeAsList (xs : ListM m α) (n : Nat) : m (List α) :=
  go n [] xs
where
  go (r : Nat) (acc : List α) (xs : ListM m α) : m (List α) :=
    match r with
    | 0 => pure acc.reverse
    | r+1 => do match ← xs.uncons with
      | none => pure acc.reverse
      | some (x, xs) => go r (x :: acc) xs
#align tactic.mllist.take ListM.takeAsList

/-- Take the first `n` elements, as an array inside the monad. -/
partial def takeAsArray (xs : ListM m α) (n : Nat) : m (Array α) :=
  go n #[] xs
where
  go (r : Nat) (acc : Array α) (xs : ListM m α) : m (Array α) :=
    match r with
    | 0 => pure acc
    | r+1 => do match ← xs.uncons with
      | none => pure acc
      | some (x, xs) => go r (acc.push x) xs

/-- Take the first `n` elements. -/
partial def take (xs : ListM m α) : Nat → ListM m α
  | 0 => empty
  | n+1 => xs.cases' {} fun h l => cons do pure (h, l.take n)

/-- Drop the first `n` elements. -/
def drop (xs : ListM m α) : Nat → ListM m α
  | 0 => xs
  | n+1 => xs.cases' {} fun _ l => l.drop n

/-- Apply a function which returns values in the monad to every element of a `ListM`. -/
partial def mapM (f : α → m β) (xs : ListM m α) : ListM m β :=
  xs.cases' {} fun x xs => cons do return (← f x, xs.mapM f)
#align tactic.mllist.mmap ListM.mapM

/-- Apply a function to every element of a `ListM`. -/
def map (f : α → β) (L : ListM m α) : ListM m β :=
  L.mapM fun a => pure (f a)
#align tactic.mllist.map ListM.map

/-- Filter a `ListM` using a monadic function. -/
partial def filterM (p : α → m (ULift Bool)) (L : ListM m α) : ListM m α :=
  L.cases' {} fun x xs => cons do
    return (if (← p x).down then some x else none, filterM p xs)
#align tactic.mllist.mfilter ListM.filterM

/-- Filter a `ListM`. -/
def filter (p : α → Bool) (L : ListM m α) : ListM m α :=
  L.filterM fun a => pure <| .up (p a)
#align tactic.mllist.filter ListM.filter

/-- Filter and transform a `ListM` using a function that returns values inside the monad. -/
-- Note that the type signature has changed since Lean 3, when we allowed `f` to fail.
-- Use `try?` from `Mathlib.Control.Basic` to lift a possibly failing function to `Option`.
partial def filterMapM (f : α → m (Option β)) (xs : ListM m α) : ListM m β :=
  xs.cases' {} fun x xs => cons do return (← f x, xs.filterMapM f)
#align tactic.mllist.mfilter_map ListM.filterMapM

/-- Filter and transform a `ListM` using an `Option` valued function. -/
def filterMap (f : α → Option β) : ListM m α → ListM m β :=
  filterMapM fun a => do pure (f a)
#align tactic.mllist.filter_map ListM.filterMap

/-- Take the initial segment of the lazy list, until the function `f` first returns `false`. -/
partial def takeWhileM (f : α → m (ULift Bool)) (L : ListM m α) : ListM m α :=
  L.cases' {} fun x xs => cons do
    return if !(← f x).down then (none, {}) else (some x, xs.takeWhileM f)

/-- Take the initial segment of the lazy list, until the function `f` first returns `false`. -/
def takeWhile (f : α → Bool) : ListM m α → ListM m α :=
  takeWhileM fun a => pure (.up (f a))

/-- Concatenate two monadic lazy lists. -/
partial def append (xs ys : ListM m α) : ListM m α :=
  xs.cases' ys fun x xs => cons' x (append xs ys)
#align tactic.mllist.append ListM.append

/-- Join a monadic lazy list of monadic lazy lists into a single monadic lazy list. -/
partial def join (xs : ListM m (ListM m α)) : ListM m α :=
  xs.cases' {} fun x xs => append x (join xs)
#align tactic.mllist.join ListM.join

/-- Enumerate the elements of a monadic lazy list, starting at a specified offset. -/
partial def enum_from (n : Nat) (xs : ListM m α) : ListM m (Nat × α) :=
  xs.cases' {} fun x xs => cons' (n, x) (xs.enum_from (n+1))
#align tactic.mllist.enum_from ListM.enum_from

/-- Enumerate the elements of a monadic lazy list. -/
def enum : ListM m α → ListM m (Nat × α) :=
  enum_from 0
#align tactic.mllist.enum ListM.enum

/-- The infinite monadic lazy list of natural numbers.-/
def range {m : Type → Type} [Monad m] : ListM m Nat :=
  ListM.fix (fun n => pure (n + 1)) 0
#align tactic.mllist.range ListM.range

/-- Iterate through the elements of `Fin n`. -/
def fin {m : Type → Type} [Monad m] (n : Nat) : ListM m (Fin n) :=
  match n with
  | 0 => .nil
  | n+1 => fix? (fun i => if i < n then return some (i+1) else return none) 0

/-- Convert an array to a monadic lazy list. -/
def ofArray {m : Type → Type} [Monad m] {α : Type} (L : Array α) : ListM m α :=
  fin L.size |>.map L.get

/-- Group the elements of a lazy list into chunks of a given size.
If the lazy list is finite, the last chunk may be smaller (possibly even length 0). -/
partial def chunk (L : ListM m α) (n : Nat) : ListM m (Array α) :=
  go n #[] L
where
  go (r : Nat) (acc : Array α) (M : ListM m α) : ListM m (Array α) :=
    match r with
    | 0 => cons (pure (some acc, go n #[] M))
    | r+1 => squash do match ← M.uncons with
      | none => return cons (pure (some acc, .nil))
      | some (a, M') => return go r (acc.push a) M'

/-- Add one element to the end of a monadic lazy list. -/
def concat : ListM m α → α → ListM m α
  | L, a => (ListM.ofList [L, ListM.ofList [a]]).join
#align tactic.mllist.concat ListM.concat

/-- Take the product of two monadic lazy lists. -/
partial def zip (L : ListM m α) (M : ListM m β) : ListM m (α × β) :=
  L.cases' {} fun a L =>
  M.cases' {} fun b M =>
  cons' (a, b) (L.zip M)

/-- Apply a function returning a monadic lazy list to each element of a monadic lazy list,
joining the results. -/
partial def bind (xs : ListM m α) (f : α → ListM m β) : ListM m β :=
  xs.cases' {} fun x xs => append (f x) (bind xs f)
#align tactic.mllist.bind_ ListM.bind

/-- Convert any value in the monad to the singleton monadic lazy list. -/
def monadLift (x : m α) : ListM m α :=
  cons <| (flip Prod.mk nil ∘ some) <$> x
#align tactic.mllist.monad_lift ListM.monadLift

/-- Lift the monad of a lazy list. -/
partial def liftM [Monad n] [MonadLiftT m n] (L : ListM m α) : ListM n α :=
  squash do return match ← (uncons L : m _) with
    | none => {}
    | some (a, L') => cons' a L'.liftM

/-- Given a lazy list in a state monad, run it on some initial state, recording the states. -/
partial def runState (L : ListM (StateT.{u} σ m) α) (s : σ) : ListM m (α × σ) :=
  squash do return match ← (uncons L).run s with
    | (none, _) => {}
    | (some (a, L'), s') => cons' (a, s') (L'.runState s')

/-- Given a lazy list in a state monad, run it on some initial state. -/
def runState' (L : ListM (StateT.{u} σ m) α) (s : σ) : ListM m α :=
  L.runState s |>.map (·.1)

/-- Return the head of a monadic lazy list if it exists, as an `Option` in the monad. -/
def head? (L : ListM m α) : m (Option α) := do
  pure <| (← L.uncons).map (·.1)

/-- Take the initial segment of the lazy list,
up to and including the first place where `f` gives `true`. -/
partial def takeUpToFirstM (L : ListM m α) (f : α → m (ULift Bool)) : ListM m α :=
  L.cases' {} fun x xs => cons do
    return (some x, if (← (f x)).down then empty else xs.takeUpToFirstM f)

/-- Take the initial segment of the lazy list,
up to and including the first place where `f` gives `true`. -/
def takeUpToFirst (L : ListM m α) (f : α → Bool) : ListM m α :=
  L.takeUpToFirstM fun a => pure (.up (f a))

/-- Gets the last element of a monadic lazy list, as an option in the monad.
This will run forever if the list is infinite. -/
partial def getLast? (L : ListM m α) : m (Option α) := do
  match ← uncons L with
  | none => return none
  | some (x, xs) => aux x xs
where aux (x : α) (L : ListM m α) : m (Option α) := do
  match ← uncons L with
  | none => return (some x)
  | some (y, ys) => aux y ys

/-- Gets the last element of a monadic lazy list, or the default value if the list is empty.
This will run forever if the list is infinite. -/
partial def getLast! [Inhabited α] (L : ListM m α) : m α :=
  Option.get! <$> L.getLast?

/-- Folds a binary function across a monadic lazy list, from an initial starting value.
This will run forever if the list is infinite. -/
partial def foldM (f : β → α → m β) (init : β) (L : ListM m α) : m β :=
  (L.foldsM f init |>.getLast?) <&> (·.getD init) -- `foldsM` is always non-empty, anyway.

/-- Folds a binary function across a monadic lazy list, from an initial starting value.
This will run forever if the list is infinite. -/
unsafe def fold (f : β → α → β) (init : β) (L : ListM m α) : m β :=
  L.foldM (fun b a => pure (f b a)) init

section Alternative
variable [Alternative m]

/--
Return the head of a monadic lazy list, as a value in the monad.
Fails if the list is empty.
-/
def head (L : ListM m α) : m α := do
  let some (r, _) ← L.uncons | failure
  return r
#align tactic.mllist.head ListM.head

/--
Apply a function returning values inside the monad to a monadic lazy list,
returning only the first successful result.
-/
def firstM (L : ListM m α) (f : α → m (Option β)) : m β :=
  (L.filterMapM f).head
#align tactic.mllist.mfirst ListM.firstM

/-- Return the first value on which a predicate returns true. -/
def first (L : ListM m α) (p : α → Bool) : m α :=
  (L.filter p).head

end Alternative

instance : Monad (ListM m) where
  pure := fun a => .ofList [a]
  seq := fun fs as => fs.zip (as ()) |>.map fun ⟨f, a⟩ => f a
  bind := bind

instance : Alternative (ListM m) where
  failure := nil
  orElse := fun L M => L.append (M ())

instance : MonadLift m (ListM m) where
  monadLift := monadLift
