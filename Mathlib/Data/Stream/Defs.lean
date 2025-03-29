/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.Nat.Notation

/-!
# Definition of `Stream'` and functions on streams

A stream `Stream' α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `Stream'` and some functions that take and/or return streams.
Note that we already have `Stream` to represent a similar object, hence the awkward naming.
-/

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}

/-- A stream `Stream' α` is an infinite sequence of elements of `α`. -/
def Stream' (α : Type u) := ℕ → α

namespace Stream'

/-- Prepend an element to a stream. -/
def cons (a : α) (s : Stream' α) : Stream' α
  | 0 => a
  | n + 1 => s n

@[inherit_doc] scoped infixr:67 " :: " => cons

/-- Get the `n`-th element of a stream. -/
def get (s : Stream' α) (n : ℕ) : α := s n

/-- Head of a stream: `Stream'.head s = Stream'.get s 0`. -/
abbrev head (s : Stream' α) : α := s.get 0

/-- Tail of a stream: `Stream'.tail (h :: t) = t`. -/
def tail (s : Stream' α) : Stream' α := fun i => s.get (i + 1)

/-- Drop first `n` elements of a stream. -/
def drop (n : ℕ) (s : Stream' α) : Stream' α := fun i => s.get (i + n)

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def All (p : α → Prop) (s : Stream' α) := ∀ n, p (get s n)

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def Any (p : α → Prop) (s : Stream' α) := ∃ n, p (get s n)

/-- `a ∈ s` means that `a = Stream'.get n s` for some `n`. -/
instance : Membership α (Stream' α) :=
  ⟨fun s a => Any (fun b => a = b) s⟩

/-- Apply a function `f` to all elements of a stream `s`. -/
def map (f : α → β) (s : Stream' α) : Stream' β := fun n => f (get s n)

/-- Zip two streams using a binary operation:
`Stream'.get n (Stream'.zip f s₁ s₂) = f (Stream'.get s₁) (Stream'.get s₂)`. -/
def zip (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ :=
  fun n => f (get s₁ n) (get s₂ n)

/-- Enumerate a stream by tagging each element with its index. -/
def enum (s : Stream' α) : Stream' (ℕ × α) := fun n => (n, s.get n)

/-- The constant stream: `Stream'.get n (Stream'.const a) = a`. -/
def const (a : α) : Stream' α := fun _ => a

/-- Iterates of a function as a stream. -/
def iterate (f : α → α) (a : α) : Stream' α
  | 0 => a
  | n + 1 => f (iterate f a n)

def corec (f : α → β) (g : α → α) : α → Stream' β := fun a => map f (iterate g a)

def corecOn (a : α) (f : α → β) (g : α → α) : Stream' β :=
  corec f g a

def corec' (f : α → β × α) : α → Stream' β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)

/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

-- corec is also known as unfolds
abbrev unfolds (g : α → β) (f : α → α) (a : α) : Stream' β :=
  corec g f a

/-- Interleave two streams. -/
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corecOn (s₁, s₂) (fun ⟨s₁, _⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

@[inherit_doc] infixl:65 " ⋈ " => interleave

/-- Elements of a stream with even indices. -/
def even (s : Stream' α) : Stream' α :=
  corec head (fun s => tail (tail s)) s

/-- Elements of a stream with odd indices. -/
def odd (s : Stream' α) : Stream' α :=
  even (tail s)

/-- Append a stream to a list. -/
def appendStream' : List α → Stream' α → Stream' α
  | [], s => s
  | List.cons a l, s => a::appendStream' l s

@[inherit_doc] infixl:65 " ++ₛ " => appendStream'

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Stream' α → List α
  | 0, _ => []
  | n + 1, s => List.cons (head s) (take n (tail s))

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (_, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : ∀ l : List α, l ≠ [] → Stream' α
  | [], h => absurd rfl h
  | List.cons a l, _ => corec Stream'.cycleF Stream'.cycleG (a, l, a, l)

/-- Tails of a stream, starting with `Stream'.tail s`. -/
def tails (s : Stream' α) : Stream' (Stream' α) :=
  corec id tail (tail s)

/-- An auxiliary definition for `Stream'.inits`. -/
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corecOn (l, s) (fun ⟨a, _⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')

/-- Nonempty initial segments of a stream. -/
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [head s] (tail s)

/-- A constant stream, same as `Stream'.const`. -/
def pure (a : α) : Stream' α :=
  const a

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : Stream' (α → β)) (s : Stream' α) : Stream' β := fun n => (get f n) (get s n)

@[inherit_doc] infixl:75 " ⊛ " => apply -- input as `\circledast`

/-- The stream of natural numbers: `Stream'.get n Stream'.nats = n`. -/
def nats : Stream' ℕ := fun n => n

end Stream'
