/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Data.Nat.Basic
/-!
# Definition of `Stream'` and functions on streams

A stream `Stream' α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `Stream'` and some functions that take and/or return streams.
Note that we already have `Stream` to represent a similar object, hence the awkward naming.

-/

universe u v w
/-- A stream `Stream' α` is an infinite sequence of elements of `α`. -/
def Stream' (α : Type u) := ℕ → α
#align stream Stream'

open Nat

namespace Stream'

variable {α : Type u} {β : Type v} {δ : Type w}

/-- Prepend an element to a stream. -/
def cons (a : α) (s : Stream' α) : Stream' α
  | 0 => a
  | n + 1 => s n
#align stream.cons Stream'.cons

scoped infixr:67 " :: " => cons

/-- Head of a stream: `Stream'.head s = Stream'.nth s 0`. -/
def head (s : Stream' α) : α := s 0
#align stream.head Stream'.head

/-- Tail of a stream: `Stream'.tail (h :: t) = t`. -/
def tail (s : Stream' α) : Stream' α := fun i => s (i + 1)
#align stream.tail Stream'.tail

/-- Drop first `n` elements of a stream. -/
def drop (n : Nat) (s : Stream' α) : Stream' α := fun i => s (i + n)
#align stream.drop Stream'.drop

/-- `n`-th element of a stream. -/
def nth (s : Stream' α) (n : ℕ) : α := s n
#align stream.nth Stream'.nth

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def All (p : α → Prop) (s : Stream' α) := ∀ n, p (nth s n)
#align stream.all Stream'.All

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def Any (p : α → Prop) (s : Stream' α) := ∃ n, p (nth s n)
#align stream.any Stream'.Any

/-- `a ∈ s` means that `a = Stream'.nth n s` for some `n`. -/
instance : Membership α (Stream' α) :=
  ⟨fun a s => Any (fun b => a = b) s⟩

/-- Apply a function `f` to all elements of a stream `s`. -/
def map (f : α → β) (s : Stream' α) : Stream' β := fun n => f (nth s n)
#align stream.map Stream'.map

/-- Zip two streams using a binary operation:
`Stream'.nth n (Stream'.zip f s₁ s₂) = f (Stream'.nth s₁) (Stream'.nth s₂)`. -/
def zip (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ :=
  fun n => f (nth s₁ n) (nth s₂ n)
#align stream.zip Stream'.zip

/-- Enumerate a stream by tagging each element with its index. -/
def enum (s : Stream' α) : Stream' (ℕ × α) := fun n => (n, s.nth n)
#align stream.enum Stream'.enum

/-- The constant stream: `Stream'.nth n (Stream'.const a) = a`. -/
def const (a : α) : Stream' α := fun _ => a
#align stream.const Stream'.const

-- porting note: used to be implemented using RecOn
/-- Iterates of a function as a stream. -/
def iterate (f : α → α) (a : α) : Stream' α
  | 0 => a
  | n + 1 => f (iterate f a n)
#align stream.iterate Stream'.iterate

def corec (f : α → β) (g : α → α) : α → Stream' β := fun a => map f (iterate g a)
#align stream.corec Stream'.corec

def corecOn (a : α) (f : α → β) (g : α → α) : Stream' β :=
  corec f g a
#align stream.corec_on Stream'.corecOn

def corec' (f : α → β × α) : α → Stream' β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)
#align stream.corec' Stream'.corec'

-- porting note: this `#align` should be elsewhere but idk where
#align state StateM

/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)
#align stream.corec_state Stream'.corecState

-- corec is also known as unfold
def unfolds (g : α → β) (f : α → α) (a : α) : Stream' β :=
  corec g f a
#align stream.unfolds Stream'.unfolds

/-- Interleave two streams. -/
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corecOn (s₁, s₂) (fun ⟨s₁, _⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)
#align stream.interleave Stream'.interleave

infixl:65 " ⋈ " => interleave

/-- Elements of a stream with even indices. -/
def even (s : Stream' α) : Stream' α :=
  corec (fun s => head s) (fun s => tail (tail s)) s
#align stream.even Stream'.even

/-- Elements of a stream with odd indices. -/
def odd (s : Stream' α) : Stream' α :=
  even (tail s)
#align stream.odd Stream'.odd

/-- Append a stream to a list. -/
def appendStream' : List α → Stream' α → Stream' α
  | [], s => s
  | List.cons a l, s => a::appendStream' l s
#align stream.append_stream Stream'.appendStream'

infixl:65 " ++ₛ " => appendStream'

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Stream' α → List α
  | 0, _ => []
  | n + 1, s => List.cons (head s) (take n (tail s))
#align stream.take Stream'.take

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v
#align stream.cycle_f Stream'.cycleF

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (_, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)
#align stream.cycle_g Stream'.cycleG

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : ∀ l : List α, l ≠ [] → Stream' α
  | [], h => absurd rfl h
  | List.cons a l, _ => corec Stream'.cycleF Stream'.cycleG (a, l, a, l)
#align stream.cycle Stream'.cycle

/-- Tails of a stream, starting with `Stream'.tail s`. -/
def tails (s : Stream' α) : Stream' (Stream' α) :=
  corec id tail (tail s)
#align stream.tails Stream'.tails

/-- An auxiliary definition for `Stream'.inits`. -/
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corecOn (l, s) (fun ⟨a, _⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')
#align stream.inits_core Stream'.initsCore

/-- Nonempty initial segments of a stream. -/
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [head s] (tail s)
#align stream.inits Stream'.inits

/-- A constant stream, same as `Stream'.const`. -/
def pure (a : α) : Stream' α :=
  const a
#align stream.pure Stream'.pure

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : Stream' (α → β)) (s : Stream' α) : Stream' β := fun n => (nth f n) (nth s n)
#align stream.apply Stream'.apply

infixl:75 " ⊛ " => apply
-- PORTING NOTE: "input as \o*" was here but doesn't work for the above notation

/-- The stream of natural numbers: `Stream'.nth n Stream'.nats = n`. -/
def nats : Stream' Nat := fun n => n
#align stream.nats Stream'.nats

end Stream'
