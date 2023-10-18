/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.PFunctor.Univariate.M

#align_import data.stream.defs from "leanprover-community/mathlib"@"39af7d3bf61a98e928812dbc3e16f4ea8b795ca3"

/-!
# Definition of `Stream'` and functions on streams

A stream `Stream' α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `Stream'` and some functions that take and/or return streams.
Note that we already have `Stream` to represent a similar object, hence the awkward naming.
-/

set_option autoImplicit true

open PFunctor

/-- A polynomial functor which is used to declare `Stream' α`. -/
def Stream'.shape (α : Type u) : PFunctor.{u} where
  A := α
  B := fun _ => PUnit

/-- A stream `Stream' α` is an infinite sequence of elements of `α`. -/
def Stream' (α : Type u) := M (Stream'.shape α)
#align stream Stream'

namespace Stream'

/-- Prepend an element to a stream. -/
@[inline]
def cons (a : α) (s : Stream' α) : Stream' α :=
  M.mk ⟨a, fun _ => s⟩
#align stream.cons Stream'.cons

@[inherit_doc]
infixr:67 " ::ₛ " => cons

/-- Head of a stream: `Stream'.head (h ::ₛ t) = h`. -/
@[inline]
def head (s : Stream' α) : α := M.dest s |>.1
#align stream.head Stream'.head

/-- Tail of a stream: `Stream'.tail (h ::ₛ t) = t`. -/
@[inline]
def tail (s : Stream' α) : Stream' α := M.dest s |>.2 ⟨⟩
#align stream.tail Stream'.tail

/-- Get the `n`-th element of a stream. -/
def get (s : Stream' α) : ℕ → α
  | 0     => head s
  | n + 1 => get (tail s) n
#align stream.nth Stream'.get

/-- Drop first `n` elements of a stream. -/
def drop : ℕ → Stream' α → Stream' α
  | 0    , s => s
  | n + 1, s => drop n (tail s)
#align stream.drop Stream'.drop

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def All (p : α → Prop) (s : Stream' α) : Prop :=
  ∃ q : Stream' α → Prop, q s ∧ ∀ s', q s' → p (head s') ∧ q (tail s')
#align stream.all Stream'.All

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
inductive Any (p : α → Prop) : Stream' α → Prop
  | head (s) : p (head s) → Any p s
  | tail (s) : Any p (tail s) → Any p s
#align stream.any Stream'.Any

/-- `a ∈ s` means that `a` is the element of `s`. -/
instance : Membership α (Stream' α) :=
  ⟨fun a s => Any (Eq a) s⟩

theorem mem_def {a : α} {s : Stream' α} : a ∈ s ↔ Any (Eq a) s :=
  Iff.rfl

@[inline]
def corec' (f : α → β × α) : α → Stream' β :=
  M.corec ((fun (b, a) => ⟨b, fun _ => a⟩) ∘ f)
#align stream.corec' Stream'.corec'

@[inline]
def corec (f : α → β) (g : α → α) : α → Stream' β :=
  corec' (fun a => (f a, g a))
#align stream.corec Stream'.corec

abbrev corecOn (a : α) (f : α → β) (g : α → α) : Stream' β :=
  corec f g a
#align stream.corec_on Stream'.corecOn

/-- Apply a function `f` to all elements of a stream `s`. -/
@[inline]
def map (f : α → β) : Stream' α → Stream' β :=
  corec (f ∘ head) tail
#align stream.map Stream'.map

/-- Zip two streams using a binary operation:
- `Stream'.head (Stream'.zipWith f s₁ s₂) = f (Stream'.head s₁) (Stream'.head s₂)`
- `Stream'.tail (Stream'.zipWith f s₁ s₂) =
   Stream'.zipWith f (Stream'.tail s₁) (Stream'.tail s₂)` -/
@[inline]
def zipWith (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ :=
  corec (fun (s₁, s₂) => f (head s₁) (head s₂)) (fun (s₁, s₂) => (tail s₁, tail s₂)) (s₁, s₂)
#align stream.zip Stream'.zipWith

/-- Zip two streams:
- `Stream'.head (Stream'.zip s₁ s₂) = (Stream'.head s₁, Stream'.head s₂)`
- `Stream'.tail (Stream'.zip s₁ s₂) = Stream'.zip (Stream'.tail s₁) (Stream'.tail s₂)` -/
def zip : Stream' α → Stream' β → Stream' (α × β) :=
  zipWith Prod.mk

/-- Iterates of a function as a stream. -/
@[inline]
def iterate (f : α → α) : α → Stream' α :=
  corec id f
#align stream.iterate Stream'.iterate

/-- The stream of natural numbers from `n` :
- `Stream'.head (Stream'.natsFrom n) = n`
- `Stream'.tail (Stream'.natsFrom n) = Stream'.natsFrom (n + 1)` -/
def natsFrom : ℕ → Stream' ℕ :=
  iterate Nat.succ

/-- The stream of natural numbers. -/
abbrev nats : Stream' Nat :=
  natsFrom 0
#align stream.nats Stream'.nats

/-- Construct a stream from a function of `ℕ → α`. -/
@[inline]
def ofFn (f : ℕ → α) : Stream' α :=
  map f nats

/-- Enumerate a stream by tagging each element with its index. -/
def enum (s : Stream' α) : Stream' (ℕ × α) :=
  zip nats s
#align stream.enum Stream'.enum

/-- The constant stream:
- `Stream'.head (Stream'.const a) = a`
- `Stream'.tail (Stream'.const a) = Stream'.const a` -/
def const (a : α) : Stream' α :=
  corec (fun _ : Unit => a) id ()
#align stream.const Stream'.const

-- porting note: this `#align` should be elsewhere but idk where
#align state StateM

/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)
#align stream.corec_state Stream'.corecState

#align stream.unfolds Stream'.corec

/-- Interleave two streams. -/
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corec (fun (s₁, _) => head s₁) (fun (s₁, s₂) => (s₂, tail s₁)) (s₁, s₂)
#align stream.interleave Stream'.interleave

infixl:65 " ⋈ " => interleave

/-- Elements of a stream with even indices. -/
def even : Stream' α → Stream' α :=
  corec head (tail ∘ tail)
#align stream.even Stream'.even

/-- Elements of a stream with odd indices. -/
def odd (s : Stream' α) : Stream' α :=
  even (tail s)
#align stream.odd Stream'.odd

/-- Append a stream to a list. -/
def hAppend : List α → Stream' α → Stream' α
  | [], s => s
  | a :: l, s => a ::ₛ hAppend l s
#align stream.append_stream Stream'.hAppend

instance : HAppend (List α) (Stream' α) (Stream' α) where
  hAppend := hAppend

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Stream' α → List α
  | 0, _ => []
  | n + 1, s => head s :: take n (tail s)
#align stream.take Stream'.take

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v
#align stream.cycle_f Stream'.cycleF

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (_, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, v₂ :: l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)
#align stream.cycle_g Stream'.cycleG

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : ∀ l : List α, l ≠ [] → Stream' α
  | [], h => absurd rfl h
  | a :: l, _ => corec Stream'.cycleF Stream'.cycleG (a, l, a, l)
#align stream.cycle Stream'.cycle

/-- Tails of a stream, starting with `s`. -/
def tails : Stream' α → Stream' (Stream' α) :=
  iterate tail
#align stream.tails Stream'.tails

/-- An auxiliary definition for `Stream'.inits`. -/
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corec (fun (a, _) => a)
    (fun (l', s') => (List.concat l' (head s'), tail s'))
    (l, s)
#align stream.inits_core Stream'.initsCore

/-- Initial segments of a stream. -/
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [] s
#align stream.inits Stream'.inits

#align stream.pure Stream'.const

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply : Stream' (α → β) → Stream' α → Stream' β :=
  zipWith id
#align stream.apply Stream'.apply

@[inherit_doc]
infixl:75 " ⊛ " => apply
-- PORTING NOTE: "input as \o*" was here but doesn't work for the above notation

end Stream'
