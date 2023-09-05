/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Data.Nat.Basic

#align_import data.stream.defs from "leanprover-community/mathlib"@"39af7d3bf61a98e928812dbc3e16f4ea8b795ca3"

/-!
# Definition of `Stream'` and functions on streams

A stream `Stream' α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `Stream'` and some functions that take and/or return streams.
Note that we already have `Stream` to represent a similar object, hence the awkward naming.

## Main definitions

Given a type `α` and a function `f : ℕ → α`:

* `Stream' α` : the type of streams whose elements have type `α`
* `strmOf f : Stream' α` : the stream whose `n`-th element is `f n`.
* `ₛ[ f n | n ] : Stream' α` :
  the stream whose `n`-th element is `f n`, this is an notation of `strmOf fun n => f n`.
-/

set_option autoImplicit true

/-- A stream `Stream' α` is an infinite sequence of elements of `α`. -/
def Stream' (α : Type u) := ℕ → α
#align stream Stream'

/-- `strmOf f` is the stream whose `n`-th element is `f n` -/
@[always_inline, inline]
def strmOf (f : ℕ → α) : Stream' α := f

open Lean Macro in
/--
`ₛ[ f n | n ]` is the stream whose `n`-th element is `f n`,
this is an notation of `strmOf fun n => f n`. -/
macro "ₛ[ " t:term " | " b:binderIdent  " ]" : term =>
  match b with
  | `(binderIdent| $i:ident) => `(strmOf fun $i => $t)
  | `(binderIdent| _)        => `(strmOf fun _ => $t)
  | _                        => throwUnsupported

/-- Unexpand `fun` expressions to stream expressions. -/
@[app_unexpander strmOf] def unexpandStrmOf : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b)                     => `(ₛ[ $b | $x:ident ])
  | `($(_) fun ($x:ident : $_) => $b)              => `(ₛ[ $b | $x:ident ])
  | _                                              => throw ()

namespace Stream'

/-- Get the `n`-th element of a stream. -/
@[always_inline, inline]
def get (s : Stream' α) (n : ℕ) : α := s n
#align stream.nth Stream'.get

instance : GetElem (Stream' α) ℕ α (fun _ _ => True) where
  getElem s n _ := get s n

@[simp]
theorem getElem_eq_get (s : Stream' α) (n : ℕ) (h : True) : s[n]'h = get s n :=
  rfl

@[simp]
theorem get_strmOf {f : ℕ → α} {m : ℕ} : get ₛ[ f n | n ] m = f m :=
  rfl

/-- Prepend an element to a stream. -/
def cons (a : α) (s : Stream' α) : Stream' α :=
  ₛ[ (match m with
      | 0 => a
      | n + 1 => get s n) | m ]
#align stream.cons Stream'.cons

infixr:67 " ::ₛ " => cons

/-- Head of a stream: `Stream'.head s = Stream'.get s 0`. -/
abbrev head (s : Stream' α) : α := s.get 0
#align stream.head Stream'.head

/-- Tail of a stream: `Stream'.tail (h ::ₛ t) = t`. -/
def tail (s : Stream' α) : Stream' α := ₛ[ s.get (i + 1) | i ]
#align stream.tail Stream'.tail

/-- Drop first `n` elements of a stream. -/
def drop (n : Nat) (s : Stream' α) : Stream' α := ₛ[ s.get (i + n) | i ]
#align stream.drop Stream'.drop

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def All (p : α → Prop) (s : Stream' α) := ∀ n, p (get s n)
#align stream.all Stream'.All

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def Any (p : α → Prop) (s : Stream' α) := ∃ n, p (get s n)
#align stream.any Stream'.Any

/-- `a ∈ s` means that `a = Stream'.get n s` for some `n`. -/
instance : Membership α (Stream' α) :=
  ⟨fun a s => Any (fun b => a = b) s⟩

/-- Apply a function `f` to all elements of a stream `s`. -/
def map (f : α → β) (s : Stream' α) : Stream' β := ₛ[ f (get s n) | n ]
#align stream.map Stream'.map

/-- Zip two streams using a binary operation:
`Stream'.get (Stream'.zip f s₁ s₂) n = f (Stream'.get s₁ n) (Stream'.get s₂ n)`. -/
def zip (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ :=
  ₛ[ f (get s₁ n) (get s₂ n) | n ]
#align stream.zip Stream'.zip

/-- Enumerate a stream by tagging each element with its index. -/
def enum (s : Stream' α) : Stream' (ℕ × α) := ₛ[ (n, s.get n) | n ]
#align stream.enum Stream'.enum

/-- The constant stream: `Stream'.get (Stream'.const a) n = a`. -/
def const (a : α) : Stream' α := ₛ[ a | _ ]
#align stream.const Stream'.const

instance : Functor Stream' where
  map f s := map f s
  mapConst a _ := const a

instance : Pure Stream' where
  pure a := const a

@[simp]
theorem map_eq_map (f : α → β) : Functor.map f = map f :=
  rfl

@[simp]
theorem mapConst_eq_const (a : α) (s : Stream' β) : Functor.mapConst a s = const a :=
  rfl

/-- Iterates of a function as a stream. -/
def iterate (f : α → α) (a : α) : Stream' α :=
  ₛ[ Nat.recOn n a (fun _ r => f r) | n ]
#align stream.iterate Stream'.iterate

/-- `corec f g b` is the corecursor for `Stream' α` as a coinductive type.
  `head (corec f g a) = f a`, and `tail (corec f g a) = corec f g (g a)`. -/
def corec (f : α → β) (g : α → α) : α → Stream' β := fun a => map f (iterate g a)
#align stream.corec Stream'.corec

/-- `corecOn` is `corec` with swapped arguments. -/
def corecOn (a : α) (f : α → β) (g : α → α) : Stream' β :=
  corec f g a
#align stream.corec_on Stream'.corecOn

/-- `corec' f a` is the corecursor for `Stream' α` as a coinductive type.
  `head (corec' f a) = (f a).1`, and `tail (corec' f a) = corec f (f a).2`. -/
def corec' (f : α → β × α) : α → Stream' β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)
#align stream.corec' Stream'.corec'

-- porting note: this `#align` should be elsewhere but idk where
#align state StateM

/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)
#align stream.corec_state Stream'.corecState

#align stream.unfolds Stream'.corec

/-- Interleave two streams. -/
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corecOn (s₁, s₂) (fun (s₁, _) => head s₁) (fun (s₁, s₂) => (s₂, tail s₁))
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
def appendStream : List α → Stream' α → Stream' α
  | []    , s => s
  | a :: l, s => a ::ₛ appendStream l s
#align stream.append_stream Stream'.appendStream

instance : HAppend (List α) (Stream' α) (Stream' α) where
  hAppend := appendStream

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Stream' α → List α
  | 0    , _ => []
  | n + 1, s => head s :: take n (tail s)
#align stream.take Stream'.take

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v
#align stream.cycle_f Stream'.cycleF

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (_, []      , v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, v₂ :: l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)
#align stream.cycle_g Stream'.cycleG

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : ∀ l : List α, l ≠ [] → Stream' α
  | []    , h => absurd rfl h
  | a :: l, _ => corec Stream'.cycleF Stream'.cycleG (a, l, a, l)
#align stream.cycle Stream'.cycle

/-- Tails of a stream, starting with `Stream'.tail s`. -/
def tails (s : Stream' α) : Stream' (Stream' α) :=
  corec id tail (tail s)
#align stream.tails Stream'.tails

/-- An auxiliary definition for `Stream'.inits`. -/
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corecOn (l, s) (fun (a, _) => a) (fun (l', s') => (l' ++ [head s'], tail s'))
#align stream.inits_core Stream'.initsCore

/-- Nonempty initial segments of a stream. -/
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [head s] (tail s)
#align stream.inits Stream'.inits

#align stream.pure Stream'.const

@[simp]
theorem pure_eq_const {a : α} : (Pure.pure a : Stream' α) = const a :=
  rfl

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : Stream' (α → β)) (s : Stream' α) : Stream' β := ₛ[ get f n (get s n) | n ]
#align stream.apply Stream'.apply

infixl:75 " ⊛ " => apply

/-- The stream of natural numbers: `Stream'.get n Stream'.nats = n`. -/
def nats : Stream' Nat := ₛ[ n | n ]
#align stream.nats Stream'.nats

end Stream'
