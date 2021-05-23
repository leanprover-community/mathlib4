/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mem
/-!

# Sets

This file sets up the theory of subsets of a type.

## Main definitions

* `{a : X | p a} : Set X` : the subset of `X` cut out by the predicate `p : X → Prop`
* `{a | p a} : Set X` : equal to `{a : X | p a}`
* `{a ∈ S | p a} : Set X` : the subset of `X` consisting of the elements of `S : set X`
     which are cut out by `p`.

## Implementation issues

As in Lean 3, `Set X := X → Prop`

I didn't call this file Data.Set.Basic because it contains core Lean 3
stuff which happens before mathlib3's data.set.basic .
This file is a port of the core Lean 3 file `lib/lean/library/init/data/set.lean`.

## TODO

Notation {a,b,c} for finite sets (both parser and prettyprinter).

-/

universes u v

def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α :=
p

class Subset (α : Type u) :=
(subset : α → α → Prop)

infix:50 " ⊆ " => Subset.subset

class Union (α : Type u) :=
(union : α → α → α)

infixl:65 " ∪ " => Union.union

class Inter (α : Type u) :=
(inter : α → α → α)

infixl:70 " ∩ " => Inter.inter

class Sdiff (α : Type u) :=
(sdiff : α → α → α)

infix:70 " \\ " => Sdiff.sdiff

namespace Set

variable {α : Type u} {β : Type v}

protected def mem (a : α) (s : Set α) :=
s a

instance : Mem α (Set α) :=
⟨Set.mem⟩

protected def subset (s₁ s₂ : Set α) :=
∀ {a}, a ∈ s₁ → a ∈ s₂

instance : Subset (Set α) :=
⟨Set.subset⟩

instance : EmptyCollection (Set α) :=
⟨λ a => false⟩

declare_syntax_cat binderterm -- notation for `a` or `a : A` or `a ∈ S`
syntax ident : binderterm
syntax ident ":" term : binderterm
syntax ident "∈" term : binderterm

-- Notation for sets
syntax "{" binderterm "|" term "}" : term

macro_rules
 -- {a : A | p a}
| `({ $x:ident : $t | $p }) => `(setOf (λ ($x:ident : $t) => $p))
 -- {a | p a}
| `({ $x:ident | $p }) => `(setOf (λ ($x:ident) => $p))
 -- {a ∈ s | p a} := {a | a ∈ s ∧ p a}
| `({ $x:ident ∈ $s | $p }) => `(setOf (λ $x => $x ∈ $s ∧ $p))

syntax "∀" binderterm "," term : term
syntax "∃" binderterm "," term : term

macro_rules
-- ∀ x ∈ s, p := ∀ x, x ∈ s → p
| `(∀ $x:ident ∈ $s, $p) => `(∀ $x:ident, $x ∈ $s → $p)
-- ∃ x ∈ s, p := ∃ x, x ∈ s ∧ p
| `(∃ $x:ident ∈ $s, $p) => `(∃ $x:ident, $x ∈ $s ∧ $p)

def univ : Set α := {a | True }

protected def insert (a : α) (s : Set α) : Set α :=
{b | b = a ∨ b ∈ s}

protected def union (s₁ s₂ : Set α) : Set α :=
{a | a ∈ s₁ ∨ a ∈ s₂}

instance : Union (Set α) :=
⟨Set.union⟩

protected def inter (s₁ s₂ : Set α) : Set α :=
{a | a ∈ s₁ ∧ a ∈ s₂}

instance : Inter (Set α) :=
⟨Set.inter⟩

def compl (s : Set α) : Set α :=
{a | a ∉ s}

protected def diff (s t : Set α) : Set α :=
{a ∈ s | a ∉ t}

instance : Sdiff (Set α) :=
⟨Set.diff⟩

def powerset (s : Set α) : Set (Set α) :=
{t | t ⊆ s}

prefix:100 "𝒫" => powerset

@[reducible]
def sUnion (s : Set (Set α)) : Set α := {t | ∃ a ∈ s, t ∈ a}

prefix:110 "⋃₀" => sUnion

def image (f : α → β) (s : Set α) : Set β :=
{b | ∃ a, a ∈ s ∧ f a = b}

instance : Functor Set :=
{ map := @Set.image }

instance : LawfulFunctor Set :=
{ id_map := λ s => funext $ λ b => propext ⟨λ ⟨_, sb, rfl⟩ => sb, λ sb => ⟨_, sb, rfl⟩⟩,
  comp_map := λ g h s => funext $ λ c => propext
    ⟨λ ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     λ ⟨b, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ => ⟨a, ⟨h₁, show h (g a) = c from h₂ ▸ h₃⟩⟩⟩,
  map_const := rfl }

end Set
