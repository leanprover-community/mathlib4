/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term
import Mathlib.Init.SetNotation

/-!

# Sets

This file sets up the theory of sets whose elements have a given type.

## Main definitions

Given a type `X` and a predicate `p : X → Prop`:

* `Set X` : the type of sets whose elements have type `X`
* `{a : X | p a} : Set X` : the set of all elements of `X` satisfying `p`
* `{a | p a} : Set X` : a more concise notation for `{a : X | p a}`
* `{a ∈ S | p a} : Set X` : given `S : Set X`, the subset of `S` consisting of
   its elements satisfying `p`.

## Implementation issues

As in Lean 3, `Set X := X → Prop`

I didn't call this file Data.Set.Basic because it contains core Lean 3
stuff which happens before mathlib3's data.set.basic .
This file is a port of the core Lean 3 file `lib/lean/library/init/data/set.lean`.

-/

def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α :=
p

namespace Set

protected def mem (a : α) (s : Set α) :=
s a

instance : Membership α (Set α) :=
⟨Set.mem⟩

protected def subset (s₁ s₂ : Set α) :=
∀ {a}, a ∈ s₁ → a ∈ s₂

instance : Subset (Set α) :=
⟨Set.subset⟩

instance : EmptyCollection (Set α) :=
⟨λ _ => false⟩

open Mathlib.ExtendedBinder in
syntax "{ " extBinder " | " term " }" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x:ident => $p)
  | `({ $x:ident : $t | $p }) => `(setOf fun $x:ident : $t => $p)
  | `({ $x:ident $b:binderPred | $p }) =>
    `(setOf fun $x:ident => satisfiesBinderPred% $x $b ∧ $p)

@[appUnexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $p) => `({ $x:ident | $p })
  | `($_ fun $x:ident : $ty:term => $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()

open Mathlib.ExtendedBinder in
macro (priority := low) "{ " t:term " | " bs:extBinders " }" : term =>
  `({ x | ∃ᵉ $bs:extBinders, $t = x })

def univ : Set α := {_a | True}

protected def insert (a : α) (s : Set α) : Set α :=
{b | b = a ∨ b ∈ s}

instance : Insert α (Set α) := ⟨Set.insert⟩

protected def singleton (a : α) : Set α :=
{b | b = a}

instance : Singleton α (Set α) := ⟨Set.singleton⟩

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
  { f a | a ∈ s }

instance : Functor Set :=
{ map := @Set.image }

instance : LawfulFunctor Set where
  id_map _ := funext fun _ => propext ⟨λ ⟨_, sb, rfl⟩ => sb, λ sb => ⟨_, sb, rfl⟩⟩
  comp_map g h _ := funext $ λ c => propext
    ⟨λ ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     λ ⟨_, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ => ⟨a, ⟨h₁, show h (g a) = c from h₂ ▸ h₃⟩⟩⟩
  map_const := rfl

end Set
