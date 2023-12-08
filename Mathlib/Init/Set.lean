/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term
import Std.Classes.SetNotation
import Mathlib.Mathport.Rename

/-!

# Sets

This file sets up the theory of sets whose elements have a given type.

## Main definitions

Given a type `X` and a predicate `p : X → Prop`:

* `Set X` : the type of sets whose elements have type `X`
* `{a : X | p a} : Set X` : the set of all elements of `X` satisfying `p`
* `{a | p a} : Set X` : a more concise notation for `{a : X | p a}`
* `{f x y | (x : X) (y : Y)} : Set Z` : a more concise notation for `{z : Z | ∃ x y, f x y = z}`
* `{a ∈ S | p a} : Set X` : given `S : Set X`, the subset of `S` consisting of
   its elements satisfying `p`.

## Implementation issues

As in Lean 3, `Set X := X → Prop`

I didn't call this file Data.Set.Basic because it contains core Lean 3
stuff which happens before mathlib3's data.set.basic .
This file is a port of the core Lean 3 file `lib/lean/library/init/data/set.lean`.

-/

set_option autoImplicit true

/-- A set is a collection of elements of some type `α`.

Although `Set` is defined as `α → Prop`, this is an implementation detail which should not be
relied on. Instead, `setOf` and membership of a set (`∈`) should be used to convert between sets
and predicates.
-/
def Set (α : Type u) := α → Prop
#align set Set

/-- Turn a predicate `p : α → Prop` into a set, also written as `{x | p x}` -/
def setOf {α : Type u} (p : α → Prop) : Set α :=
  p
#align set_of setOf

namespace Set

/-- Membership in a set -/
protected def Mem (a : α) (s : Set α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x ↦ propext (h x))

protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

/-- Porting note: we introduce `≤` before `⊆` to help the unifier when applying lattice theorems
to subset hypotheses. -/
instance : LE (Set α) :=
  ⟨Set.Subset⟩

instance : HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩

instance : EmptyCollection (Set α) :=
  ⟨λ _ => False⟩

open Std.ExtendedBinder in
syntax "{" extBinder " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x:ident ↦ $p)
  | `({ $x:ident : $t | $p }) => `(setOf fun $x:ident : $t ↦ $p)
  | `({ $x:ident $b:binderPred | $p }) =>
    `(setOf fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)

@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) ↦ $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()

open Std.ExtendedBinder in
/--
`{ f x y | (x : X) (y : Y) }` is notation for the set of elements `f x y` constructed from the
binders `x` and `y`, equivalent to `{z : Z | ∃ x y, f x y = z}`.

If `f x y` is a single identifier, it must be parenthesized to avoid ambiguity with `{x | p x}`;
for instance, `{(x) | (x : Nat) (y : Nat) (_hxy : x = y^2)}`.
-/
macro (priority := low) "{" t:term " | " bs:extBinders "}" : term =>
  `({x | ∃ᵉ $bs:extBinders, $t = x})

/--
* `{ pat : X | p }` is notation for pattern matching in set-builder notation,
  where `pat` is a pattern that is matched by all objects of type `X`
  and `p` is a proposition that can refer to variables in the pattern.
  It is the set of all objects of type `X` which, when matched with the pattern `pat`,
  make `p` come out true.
* `{ pat | p }` is the same, but in the case when the type `X` can be inferred.

For example, `{ (m, n) : ℕ × ℕ | m * n = 12 }` denotes the set of all ordered pairs of
natural numbers whose product is 12.

Note that if the type ascription is left out and `p` can be interpreted as an extended binder,
then the extended binder interpretation will be used.  For example, `{ n + 1 | n < 3 }` will
be interpreted as `{ x : Nat | ∃ n < 3, n + 1 = x }` rather than using pattern matching.
-/
macro (name := macroPattSetBuilder) (priority := low-1)
  "{" pat:term " : " t:term " | " p:term "}" : term =>
  `({ x : $t | match x with | $pat => $p })

@[inherit_doc macroPattSetBuilder]
macro (priority := low-1) "{" pat:term " | " p:term "}" : term =>
  `({ x | match x with | $pat => $p })

/-- Pretty printing for set-builder notation with pattern matching. -/
@[app_unexpander setOf]
def setOfPatternMatchUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ match $y:ident with | $pat => $p) =>
      if x == y then
        `({ $pat:term | $p:term })
      else
        throw ()
  | `($_ fun ($x:ident : $ty:term) ↦ match $y:ident with | $pat => $p) =>
      if x == y then
        `({ $pat:term : $ty:term | $p:term })
      else
        throw ()
  | _ => throw ()

def univ : Set α := {_a | True}
#align set.univ Set.univ

protected def insert (a : α) (s : Set α) : Set α := {b | b = a ∨ b ∈ s}

instance : Insert α (Set α) := ⟨Set.insert⟩

protected def singleton (a : α) : Set α := {b | b = a}

instance instSingletonSet : Singleton α (Set α) := ⟨Set.singleton⟩

protected def union (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∨ a ∈ s₂}

instance : Union (Set α) := ⟨Set.union⟩

protected def inter (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∧ a ∈ s₂}

instance : Inter (Set α) := ⟨Set.inter⟩

protected def compl (s : Set α) : Set α := {a | a ∉ s}

protected def diff (s t : Set α) : Set α := {a ∈ s | a ∉ t}

instance : SDiff (Set α) := ⟨Set.diff⟩

def powerset (s : Set α) : Set (Set α) := {t | t ⊆ s}

prefix:100 "𝒫" => powerset

def image (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}

instance : Functor Set where map := @Set.image

instance : LawfulFunctor Set where
  id_map _ := funext fun _ ↦ propext ⟨λ ⟨_, sb, rfl⟩ => sb, λ sb => ⟨_, sb, rfl⟩⟩
  comp_map g h _ := funext $ λ c => propext
    ⟨λ ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     λ ⟨_, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ => ⟨a, ⟨h₁, show h (g a) = c from h₂ ▸ h₃⟩⟩⟩
  map_const := rfl

/-- The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
#align set.nonempty Set.Nonempty

end Set
