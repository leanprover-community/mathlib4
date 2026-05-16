/-
Copyright (c) 2026 Haitao Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitao Ji
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Defs

/-!

# Fuzzy sets

This file defines the basic theory of fuzzy sets.

A fuzzy set on a type `α` with membership values in `L` is represented as a function
`α → L`.

We use `abbrev` for `FuzzySet` so that it reduces to `α → L`. This allows fuzzy sets
to inherit pointwise order and lattice structures from the corresponding `Pi` type
instances.

## Main definitions

* `FuzzySet α L`: The type of fuzzy sets on `α` with values in `L`.
* `FuzzySet.degree`: The membership degree of an element in a fuzzy set.
* `FuzzySet.support`: The support of a fuzzy set.
* `FuzzySet.core`: The core of a fuzzy set.
* `FuzzySet.weakCut`: The weak cut of a fuzzy set.
* `FuzzySet.strongCut`: The strong cut of a fuzzy set.

## Main results

* `FuzzySet.weakCut_antitone`: weak cuts are antitone in the level.
* `FuzzySet.strongCut_antitone`: strong cuts are antitone in the level.
* `FuzzySet.weakCut_mono`: weak cuts are monotone in the fuzzy set.
* `FuzzySet.strongCut_mono`: strong cuts are monotone in the fuzzy set.
-/

@[expose] public section

/-- `FuzzySet α L` is the type of fuzzy sets on `α` with membership values in `L`. -/
abbrev FuzzySet (α : Type*) (L : Type*) :=
  α → L

namespace FuzzySet

variable {α : Type*} {L : Type*}

/-! ### Basic API -/

/-- The membership degree of an element `x` in a fuzzy set `A`. -/
def degree (A : FuzzySet α L) (x : α) : L :=
  A x

/-- See `FuzzySet.degree`. -/
@[simp]
theorem degree_apply {A : FuzzySet α L} {x : α} : A.degree x = A x :=
  rfl

/-- Two fuzzy sets are equal iff their degrees at every element are equal. -/
protected theorem ext {A B : FuzzySet α L} (h : ∀ x, A.degree x = B.degree x) : A = B :=
  funext h

/-- See `FuzzySet.ext`. -/
theorem ext_iff {A B : FuzzySet α L} : A = B ↔ ∀ x, A.degree x = B.degree x :=
  ⟨fun h _ => h ▸ rfl, FuzzySet.ext⟩

attribute [ext] FuzzySet.ext

/-! ### Characteristic sets -/

section Support

variable [Bot L] [LT L]

/-- The support of a fuzzy set `A` is the set of elements `x` such that `⊥ < A.degree x`. -/
def support (A : FuzzySet α L) : Set α :=
  {x | ⊥ < A.degree x}

/-- See `FuzzySet.support`. -/
@[simp]
theorem mem_support {A : FuzzySet α L} {x : α} :
    x ∈ A.support ↔ ⊥ < A.degree x :=
  Iff.rfl

end Support

section Core

variable [Top L]

/-- The core of a fuzzy set `A` is the set of elements `x` such that `A.degree x = ⊤`. -/
def core (A : FuzzySet α L) : Set α :=
  {x | A.degree x = ⊤}

/-- See `FuzzySet.core`. -/
@[simp]
theorem mem_core {A : FuzzySet α L} {x : α} :
    x ∈ A.core ↔ A.degree x = ⊤ :=
  Iff.rfl

end Core

/-! ### Cuts -/

section WeakCut

variable [LE L]

/-- The weak cut of a fuzzy set `A` at level `a` is `{x | a ≤ A.degree x}`. -/
def weakCut (A : FuzzySet α L) (a : L) : Set α :=
  {x | a ≤ A.degree x}

/-- See `FuzzySet.weakCut`. -/
@[simp]
theorem mem_weakCut {A : FuzzySet α L} {a : L} {x : α} :
    x ∈ A.weakCut a ↔ a ≤ A.degree x :=
  Iff.rfl

end WeakCut

section StrongCut

variable [LT L]

/-- The strong cut of a fuzzy set `A` at level `a` is `{x | a < A.degree x}`. -/
def strongCut (A : FuzzySet α L) (a : L) : Set α :=
  {x | a < A.degree x}

/-- See `FuzzySet.strongCut`. -/
@[simp]
theorem mem_strongCut {A : FuzzySet α L} {a : L} {x : α} :
    x ∈ A.strongCut a ↔ a < A.degree x :=
  Iff.rfl

end StrongCut

/-! ### Monotonicity -/

section Monotonicity

variable [Preorder L]

/-- Weak cuts are antitone in the level. -/
theorem weakCut_antitone (A : FuzzySet α L) :
    Antitone A.weakCut :=
  fun _ _ h _ hx => le_trans h hx

/-- Strong cuts are antitone in the level. -/
theorem strongCut_antitone (A : FuzzySet α L) :
    Antitone A.strongCut :=
  fun _ _ h _ hx => lt_of_le_of_lt h hx

/-- Weak cuts are monotone in the fuzzy set. -/
theorem weakCut_mono {A B : FuzzySet α L} (hAB : A ≤ B) (a : L) :
    A.weakCut a ⊆ B.weakCut a :=
  fun _ hx => le_trans hx (hAB _)

/-- Strong cuts are monotone in the fuzzy set. -/
theorem strongCut_mono {A B : FuzzySet α L} (hAB : A ≤ B) (a : L) :
    A.strongCut a ⊆ B.strongCut a :=
  fun _ hx => lt_of_lt_of_le hx (hAB _)

end Monotonicity

end FuzzySet
