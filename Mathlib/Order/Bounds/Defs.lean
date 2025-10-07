/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.TypeStar

/-!
# Definitions about upper/lower bounds

In this file we define:
* `upperBounds`, `lowerBounds` : the set of upper bounds (resp., lower bounds) of a set;
* `BddAbove s`, `BddBelow s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `IsLeast s a`, `IsGreatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `IsLUB s a`, `IsGLB s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.
* `IsCofinal s`: for every `a`, there exists a member of `s` greater or equal to it.
* `IsCofinalFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `a ≤ b`
* `IsCoinitialFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `b ≤ a`
-/

variable {α : Type*} [LE α]

/-- The set of upper bounds of a set. -/
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

/-- The set of lower bounds of a set. -/
def lowerBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }

/-- A set is bounded above if there exists an upper bound. -/
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

/-- A set is bounded below if there exists a lower bound. -/
def BddBelow (s : Set α) :=
  (lowerBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s

/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/
def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ upperBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)

/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def IsGLB (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)

/-- A set `s` is said to be cofinal for a set `t` if, for all `a ∈ s` there exists `b ∈ t`
such that `a ≤ b`. -/
def IsCofinalFor (s t : Set α) := ∀ ⦃a⦄, a ∈ s → ∃ b ∈ t, a ≤ b

/-- A set `s` is said to be coinitial for a set `t` if, for all `a ∈ s` there exists `b ∈ t`
such that `b ≤ a`. -/
def IsCoinitialFor (s t : Set α) := ∀ ⦃a⦄, a ∈ s → ∃ b ∈ t, b ≤ a

/-- A set is cofinal when for every `x : α` there exists `y ∈ s` with `x ≤ y`. -/
def IsCofinal (s : Set α) : Prop :=
  ∀ x, ∃ y ∈ s, x ≤ y
