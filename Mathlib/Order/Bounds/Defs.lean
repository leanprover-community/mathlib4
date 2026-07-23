/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.ToDual

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
* `IsCoinitial s`: for every `a`, there exists a member of `s` less than or equal to it.
* `IsCoinitialFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `b ≤ a`
* `SupSet α`, `InfSet α`: typeclasses introducing the operation `SupSet.sSup` and `InfSet.sInf`
  (exported to the root namespace).
* `OrderSupSet α`, `OrderInfSet α`: typeclasses expressing that `sSup` (resp., `sInf`) returns
  the least upper bound (resp., the greatest lower bound) of a set whenever one exists.
-/

@[expose] public section

variable {α : Type*} [LE α]

/-- The set of upper bounds of a set. -/
@[to_dual /-- The set of lower bounds of a set. -/]
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

/-- A set is bounded above if there exists an upper bound. -/
@[to_dual /-- A set is bounded below if there exists a lower bound. -/]
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/]
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/]
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)

/-- A set `s` is said to be cofinal for a set `t` if, for all `a ∈ s` there exists `b ∈ t`
such that `a ≤ b`. -/
@[to_dual /-- A set `s` is said to be coinitial for a set `t` if, for all `a ∈ s` there exists
`b ∈ t` such that `b ≤ a`. -/]
def IsCofinalFor (s t : Set α) := ∀ ⦃a⦄, a ∈ s → ∃ b ∈ t, a ≤ b

/-- A set is cofinal when for every `x : α` there exists `y ∈ s` with `x ≤ y`. -/
@[to_dual /-- A set is coinitial when for every `x : α` there exists `y ∈ s` with `y ≤ x`. -/]
def IsCofinal (s : Set α) : Prop :=
  ∀ x, ∃ y ∈ s, x ≤ y

/-- Class for the `sSup` operator -/
class SupSet (α : Type*) where
  /-- Supremum of a set -/
  sSup : Set α → α

/-- Class for the `sInf` operator -/
@[to_dual existing]
class InfSet (α : Type*) where
  /-- Infimum of a set -/
  sInf : Set α → α

export SupSet (sSup)

export InfSet (sInf)

/-- `OrderSupSet α` expresses that `α` is equipped with the operation `sSup` that returns
the least upper bound of a set whenever one exists. -/
class OrderSupSet (α : Type*) [LE α] extends SupSet α where
  protected isLUB_sSup_of_isLUB s a : IsLUB s a → IsLUB s (sSup s)

/-- `OrderInfSet α` expresses that `α` is equipped with the operation `sInf` that returns
the greatest lower bound of a set whenever one exists. -/
@[to_dual existing]
class OrderInfSet (α : Type*) [LE α] extends InfSet α where
  protected isGLB_sInf_of_isGLB s a : IsGLB s a → IsGLB s (sInf s)
