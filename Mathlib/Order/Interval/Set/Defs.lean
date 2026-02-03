/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Push.Attr

/-!
# Intervals

In any preorder `α`, we define intervals
(which on each side can be either infinite, open, or closed)
using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side.
For instance, `Ioc a b` denotes the interval `(a, b]`.

We also define a typeclass `Set.OrdConnected`
saying that a set includes `Set.Icc a b` whenever it contains both `a` and `b`.
-/

@[expose] public section

namespace Set

variable {α : Type*} [Preorder α] {a b x : α}

/-- `Iio b` is the left-infinite right-open interval $(-∞, b)$. -/
@[to_dual /-- `Ioi a` is the left-open right-infinite interval $(a, ∞)$. -/]
def Iio (b : α) := { x | x < b }

@[to_dual (attr := simp, grind =, push)] theorem mem_Iio : x ∈ Iio b ↔ x < b := Iff.rfl
@[to_dual] theorem Iio_def (a : α) : { x | x < a } = Iio a := rfl

/-- `Iic b` is the left-infinite right-closed interval $(-∞, b]$. -/
@[to_dual /-- `Ici a` is the left-closed right-infinite interval $[a, ∞)$. -/]
def Iic (b : α) := { x | x ≤ b }

@[to_dual (attr := simp, grind =, push)] theorem mem_Iic : x ∈ Iic b ↔ x ≤ b := Iff.rfl
@[to_dual] theorem Iic_def (b : α) : { x | x ≤ b } = Iic b := rfl

/-- `Ioo a b` is the left-open right-open interval $(a, b)$. -/
@[to_dual self (reorder := a b)]
def Ioo (a b : α) := { x | a < x ∧ x < b }

to_dual_insert_cast Ioo := by grind

@[simp, grind =, push, to_dual none] theorem mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b := Iff.rfl
@[to_dual none] theorem Ioo_def (a b : α) : { x | a < x ∧ x < b } = Ioo a b := rfl

/-- `Ico a b` is the left-closed right-open interval $[a, b)$. -/
def Ico (a b : α) := { x | a ≤ x ∧ x < b }

/-- `Ioc a b` is the left-open right-closed interval $(a, b]$. -/
@[to_dual existing (reorder := a b)]
def Ioc (a b : α) := { x | a < x ∧ x ≤ b }

to_dual_insert_cast Ico := by grind
to_dual_insert_cast Ioc := by grind

@[simp, grind =, push, to_dual none] theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b := Iff.rfl
@[to_dual none] theorem Ico_def (a b : α) : { x | a ≤ x ∧ x < b } = Ico a b := rfl

@[simp, grind =, push, to_dual none] theorem mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := Iff.rfl
@[to_dual none] theorem Ioc_def (a b : α) : { x | a < x ∧ x ≤ b } = Ioc a b := rfl

/-- `Icc a b` is the left-closed right-closed interval $[a, b]$. -/
@[to_dual self (reorder := a b)]
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }

to_dual_insert_cast Icc := by grind

@[simp, grind =, push, to_dual none] theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl
@[to_dual none] theorem Icc_def (a b : α) : { x | a ≤ x ∧ x ≤ b } = Icc a b := rfl

/-- We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
`LinearOrderedField`, then this condition is also equivalent to `Convex α s`. -/
class OrdConnected (s : Set α) : Prop where
  /-- `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the interval `[[x, y]]`. -/
  out' ⦃x : α⦄ (hx : x ∈ s) ⦃y : α⦄ (hy : y ∈ s) : Icc x y ⊆ s

attribute [to_dual self (reorder := x y, hx hy)] OrdConnected.out'

end Set
