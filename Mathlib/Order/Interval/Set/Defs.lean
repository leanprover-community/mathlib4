/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.Defs
import Mathlib.Order.Defs.PartialOrder

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

namespace Set

variable {α : Type*} [Preorder α] {a b x : α}

/-- `Ioo a b` is the left-open right-open interval $(a, b)$. -/
def Ioo (a b : α) := { x | a < x ∧ x < b }

@[simp] theorem mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b := Iff.rfl
theorem Ioo_def (a b : α) : { x | a < x ∧ x < b } = Ioo a b := rfl

/-- `Ico a b` is the left-closed right-open interval $[a, b)$. -/
def Ico (a b : α) := { x | a ≤ x ∧ x < b }

@[simp] theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b := Iff.rfl
theorem Ico_def (a b : α) : { x | a ≤ x ∧ x < b } = Ico a b := rfl

/-- `Iio b` is the left-infinite right-open interval $(-∞, b)$. -/
def Iio (b : α) := { x | x < b }

@[simp] theorem mem_Iio : x ∈ Iio b ↔ x < b := Iff.rfl
theorem Iio_def (a : α) : { x | x < a } = Iio a := rfl

/-- `Icc a b` is the left-closed right-closed interval $[a, b]$. -/
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }

@[simp] theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl
theorem Icc_def (a b : α) : { x | a ≤ x ∧ x ≤ b } = Icc a b := rfl

/-- `Iic b` is the left-infinite right-closed interval $(-∞, b]$. -/
def Iic (b : α) := { x | x ≤ b }

@[simp] theorem mem_Iic : x ∈ Iic b ↔ x ≤ b := Iff.rfl
theorem Iic_def (b : α) : { x | x ≤ b } = Iic b := rfl

/-- `Ioc a b` is the left-open right-closed interval $(a, b]$. -/
def Ioc (a b : α) := { x | a < x ∧ x ≤ b }

@[simp] theorem mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := Iff.rfl
theorem Ioc_def (a b : α) : { x | a < x ∧ x ≤ b } = Ioc a b := rfl

/-- `Ici a` is the left-closed right-infinite interval $[a, ∞)$. -/
def Ici (a : α) := { x | a ≤ x }

@[simp] theorem mem_Ici : x ∈ Ici a ↔ a ≤ x := Iff.rfl
theorem Ici_def (a : α) : { x | a ≤ x } = Ici a := rfl

/-- `Ioi a` is the left-open right-infinite interval $(a, ∞)$. -/
def Ioi (a : α) := { x | a < x }

@[simp] theorem mem_Ioi : x ∈ Ioi a ↔ a < x := Iff.rfl
theorem Ioi_def (a : α) : { x | a < x } = Ioi a := rfl

/-- We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
`LinearOrderedField`, then this condition is also equivalent to `Convex α s`. -/
class OrdConnected (s : Set α) : Prop where
  /-- `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the interval `[[x, y]]`. -/
  out' ⦃x : α⦄ (hx : x ∈ s) ⦃y : α⦄ (hy : y ∈ s) : Icc x y ⊆ s

end Set
