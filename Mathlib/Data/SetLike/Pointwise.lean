/-
Copyright (c) 2021 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Hom.Basic

/-! # Pointwise instances on `SetLike`s

This file provides:

* `IsConcreteNeg`
* `SetLike.pointwiseNeg`
* `SetLike.involutivePointwiseNeg`
-/

@[expose] public section

open scoped Pointwise

/-- A class to indicate that the instance of `Neg` on the type is compatible with the
canonical injection between `A` and `Set B`.
-/
class IsConcreteNeg (α : Type*) (V : outParam Type*) [Neg V] [SetLike α V] where
  /-- Mapping an instance of `α` to its pointwise negative. -/
  neg : α → α
  coe_set_neg' (p : α) : neg p = -(p : Set V)

namespace SetLike

variable {α : Type*} {V : Type*}
variable [Neg V] [SetLike α V] [IsConcreteNeg α V]

/-- A `SetLike` with every element negated.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
protected def pointwiseNeg : Neg α := ⟨IsConcreteNeg.neg⟩

scoped[Pointwise] attribute [instance] SetLike.pointwiseNeg

open scoped Pointwise

@[simp] theorem coe_set_neg (p : α) : ↑(-p) = -(p : Set V) :=
  IsConcreteNeg.coe_set_neg' p

@[simp] theorem mem_neg {p : α} {g : V} : g ∈ -p ↔ -g ∈ p := by simp [← SetLike.mem_coe]

variable {α : Type*} {V : Type*}
variable [InvolutiveNeg V] [SetLike α V] [IsConcreteNeg α V]

/-- `SetLike.pointwiseNeg` is involutive.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
protected def involutivePointwiseNeg : InvolutiveNeg α where
  neg_neg _ := SetLike.coe_injective (by simp)

scoped[Pointwise] attribute [instance] SetLike.involutivePointwiseNeg

variable [LE α] [IsConcreteLE α V]

@[simp] theorem neg_le_neg {p q : α} : -p ≤ -q ↔ p ≤ q := by
  simp [← SetLike.coe_subset_coe]

theorem neg_le {p q : α} : -p ≤ q ↔ p ≤ -q := by
  simp [← SetLike.coe_subset_coe, Set.neg_subset]

variable {α : Type*} {V : Type*}
variable [InvolutiveNeg V] [SetLike α V] [IsConcreteNeg α V]
variable [PartialOrder α] [IsConcreteLE α V]

theorem neg_eq_self_iff_neg_le {p : α} : -p = p ↔ -p ≤ p :=
  ⟨le_of_eq, fun h => antisymm h <| neg_le.mp h⟩

/-- `SetLike.pointwiseNeg` as an order isomorphism. -/
def negOrderIso : α ≃o α where
  toEquiv := Equiv.neg _
  map_rel_iff' := neg_le_neg

end SetLike
