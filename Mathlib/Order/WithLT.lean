/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.RelClasses

/-!
# Type alias for overriding order instances

This file defines `WithLT α r`, for a partially ordered less-than relation `r`, as a type alias
for `α` where `toLT r x < toLT r y ↔ r x y`. This lets us override the order instance of a type, or
apply API for bundled relations to unbundled ones.
-/

public section

/-- A one-field structure wrapper for `α` with a given well-order `r`. -/
@[ext]
structure WithLT (α : Type*) (r : α → α → Prop) [IsStrictOrder α r] where
  /-- Converts an element of `α` to an element of `WithLT α r`. -/
  toLT (r) ::
  /-- Converts an element of `WithLT α r` to an element of `α`. -/
  ofLT : α

namespace WithLT
variable {α : Type*} {r : α → α → Prop}

section IsStrictOrder
variable [IsStrictOrder α r]

variable (α r) in
/-- `WithLT.ofLT` and `WithLT.toLT` as an equivalence. -/
@[expose, simps]
protected def equiv : WithLT α r ≃ α where
  toFun := ofLT
  invFun := toLT r
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem ofLT_toLT (x : α) : ofLT (toLT r x) = x := rfl
@[simp] theorem toLT_ofLT (x : WithLT α r) : toLT r (ofLT x) = x := rfl

open Classical in
noncomputable instance : PartialOrder (WithLT α r) :=
  letI : PartialOrder α := partialOrderOfSO r
  PartialOrder.lift _ (WithLT.equiv α r).injective

instance [Nonempty α] : Nonempty (WithLT α r) :=
  (WithLT.equiv α r).nonempty

theorem lt_def {x y : WithLT α r} : x < y ↔ r (ofLT x) (ofLT y) := .rfl
theorem toLT_lt_toLT_iff {x y : α} : toLT r x < toLT r y ↔ r x y := .rfl

theorem le_def {x y : WithLT α r} : x ≤ y ↔ x = y ∨ r (ofLT x) (ofLT y) := le_iff_eq_or_lt

end IsStrictOrder

section IsStrictTotalOrder
variable [IsStrictTotalOrder α r]

open Classical in
noncomputable instance : LinearOrder (WithLT α r) :=
  letI : LinearOrder α := linearOrderOfSTO r
  LinearOrder.lift' _ (WithLT.equiv α r).injective

theorem le_def' {x y : WithLT α r} : x ≤ y ↔ ¬ r (ofLT y) (ofLT x) := not_lt.symm
theorem toLT_le_toLT_iff {x y : α} : toLT r x ≤ toLT r y ↔ ¬ r y x := le_def'

end IsStrictTotalOrder

section WellFounded
variable [wf : WellFounded r] [IsStrictOrder α r]

instance : WellFoundedLT (WithLT α r) := by
  apply InvImage.wf _ wf

end WellFounded
end WithLT
