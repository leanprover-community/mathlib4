/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Defs

#align_import algebra.order.ring.cone from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# Constructing an ordered ring from a ring with a specified positive cone.

-/


/-! ### Positive cones -/


variable {α : Type*} [Ring α] [Nontrivial α]

namespace Ring

/-- A positive cone in a ring consists of a positive cone in underlying `AddCommGroup`,
which contains `1` and such that the positive elements are closed under multiplication. -/
structure PositiveCone (α : Type*) [Ring α] extends AddCommGroup.PositiveCone α where
  /-- In a positive cone, `1` is `nonneg` -/
  one_nonneg : nonneg 1
  /-- In a positive cone, if `a` and `b` are `pos` then so is `a * b` -/
  mul_pos : ∀ a b, pos a → pos b → pos (a * b)
#align ring.positive_cone Ring.PositiveCone

/-- Forget that a positive cone in a ring respects the multiplicative structure. -/
add_decl_doc PositiveCone.toPositiveCone
#align ring.positive_cone.to_positive_cone Ring.PositiveCone.toPositiveCone

/-- A total positive cone in a nontrivial ring induces a linear order. -/
structure TotalPositiveCone (α : Type*) [Ring α] extends PositiveCone α,
  AddCommGroup.TotalPositiveCone α
#align ring.total_positive_cone Ring.TotalPositiveCone
#align ring.total_positive_cone.to_positive_cone Ring.TotalPositiveCone.toPositiveCone_1

/-- Forget that a `TotalPositiveCone` in a ring is total. -/
add_decl_doc TotalPositiveCone.toPositiveCone_1

/-- Forget that a `TotalPositiveCone` in a ring respects the multiplicative structure. -/
add_decl_doc TotalPositiveCone.toTotalPositiveCone
#align ring.total_positive_cone.to_total_positive_cone Ring.TotalPositiveCone.toTotalPositiveCone

theorem PositiveCone.one_pos (C : PositiveCone α) : C.pos 1 :=
  (C.pos_iff _).2 ⟨C.one_nonneg, fun h => one_ne_zero <| C.nonneg_antisymm C.one_nonneg h⟩
#align ring.positive_cone.one_pos Ring.PositiveCone.one_pos

end Ring

open Ring

/-- Construct a `StrictOrderedRing` by designating a positive cone in an existing `Ring`. -/
def StrictOrderedRing.mkOfPositiveCone (C : PositiveCone α) : StrictOrderedRing α :=
  { ‹Ring α›, OrderedAddCommGroup.mkOfPositiveCone C.toPositiveCone with
    exists_pair_ne := ⟨0, 1, fun h => by simpa [← h, C.pos_iff] using C.one_pos⟩,
                                         -- 🎉 no goals
    zero_le_one := by
      change C.nonneg (1 - 0)
      -- ⊢ AddCommGroup.PositiveCone.nonneg C.toPositiveCone (1 - 0)
      convert C.one_nonneg
      -- ⊢ 1 - 0 = 1
      simp,
      -- 🎉 no goals
    mul_pos := fun x y xp yp => by
      change C.pos (x * y - 0)
      -- ⊢ AddCommGroup.PositiveCone.pos C.toPositiveCone (x * y - 0)
      -- porting note: used to be convert, but it relied on unfolding definitions
      rw [sub_zero]
      -- ⊢ AddCommGroup.PositiveCone.pos C.toPositiveCone (x * y)
      exact C.mul_pos x y (by rwa [← sub_zero x]) (by rwa [← sub_zero y]) }
      -- 🎉 no goals
#align strict_ordered_ring.mk_of_positive_cone StrictOrderedRing.mkOfPositiveCone

/-- Construct a `LinearOrderedRing` by
designating a positive cone in an existing `Ring`. -/
def LinearOrderedRing.mkOfPositiveCone (C : TotalPositiveCone α) : LinearOrderedRing α :=
  { LinearOrderedAddCommGroup.mkOfPositiveCone C.toTotalPositiveCone,
    StrictOrderedRing.mkOfPositiveCone C.toPositiveCone_1 with }
#align linear_ordered_ring.mk_of_positive_cone LinearOrderedRing.mkOfPositiveCone
