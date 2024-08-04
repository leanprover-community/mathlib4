/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.Order.Ring.Defs

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

/-- Forget that a positive cone in a ring respects the multiplicative structure. -/
add_decl_doc PositiveCone.toPositiveCone

/-- A total positive cone in a nontrivial ring induces a linear order. -/
structure TotalPositiveCone (α : Type*) [Ring α] extends PositiveCone α,
  AddCommGroup.TotalPositiveCone α

/-- Forget that a `TotalPositiveCone` in a ring is total. -/
add_decl_doc TotalPositiveCone.toPositiveCone_1

/-- Forget that a `TotalPositiveCone` in a ring respects the multiplicative structure. -/
add_decl_doc TotalPositiveCone.toTotalPositiveCone

theorem PositiveCone.one_pos (C : PositiveCone α) : C.pos 1 :=
  (C.pos_iff _).2 ⟨C.one_nonneg, fun h => one_ne_zero <| C.nonneg_antisymm C.one_nonneg h⟩

end Ring

open Ring

/-- Construct a `StrictOrderedRing` by designating a positive cone in an existing `Ring`. -/
def StrictOrderedRing.mkOfPositiveCone (C : PositiveCone α) : StrictOrderedRing α :=
  { ‹Ring α›, OrderedAddCommGroup.mkOfPositiveCone C.toPositiveCone with
    exists_pair_ne := ⟨0, 1, fun h => by simpa [← h, C.pos_iff] using C.one_pos⟩,
    zero_le_one := by
      change C.nonneg (1 - 0)
      convert C.one_nonneg
      simp,
    mul_pos := fun x y xp yp => by
      change C.pos (x * y - 0)
      -- Porting note: used to be convert, but it relied on unfolding definitions
      rw [sub_zero]
      exact C.mul_pos x y (by rwa [← sub_zero x]) (by rwa [← sub_zero y]) }

/-- Construct a `LinearOrderedRing` by
designating a positive cone in an existing `Ring`. -/
def LinearOrderedRing.mkOfPositiveCone (C : TotalPositiveCone α) : LinearOrderedRing α :=
  { LinearOrderedAddCommGroup.mkOfPositiveCone C.toTotalPositiveCone,
    StrictOrderedRing.mkOfPositiveCone C.toPositiveCone_1 with }
