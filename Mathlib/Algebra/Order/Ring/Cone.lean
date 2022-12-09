/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Constructing an ordered ring from a ring with a specified positive cone.

-/


/-! ### Positive cones -/


variable {α : Type _} [Ring α] [Nontrivial α]

namespace Ring

/-- A positive cone in a ring consists of a positive cone in underlying `add_comm_group`,
which contains `1` and such that the positive elements are closed under multiplication. -/
@[nolint has_nonempty_instance]
structure PositiveCone (α : Type _) [Ring α] extends AddCommGroup.PositiveCone α where
  one_nonneg : nonneg 1
  mul_pos : ∀ a b, Pos a → Pos b → Pos (a * b)
#align ring.positive_cone Ring.PositiveCone

/-- Forget that a positive cone in a ring respects the multiplicative structure. -/
add_decl_doc positive_cone.to_positive_cone

/-- A total positive cone in a nontrivial ring induces a linear order. -/
@[nolint has_nonempty_instance]
structure TotalPositiveCone (α : Type _) [Ring α] extends PositiveCone α,
  AddCommGroup.TotalPositiveCone α
#align ring.total_positive_cone Ring.TotalPositiveCone

/-- Forget that a `total_positive_cone` in a ring is total. -/
add_decl_doc total_positive_cone.to_positive_cone

/-- Forget that a `total_positive_cone` in a ring respects the multiplicative structure. -/
add_decl_doc total_positive_cone.to_total_positive_cone

theorem PositiveCone.one_pos (C : PositiveCone α) : C.Pos 1 :=
  (C.pos_iff _).2 ⟨C.one_nonneg, fun h => one_ne_zero <| C.nonneg_antisymm C.one_nonneg h⟩
#align ring.positive_cone.one_pos Ring.PositiveCone.one_pos

end Ring

open Ring

/-- Construct a `strict_ordered_ring` by designating a positive cone in an existing `ring`. -/
def StrictOrderedRing.mkOfPositiveCone (C : PositiveCone α) : StrictOrderedRing α :=
  { ‹Ring α›, OrderedAddCommGroup.mkOfPositiveCone C.toPositiveCone with
    exists_pair_ne := ⟨0, 1, fun h => by simpa [← h, C.pos_iff] using C.one_pos⟩,
    zero_le_one := by
      change C.nonneg (1 - 0)
      convert C.one_nonneg
      simp,
    mul_pos := fun x y xp yp => by
      change C.pos (x * y - 0)
      convert
        C.mul_pos x y
          (by
            convert xp
            simp)
          (by
            convert yp
            simp)
      simp }
#align strict_ordered_ring.mk_of_positive_cone StrictOrderedRing.mkOfPositiveCone

/-- Construct a `linear_ordered_ring` by
designating a positive cone in an existing `ring`. -/
def LinearOrderedRing.mkOfPositiveCone (C : TotalPositiveCone α) : LinearOrderedRing α :=
  { StrictOrderedRing.mkOfPositiveCone C.toPositiveCone,
    LinearOrderedAddCommGroup.mkOfPositiveCone C.toTotalPositiveCone with }
#align linear_ordered_ring.mk_of_positive_cone LinearOrderedRing.mkOfPositiveCone
