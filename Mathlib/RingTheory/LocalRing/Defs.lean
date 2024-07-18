/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.Ideal.Basic

#align_import ring_theory.ideal.local_ring from "leanprover-community/mathlib"@"ec1c7d810034d4202b0dd239112d1792be9f6fdc"

/-!

# Local rings

Define local rings as commutative rings having a unique maximal ideal.

## Main definitions

* `LocalRing`: A predicate on commutative semirings, stating that for any pair of elements that
  adds up to `1`, one of them is a unit. This is shown to be equivalent to the condition that there
  exists a unique maximal ideal.
* `LocalRing.maximalIdeal`: The unique maximal ideal for a local rings. Its carrier set is the
  set of non units.

-/

universe u v

variable {R : Type u} {S : Type v}

/-- A semiring is local if it is nontrivial and `a` or `b` is a unit whenever `a + b = 1`.
Note that `LocalRing` is a predicate. -/
class LocalRing (R : Type u) [Semiring R] extends Nontrivial R : Prop where
  of_is_unit_or_is_unit_of_add_one ::
  /-- in a local ring `R`, if `a + b = 1`, then either `a` is a unit or `b` is a unit. In another
    word, for every `a : R`, either `a` is a unit or `1 - a` is a unit. -/
  isUnit_or_isUnit_of_add_one {a b : R} (h : a + b = 1) : IsUnit a ∨ IsUnit b
#align local_ring LocalRing

section CommSemiring

variable [CommSemiring R]

namespace LocalRing

variable [LocalRing R]

theorem isUnit_or_isUnit_of_isUnit_add {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one, mul_add] at hu
  apply Or.imp _ _ (isUnit_or_isUnit_of_add_one hu) <;> exact isUnit_of_mul_isUnit_right
#align local_ring.is_unit_or_is_unit_of_is_unit_add LocalRing.isUnit_or_isUnit_of_isUnit_add

theorem nonunits_add {a b : R} (ha : a ∈ nonunits R) (hb : b ∈ nonunits R) : a + b ∈ nonunits R :=
  fun H => not_or_of_not ha hb (isUnit_or_isUnit_of_isUnit_add H)
#align local_ring.nonunits_add LocalRing.nonunits_add

variable (R)

/-- The ideal of elements that are not units. -/
def maximalIdeal : Ideal R where
  carrier := nonunits R
  zero_mem' := zero_mem_nonunits.2 <| zero_ne_one
  add_mem' {_ _} hx hy := nonunits_add hx hy
  smul_mem' _ _ := mul_mem_nonunits_right
#align local_ring.maximal_ideal LocalRing.maximalIdeal

end LocalRing

end CommSemiring
