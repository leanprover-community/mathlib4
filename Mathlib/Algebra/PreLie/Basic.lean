/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.Associator
import Mathlib.GroupTheory.GroupAction.Ring
/-!
# Pre-Lie rings and algebras

In this file we introduce left and righ pre-Lie rings, defined as a `NonUnitalNonAssocRing` where
the associator `associator x y z := (x * y) * z - x * (y * z)` is left or right symmetric,
respectively.

We prove that every `Left(Right)PreLieRing L` is a `Right(Left)PreLieRing L` with
the opposite `mul`. The equivalence is simple given by `op : L ≃* Lᵐᵒᵖ`.

Everything holds for the algebra versions where `L` is also an `R-Module` over a commutative ring
`R`.

## Main definitions
  All are a defined as a `NonUnitalNonAssocRing` whose `associator` satisfies an identity.
  * `LeftPreLieRing`
  * `RightPreLieRing`
  * `LeftPreLieAlgebra`
  * `RightPreLieAlgebra`

## Main results
  * Every `LeftPreLieRing` is a `RightPreLieRing` with the opposite multiplication.

## Implementation notes
There are left and right versions of the structures, equivalent via `ᵐᵒᵖ`.
Perhaps one could be favored but there is no real reason to.

## Tags
pre-lie algebras

-/
open MulOpposite Ring Module

universe u v

namespace NonUnitalNonAssocRing
@[simp]
lemma associator_op {L : Type v} (x y z : Lᵐᵒᵖ) [NonUnitalNonAssocRing L] :
    associator x y z = -op (associator (unop z) (unop y) (unop x)) := by
  simp only [associator_apply, ← unop_mul, ← unop_sub, op_unop, neg_sub]
end NonUnitalNonAssocRing

@[ext]
class LeftPreLieRing (L : Type v) : Type (v + 1) extends NonUnitalNonAssocRing L where
  assoc_symm' (x y z : L) : associator x y z = associator y x z

@[ext]
class RightPreLieRing (L : Type v) : Type (v + 1) extends NonUnitalNonAssocRing L where
  assoc_symm' (x y z : L) : associator x y z = associator x z y

section algebras
variable (R : Type u) [CommRing R]
@[ext]
class LeftPreLieAlgebra (L : Type v) [LeftPreLieRing L] : Type (max u v) extends
  Module R L, IsScalarTower R L L, SMulCommClass R L L
@[ext]
class RightPreLieAlgebra (L : Type v) [RightPreLieRing L] : Type (max u v) extends
  Module R L, IsScalarTower R L L, SMulCommClass R L L
end algebras

namespace LeftPreLieRing
variable {R : Type u} [CommRing R]
variable {L : Type v} [LeftPreLieRing L]

@[simp]
theorem assoc_symm (x y z : L) :
    associator x y z = associator y x z := LeftPreLieRing.assoc_symm' x y z

/-- Every left pre-Lie ring is a right pre-Lie ring with the opposite multiplication -/
instance : RightPreLieRing Lᵐᵒᵖ where
  assoc_symm' x y z := by simp
end LeftPreLieRing

namespace LeftPreLieAlgebra
variable {R : Type u} [CommRing R]
variable {L : Type v} [LeftPreLieRing L] [LeftPreLieAlgebra R L]
/-- Every left pre-Lie algebra is a right pre-Lie algebra with the opposite multiplication -/
instance : RightPreLieAlgebra R Lᵐᵒᵖ where
end LeftPreLieAlgebra

namespace RightPreLieRing
variable {R : Type u} [CommRing R]
variable {L : Type v} [RightPreLieRing L]

@[simp]
theorem assoc_symm (x y z : L) :
    associator x y z = associator x z y := RightPreLieRing.assoc_symm' x y z

/-- Every left pre-Lie ring is a right pre-Lie ring with the opposite multiplication -/
instance : LeftPreLieRing Lᵐᵒᵖ where
  assoc_symm' x y z := by simp
end RightPreLieRing

namespace RightPreLieAlgebra
variable {R : Type u} [CommRing R]
variable {L : Type v} [RightPreLieRing L] [RightPreLieAlgebra R L]
/-- Every left pre-Lie algebra is a right pre-Lie algebra with the opposite multiplication -/
instance : LeftPreLieAlgebra R Lᵐᵒᵖ where
end RightPreLieAlgebra
