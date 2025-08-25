/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.NonAssoc.PreLie.Basic
/-!
# Lie admissible rings and algebras

We define a Lie-admissible ring as a nonunital nonassociative ring such that the associator
satisfies the identity
```
associator x y z + associator z x y + associator y z x =
  associator y x z + associator z y x + associator x z y
```

## Main definitions:
  * `LieAdmissibleRing`
  * `LieAdmissibleAlgebra`

## Main results
  * `instance [LieAdmissibleRing L] : LieRing L`
  * `instance [CommRing R] [LieAdmissibleRing L] [LieAdmissibleAlgebra R L] : LieAlgebra R L

## Implementation Notes
Algebras are implemented as extending `Module`, `IsScalarTower` and `SMulCommClass` following the
documentation of `Algebra`.

## References
1. [Munthe-Kaas, H.Z., Lundervold, A. *On Post-Lie Algebras, Lie–Butcher Series and Moving
Frames.*][munthe-kaas_lundervold_2013]

## Tags
lie admissible, jacobi identity, lie algebra
-/

/-- A `LieAdmissibleRing` is a `NonUnitalNonAssocRing` such that the canonical bracket
`⁅x, y⁆ := x * y - y * x` turns it into a `LieRing`. This is expressed by an associator identity. -/
@[ext]
class LieAdmissibleRing (L : Type*) extends NonUnitalNonAssocRing L where
  assoc_def (x y z : L) : associator x y z + associator z x y + associator y z x =
  associator y x z + associator z y x + associator x z y

/-- `LieAdmissibleAlgebras` are `LieAdmissibleRings` with a compatible action by scalars in a
commutative ring. -/
@[ext]
class LieAdmissibleAlgebra (R : Type*) [CommRing R] (L : Type*) [LieAdmissibleRing L]
  extends Module R L, IsScalarTower R L L, SMulCommClass R L L where

section instances

variable {R L : Type*} [CommRing R]

section ring

/-- By definition, every `LieAdmissibleRing` yields a `LieRing` with the commutator bracket. -/
instance [LieAdmissibleRing L] : LieRing L where
  add_lie x y z := by
    simp [Ring.lie_def, mul_add, add_mul]
    abel
  lie_add x y z := by
    simp [Ring.lie_def, mul_add, add_mul]
    abel
  lie_self := by simp [Ring.lie_def]
  leibniz_lie x y z := by
    apply sub_eq_zero.mp
    simp [Ring.lie_def, mul_sub, sub_mul]
    have assoc := LieAdmissibleRing.assoc_def x y z
    apply sub_eq_zero_of_eq at assoc
    simp [associator_apply] at assoc
    grind

end ring

section algebra

/-- Every `LieAdmissibleAlgebra` is a `LieAlgebra` with the commutator bracket. -/
instance [LieAdmissibleRing L] [LieAdmissibleAlgebra R L] : LieAlgebra R L where
  lie_smul r x y := by
    simp [Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub]

end algebra

end instances

namespace LeftPreLieRing

variable {L : Type*} [LeftPreLieRing L]

/-- `LeftPreLieRings` are an example of `LieAdmissibleRings` by the commutatitvity assumption on the
associator. -/
instance : LieAdmissibleRing L where
  assoc_def x y z := by
    have assoc_xyz := LeftPreLieRing.assoc_symm' x y z
    have assoc_zxy := LeftPreLieRing.assoc_symm' z x y
    have assoc_yzx := LeftPreLieRing.assoc_symm' y z x
    grind

end LeftPreLieRing

namespace LeftPreLieAlgebra

variable {R L : Type*} [CommRing R] [LeftPreLieRing L] [LeftPreLieAlgebra R L]

instance : LieAdmissibleAlgebra R L where

end LeftPreLieAlgebra

namespace RightPreLieRing

variable {L : Type*} [RightPreLieRing L]

/-- `RightPreLieRings` are an example of `LieAdmissibleRings` by the commutatitvity assumption on
the associator. -/
instance : LieAdmissibleRing L where
  assoc_def x y z := by
    have assoc_xyz := RightPreLieRing.assoc_symm' x y z
    have assoc_zxy := RightPreLieRing.assoc_symm' z x y
    have assoc_yzx := RightPreLieRing.assoc_symm' y z x
    grind

end RightPreLieRing

namespace RightPreLieAlgebra

variable {R L : Type*} [CommRing R] [RightPreLieRing L] [RightPreLieAlgebra R L]

instance : LieAdmissibleAlgebra R L where

end RightPreLieAlgebra
