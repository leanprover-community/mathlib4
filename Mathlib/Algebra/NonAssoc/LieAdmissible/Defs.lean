/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.NonAssoc.PreLie.Basic
public import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike
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
  * `LieAdmissibleRing.instLieRing`: a Lie-admissible ring as a Lie ring
  * `LeftPreLieRing.instLieAdmissibleRing`: a left pre-Lie ring as a Lie admissible ring
  * `RightPreLieRing.instLieAdmissibleRing`: a right pre-Lie ring as a Lie admissible ring
  * `LieAdmissibleAlgebra.instLieAlgebra`: a Lie-admissible algebra as a Lie algebra
  * `LeftPreLieAlgebra.instLieAdmissibleAlgebra`: a left pre-Lie ring as a Lie admissible algebra
  * `RightPreLieAlgebra.instLieAdmissibleAlgebra`: a right pre-Lie ring as a Lie admissible algebra

## Implementation Notes
Algebras are implemented as extending `Module`, `IsScalarTower` and `SMulCommClass` following the
documentation of `Algebra`.

## References
[Munthe-Kaas, H.Z., Lundervold, A. **On Post-Lie Algebras, Lie–Butcher Series and Moving
Frames.**][munthe-kaas_lundervold_2013]
-/

@[expose] public section

/-- A `LieAdmissibleRing` is a `NonUnitalNonAssocRing` such that the canonical bracket
`⁅x, y⁆ := x * y - y * x` turns it into a `LieRing`. This is expressed by an associator identity. -/
@[ext]
class LieAdmissibleRing (L : Type*) extends NonUnitalNonAssocRing L where
  assoc_def (x y z : L) : associator x y z + associator z x y + associator y z x =
    associator y x z + associator z y x + associator x z y

/-- A `LieAdmissibleAlgebra` is a `LieAdmissibleRing` equipped with a compatible action by scalars
from a commutative ring. -/
@[ext]
class LieAdmissibleAlgebra (R L : Type*) [CommRing R] [LieAdmissibleRing L]
  extends Module R L, IsScalarTower R L L, SMulCommClass R L L

section instances

variable {R L : Type*} [CommRing R]

namespace LieAdmissibleRing

/-- By definition, every `LieAdmissibleRing` yields a `LieRing` with the commutator bracket. -/
instance instLieRing [LieAdmissibleRing L] : LieRing L where
  add_lie x y z := by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  lie_add x y z := by
    simp only [Ring.lie_def, mul_add, add_mul]
    abel
  lie_self := by simp [Ring.lie_def]
  leibniz_lie x y z := by
    have := LieAdmissibleRing.assoc_def x y z
    simp only [associator_apply] at this
    grind [Ring.lie_def, mul_sub, sub_mul]

end LieAdmissibleRing

namespace LieAdmissibleAlgebra

/-- Every `LieAdmissibleAlgebra` is a `LieAlgebra` with the commutator bracket. -/
instance instLieAlgebra [LieAdmissibleRing L] [LieAdmissibleAlgebra R L] : LieAlgebra R L where
  lie_smul r x y := by
    simp [Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub]

end LieAdmissibleAlgebra

end instances

namespace LeftPreLieRing

variable {L : Type*} [LeftPreLieRing L]

/-- `LeftPreLieRings` are examples of `LieAdmissibleRings` by the commutativity assumption on the
associator. -/
instance instLieAdmissibleRing : LieAdmissibleRing L where
  assoc_def x y z := by
    have assoc_xyz := LeftPreLieRing.assoc_symm' x y z
    have assoc_zxy := LeftPreLieRing.assoc_symm' z x y
    have assoc_yzx := LeftPreLieRing.assoc_symm' y z x
    grind

end LeftPreLieRing

namespace LeftPreLieAlgebra

variable {R L : Type*} [CommRing R] [LeftPreLieRing L] [LeftPreLieAlgebra R L]

instance instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where

end LeftPreLieAlgebra

namespace RightPreLieRing

variable {L : Type*} [RightPreLieRing L]

/-- `RightPreLieRings` are examples of `LieAdmissibleRings` by the commutativity assumption on
the associator. -/
instance instLieAdmissibleRing : LieAdmissibleRing L where
  assoc_def x y z := by
    have assoc_xyz := RightPreLieRing.assoc_symm' x y z
    have assoc_zxy := RightPreLieRing.assoc_symm' z x y
    have assoc_yzx := RightPreLieRing.assoc_symm' y z x
    grind

end RightPreLieRing

namespace RightPreLieAlgebra

variable {R L : Type*} [CommRing R] [RightPreLieRing L] [RightPreLieAlgebra R L]

instance instLieAdmissibleAlgebra : LieAdmissibleAlgebra R L where

end RightPreLieAlgebra
