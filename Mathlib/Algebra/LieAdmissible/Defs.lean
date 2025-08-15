/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.PreLie.Basic
import Mathlib.Tactic
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
universe u v

@[ext]
class LieAdmissibleRing (L : Type u) : Type (u + 1) extends NonUnitalNonAssocRing L where
  assoc_def (x y z : L) : associator x y z + associator z x y + associator y z x =
  associator y x z + associator z y x + associator x z y

@[ext]
class LieAdmissibleAlgebra (R : Type u) [CommRing R] (L : Type v) [LieAdmissibleRing L] :
    Type (max u v) extends Module R L, IsScalarTower R L L, SMulCommClass R L L where

section instances
variable {R : Type u} [CommRing R]
section ring
variable {L : Type v} [LieAdmissibleRing L]

instance : LieRing L where
  add_lie x y z := by
    simp [Ring.lie_def]
    noncomm_ring
  lie_add x y z := by
    simp [Ring.lie_def]
    noncomm_ring
  lie_self := by simp [Ring.lie_def]
  leibniz_lie x y z := by
    have assoc := LieAdmissibleRing.assoc_def x y z
    apply sub_eq_zero.mp
    apply sub_eq_zero_of_eq at assoc
    simp [associator_apply] at assoc
    simp [Ring.lie_def]
    noncomm_ring; simp;
    abel_nf at assoc; simp at assoc;
    grind
end ring

section algebra
variable {L : Type v} [LieAdmissibleRing L] [LieAdmissibleAlgebra R L]
instance : LieAlgebra R L where
  lie_smul r x y := by
    simp [Ring.lie_def]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
end algebra
end instances

namespace LeftPreLieRing
variable {L : Type u} [LeftPreLieRing L]
instance : LieAdmissibleRing L where
  assoc_def x y z := by
    have assoc_xyz := LeftPreLieRing.assoc_symm' x y z
    have assoc_zxy := LeftPreLieRing.assoc_symm' z x y
    have assoc_yzx := LeftPreLieRing.assoc_symm' y z x
    grind
end LeftPreLieRing

namespace LeftPreLieAlgebra
variable {R : Type u} [CommRing R]
variable {L : Type v} [LeftPreLieRing L] [LeftPreLieAlgebra R L]
instance : LieAdmissibleAlgebra R L where
end LeftPreLieAlgebra

namespace RightPreLieRing
variable {L : Type u} [RightPreLieRing L]
instance : LieAdmissibleRing L where
  assoc_def x y z := by
    have assoc_xyz := RightPreLieRing.assoc_symm' x y z
    have assoc_zxy := RightPreLieRing.assoc_symm' z x y
    have assoc_yzx := RightPreLieRing.assoc_symm' y z x
    grind
end RightPreLieRing

namespace RightPreLieAlgebra
variable {R : Type u} [CommRing R]
variable {L : Type v} [RightPreLieRing L] [RightPreLieAlgebra R L]
instance : LieAdmissibleAlgebra R L where
end RightPreLieAlgebra

-- vim:tw=100
