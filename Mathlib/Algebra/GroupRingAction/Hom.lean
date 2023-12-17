/-
Copyright (c) 2023 Qi Ge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Ge
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.GroupActionRingModule.Basic

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `MulSemiringAction M R`,
and the corresponding typeclass of invariant subrings.

Note that `Algebra` does not satisfy the axioms of `MulSemiringAction`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `MulSemiringAction`.

## Tags

group action, invariant subring

-/universe u v

/-- Typeclass for multiplicative actions by monoids on semirings.

-- This combines `DistribMulAction` with `MulDistribMulAction`. -/
class MulSemiringActionHom'
    {M N : Type*} [Monoid M] [Monoid N]
      (σ : M →* N)
        (R S : Type*) [Semiring R] [Semiring S]
          [MulSemiringAction M R] [MulSemiringAction N S]
            extends R →+* S where
  /-- A linear map preserves scalar multiplication.
  We prefer the spelling `_root_.map_smul` instead. -/
  protected map_smul' : ∀ (m : M) (r : R), toFun (m • r) = σ m • toFun r
