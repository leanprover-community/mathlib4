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
import Mathlib.Algebra.GroupRingAction.Hom

/-!
# Modules over a ring, both under group action

In this file we define

*

## Implementation notes

## Tags

-/

-- MulActionHom M N N' colission!
structure SemiActionModuleHom {M R R': Type*} [Monoid M]
    [Semiring R] [MulSemiringAction M R]
      [Semiring R'] [MulSemiringAction M R']
        (h : MulSemiringActionHom M R R')
          (N N': Type*)
            [AddCommMonoid N] [Module R N] [MulAction M N] [SemiActionModule M R N]
              [AddCommMonoid N'] [Module R' N'] [MulAction M N'] [SemiActionModule M R' N']
                extends LinearMap (h : R →+* R') N N' where
  map_smul'' : ∀ (m : M) (n : N), toFun (m • n) = m • toFun n

class SemiActionModuleHomClass (F : Type*) {M R R': outParam (Type*)}
    [Monoid M]
      [Semiring R] [MulSemiringAction M R]
        [Semiring R'] [MulSemiringAction M R']
          (g : outParam (MulSemiringActionHom M R R'))
            (N N' : outParam (Type*))
              [AddCommMonoid N] [Module R N] [MulAction M N] [SemiActionModule M R N]
                [AddCommMonoid N'] [Module R' N'] [MulAction M N'] [SemiActionModule M R' N']
                  extends SemilinearMapClass F (g : R →+* R') N N', SMulHomClass F M N N' where

variable {M R R': Type*} (N N': Type*)
    [Monoid M]
      [Semiring R] [MulSemiringAction M R]
        [Semiring R'] [MulSemiringAction M R']
          (g : MulSemiringActionHom M R R')
            [AddCommMonoid N] [Module R N] [MulAction M N] [SemiActionModule M R N]
              [AddCommMonoid N'] [Module R' N'] [MulAction M N'] [SemiActionModule M R' N']

instance semiActionModuleHomClass :
    SemiActionModuleHomClass (SemiActionModuleHom g N N') g N N' where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact LinearMap.ext (congrFun h)
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smulₛₗ
  map_smul f := f.map_smul''

-- class SemilinearMapClass (F : Type*) {R S : outParam (Type*)} [Semiring R] [Semiring S]
--   (σ : outParam (R →+* S)) (M M₂ : outParam (Type*)) [AddCommMonoid M] [AddCommMonoid M₂]
--   [Module R M] [Module S M₂] extends AddHomClass F M M₂ where

-- class SMulHomClass (F : Type*) (M X Y : outParam <| Type*) [SMul M X] [SMul M Y] extends
--   FunLike F X fun _ => Y where
--   /-- The proposition that the function preserves the action. -/
--   map_smul : ∀ (f : F) (c : M) (x : X), f (c • x) = c • f x
