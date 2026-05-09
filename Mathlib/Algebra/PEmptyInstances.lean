/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Instances on pempty

This file collects facts about algebraic structures on the (universe-polymorphic) empty type, e.g.
that it is a semigroup.
-/

@[expose] public section


universe u

@[to_additive]
instance SemigroupPEmpty : Semigroup PEmpty.{u + 1} where
  mul x _ := by cases x
  mul_assoc x y z := by cases x
