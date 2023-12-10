/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.ToAdditive

#align_import algebra.pempty_instances from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

/-!
# Instances on pempty

This file collects facts about algebraic structures on the (universe-polymorphic) empty type, e.g.
that it is a semigroup.
-/


universe u

@[to_additive]
instance SemigroupPEmpty : Semigroup PEmpty.{u + 1} where
  mul x _ := by cases x
  mul_assoc x y z := by cases x
#align semigroup_pempty SemigroupPEmpty
#align add_semigroup_pempty AddSemigroupPEmpty
