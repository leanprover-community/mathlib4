/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.DistribMulAction
import Mathlib.Algebra.Ring.Action.Basic

/-!
# Instances of `MulSemiringAction` for subobjects

These are defined in this file as `Semiring`s are not available yet where `Submonoid` and `Subgroup`
are defined.

Instances for `Subsemiring` and `Subring` are provided next to the other scalar actions instances
for those subobjects.

-/


variable {M G R : Type*}
variable [Monoid M] [Group G] [Semiring R]

/-- A stronger version of `Submonoid.distribMulAction`. -/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) :
    MulSemiringAction H R :=
  { inferInstanceAs (DistribMulAction H R), inferInstanceAs (MulDistribMulAction H R) with }

/-- A stronger version of `Subgroup.distribMulAction`. -/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) :
    MulSemiringAction H R :=
  H.toSubmonoid.mulSemiringAction
