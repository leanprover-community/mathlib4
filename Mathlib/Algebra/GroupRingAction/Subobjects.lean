/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.group_ring_action.subobjects
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Instances of `mul_semiring_action` for subobjects

These are defined in this file as `semiring`s are not available yet where `submonoid` and `subgroup`
are defined.

Instances for `subsemiring` and `subring` are provided next to the other scalar actions instances
for those subobjects.

-/


variable {M G R : Type _}

variable [Monoid M] [Group G] [Semiring R]

/-- A stronger version of `submonoid.distrib_mul_action`. -/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) :
    MulSemiringAction H R :=
  { H.MulDistribMulAction, H.DistribMulAction with smul := (· • ·) }
#align submonoid.mul_semiring_action Submonoid.mulSemiringAction

/-- A stronger version of `subgroup.distrib_mul_action`. -/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) :
    MulSemiringAction H R :=
  H.toSubmonoid.MulSemiringAction
#align subgroup.mul_semiring_action Subgroup.mulSemiringAction

