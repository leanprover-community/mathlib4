/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Negation on spheres and balls

In this file we define `InvolutiveNeg` and `ContinuousNeg` instances for spheres, open balls, and
closed balls in a seminormed group.
-/

@[expose] public section

open Metric Set Topology

variable {E : Type*} [i : SeminormedAddCommGroup E] {r : ℝ}

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance : InvolutiveNeg (sphere (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1

@[simp]
theorem coe_neg_sphere {r : ℝ} (v : sphere (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl

instance : ContinuousNeg (sphere (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl

/-- We equip the ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : InvolutiveNeg (ball (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1

@[simp] theorem coe_neg_ball {r : ℝ} (v : ball (0 : E) r) : ↑(-v) = (-v : E) := rfl

instance : ContinuousNeg (ball (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl

/-- We equip the closed ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : InvolutiveNeg (closedBall (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1

@[simp] theorem coe_neg_closedBall {r : ℝ} (v : closedBall (0 : E) r) : ↑(-v) = (-v : E) := rfl

instance : ContinuousNeg (closedBall (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl
