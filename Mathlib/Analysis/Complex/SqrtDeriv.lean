/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Derivatives of `Complex.sqrt`

This file proves that `Complex.sqrt` is differentiable on the slit plane
`Complex.slitPlane` and computes its derivative.

## Main results

* `Complex.hasDerivAt_sqrt`: the derivative of `Complex.sqrt` at `z ∈ slitPlane`
  is `z ^ (-1 / 2 : ℂ) / 2`.
* `Complex.differentiableOn_sqrt`: `Complex.sqrt` is differentiable on `slitPlane`.
* `Complex.deriv_sqrt`: the derivative equals `z ^ (-1 / 2 : ℂ) / 2`.
-/

@[expose] public section

namespace Complex

lemma hasStrictDerivAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) :
    HasStrictDerivAt sqrt (z ^ (-1 / 2 : ℂ) / 2) z := by
  exact (Complex.hasStrictDerivAt_cpow_const (c := 2⁻¹) hz).congr_deriv (by
    rw [show (2 : ℂ)⁻¹ - 1 = -1 / 2 by norm_num, mul_comm, ← div_eq_mul_inv])

lemma hasDerivAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt sqrt (z ^ (-1 / 2 : ℂ) / 2) z :=
  (hasStrictDerivAt_sqrt hz).hasDerivAt

lemma hasDerivWithinAt_sqrt {z : ℂ} {s : Set ℂ} (hz : z ∈ slitPlane) :
    HasDerivWithinAt sqrt (z ^ (-1 / 2 : ℂ) / 2) s z :=
  (hasDerivAt_sqrt hz).hasDerivWithinAt

@[fun_prop]
lemma differentiableAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ sqrt z :=
  (hasDerivAt_sqrt hz).differentiableAt

@[fun_prop]
lemma differentiableWithinAt_sqrt {z : ℂ} {s : Set ℂ} (hz : z ∈ slitPlane) :
    DifferentiableWithinAt ℂ sqrt s z :=
  (differentiableAt_sqrt hz).differentiableWithinAt

@[fun_prop]
lemma differentiableOn_sqrt : DifferentiableOn ℂ sqrt slitPlane :=
  fun _ hz => (differentiableAt_sqrt hz).differentiableWithinAt

lemma deriv_sqrt {z : ℂ} (hz : z ∈ slitPlane) : deriv sqrt z = z ^ (-1 / 2 : ℂ) / 2 :=
  (hasDerivAt_sqrt hz).deriv

lemma derivWithin_sqrt {z : ℂ} (hz : z ∈ slitPlane) :
    derivWithin sqrt slitPlane z = z ^ (-1 / 2 : ℂ) / 2 :=
  (hasDerivWithinAt_sqrt hz).derivWithin (isOpen_slitPlane.uniqueDiffWithinAt hz)

/-- `Complex.sqrt` is continuous at `z` provided `0 ≤ z.re` or `z.im ≠ 0`. This is weaker than
requiring `z ∈ slitPlane`, as it additionally includes the imaginary axis and `0`. -/
lemma continuousAt_sqrt {z : ℂ} (hz : 0 ≤ z.re ∨ z.im ≠ 0) : ContinuousAt sqrt z :=
  continuousAt_cpow_const_of_re_pos hz (by norm_num)

lemma continuousOn_sqrt : ContinuousOn sqrt slitPlane :=
  fun _ hz => (continuousAt_sqrt (hz.imp le_of_lt id)).continuousWithinAt

end Complex
