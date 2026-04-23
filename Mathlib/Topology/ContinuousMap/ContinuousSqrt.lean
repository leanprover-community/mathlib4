/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.StarOrdered
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.StarOrdered
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-! # Instances of `ContinuousSqrt`

This provides the instances of `ContinuousSqrt` for `ℝ`, `ℝ≥0`, and `ℂ`, thereby yielding instances
of `StarOrderedRing C(α, R)` and `StarOrderedRing C(α, R)₀` for any topological space `α` and `R`
among `ℝ≥0`, `ℝ`, and `ℂ`. -/

@[expose] public section

open scoped NNReal

open scoped ComplexOrder in
open RCLike in
noncomputable
instance (priority := 100) instContinuousSqrtRCLike {𝕜 : Type*} [RCLike 𝕜] :
    ContinuousSqrt 𝕜 where
  sqrt := ((↑) ∘ (√·) ∘ re ∘ (fun z ↦ z.2 - z.1))
  continuousOn_sqrt := by fun_prop
  sqrt_nonneg _ _ := by simp
  sqrt_mul_sqrt x hx := by
    simp only [Function.comp_apply]
    rw [← sub_nonneg] at hx
    obtain hx' := nonneg_iff.mp hx |>.right
    rw [← conj_eq_iff_im, conj_eq_iff_re] at hx'
    rw [← ofReal_mul, Real.mul_self_sqrt, hx', add_sub_cancel]
    simpa using nonneg_iff.mp hx |>.left

noncomputable instance : ContinuousSqrt ℝ := instContinuousSqrtRCLike (𝕜 := ℝ)

open ComplexOrder in
noncomputable instance : ContinuousSqrt ℂ := instContinuousSqrtRCLike (𝕜 := ℂ)

noncomputable instance : ContinuousSqrt ℝ≥0 where
  sqrt := NNReal.sqrt ∘ (fun x ↦ x.2 - x.1)
  continuousOn_sqrt := by fun_prop
  sqrt_nonneg := by simp
  sqrt_mul_sqrt := by simpa using fun _ _ h ↦ Eq.symm <| add_tsub_cancel_of_le h
