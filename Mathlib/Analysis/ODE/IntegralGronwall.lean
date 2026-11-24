/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# The integral Grönwall inequality

We prove the constant coefficient inequality for an interval integrable real function. The
integrating factor is applied to the absolutely continuous integral upper bound, so the original
function does not have to be continuous or bounded.
-/

@[expose] public section

open MeasureTheory Set

namespace intervalIntegral

/-- Integral Grönwall inequality with a nonnegative constant coefficient. -/
theorem le_mul_exp_of_le_add_mul_integral {u : ℝ → ℝ} {a b A C : ℝ}
    (hC : 0 ≤ C) (hu : IntervalIntegrable u volume a b)
    (h : ∀ x ∈ Icc a b, u x ≤ A + C * ∫ s in a..x, u s) :
    ∀ t ∈ Icc a b, u t ≤ A * Real.exp (C * (t - a)) := by
  intro t ht
  have hut : IntervalIntegrable u volume a t := hu.mono_set <| by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc_right ht.2
  let v (x : ℝ) := A + C * ∫ s in a..x, u s
  let p (x : ℝ) := Real.exp (-C * (x - a))
  let w (x : ℝ) := p x * v x
  have hI : AbsolutelyContinuousOnInterval (fun x ↦ ∫ s in a..x, u s) a t :=
    hut.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hA : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ A) a t := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hv : AbsolutelyContinuousOnInterval v a t := hA.add (hI.const_mul C)
  have hp : AbsolutelyContinuousOnInterval p a t := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    dsimp only [p]
    fun_prop
  have hw : AbsolutelyContinuousOnInterval w a t := hp.mul hv
  have hderiv : ∀ᵐ x ∂volume.restrict (Ioc a t), deriv w x ≤ 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hut.ae_hasDerivAt_integral] with x hx hxmem
    have hxt : x ∈ uIcc a t := by
      rw [uIcc_of_le ht.1]
      exact ⟨hxmem.1.le, hxmem.2⟩
    have hxb : x ∈ Icc a b := ⟨hxmem.1.le, hxmem.2.trans ht.2⟩
    have hinner : HasDerivAt (fun y : ℝ ↦ -C * (y - a)) (-C) x := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id x).sub_const a).const_mul (-C)
    have hp' : HasDerivAt p ((-C) * p x) x := by
      simpa only [p, Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (-C * (x - a))).comp x hinner
    have hv' : HasDerivAt v (C * u x) x :=
      ((hx hxt a (by simp)).const_mul C).const_add A
    change deriv (p * v) x ≤ 0
    rw [(hp'.mul hv').deriv]
    calc
      _ = (C * p x) * (u x - v x) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC (Real.exp_nonneg _))
        (sub_nonpos.mpr (h x hxb))
  have hw_le : w t ≤ w a := by
    apply sub_nonpos.mp
    rw [← hw.integral_deriv_eq_sub, integral_of_le ht.1]
    exact integral_nonpos_of_ae hderiv
  have hwA : w t ≤ A := by simpa [w, p, v] using hw_le
  calc
    u t ≤ v t := h t ht
    _ = Real.exp (C * (t - a)) * w t := by
      simp [w, p, neg_mul, Real.exp_neg, Real.exp_ne_zero]
    _ ≤ Real.exp (C * (t - a)) * A := mul_le_mul_of_nonneg_left hwA (Real.exp_nonneg _)
    _ = A * Real.exp (C * (t - a)) := mul_comm _ _

end intervalIntegral
