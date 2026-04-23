/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Poisson Integral Formula

This file establishes several versions of the **Poisson Integral Formula** for harmonic functions on
arbitrary disks in the complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration and with the Poisson kernel, respectively.

TODO: Extend this formula to vector-valued harmonic functions
-/

public section

open Complex InnerProductSpace Metric Real Topology

variable
  {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}

namespace InnerProductSpace

private lemma continuousOn_herglotz_riesz (_ : w ∈ ball c R) :
    ContinuousOn (fun x ↦ ((x - c + (w - c)) / (x - c - (w - c))).re)
      {z | ‖z - c‖ ∈ Set.Ioc ‖w - c‖ R} := by
  have : ∀ x ∈ {z | ‖z - c‖ ∈ Set.Ioc ‖w - c‖ R}, x - c - (w - c) ≠ 0 := by
    grind [mem_ball, mem_sphere]
  fun_prop (disch := assumption)

set_option backward.isDefEq.respectTransparency false in
/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the complex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration.
-/
theorem HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c R).exists_thickening_subset_open
    (isOpen_setOf_harmonicAt f) (by aesop)
  rw [thickening_closedBall h₁e (pos_of_mem_ball hw).le] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : DifferentiableOn ℂ F (closure (ball c R)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn (re ∘ herglotzRieszKernel c w • f)
      (reCLM ∘ (fun z ↦ ((z - c + (w - c)) / (z - c - (w - c))).re • F z))
      (sphere c R) := by
    intro x hx
    simp [h₂F (sphere_subset_ball (lt_add_of_pos_left R h₁e) hx), herglotzRieszKernel_def]
  rw [← abs_of_pos (pos_of_mem_ball hw)] at h₄F
  rw [circleAverage_congr_sphere h₄F, reCLM.circleAverage_comp_comm,
    h₃F.diffContOnCl.circleAverage_re_herglotzRieszKernel_smul' hw]
  · apply h₂F
    grind [mem_ball]
  -- CircleIntegrable (fun z ↦ ((z - c + (w - c)) / (z - c - (w - c))).re • F z) c R
  apply (ContinuousOn.smul _ _).circleIntegrable'
  · apply (continuousOn_herglotz_riesz hw).mono
    grind [mem_ball, dist_eq_norm, mem_sphere_iff_norm, (pos_of_mem_ball hw)]
  · apply (h₁F.mono _).continuousOn (𝕜 := ℂ)
    grind [mem_sphere, mem_ball, (pos_of_mem_ball hw)]

/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the complex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration.
-/
theorem HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  apply ContinuousOn.eq_of_eqOn_Ioo (r := ‖w - c‖)
  · apply ContinuousOn.circleAverage
    · rw [herglotzRieszKernel_fun_def]
      apply (continuousOn_herglotz_riesz hw).smul (hf.2.mono _)
      grind [closure_ball c (pos_of_mem_ball hw).ne', mem_closedBall_iff_norm]
    · grind [norm_nonneg (w - c)]
  · grind [mem_ball_iff_norm]
  · intro r hr
    rw [HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
      (hf.1.mono (closedBall_subset_ball hr.2)) (by grind [mem_ball_iff_norm])]

/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the complex plane,
formulated with the Poisson kernel of integration.
-/
theorem HarmonicOnNhd.circleAverage_poissonKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ ↦ by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

/--
**Poisson integral formula** for harmonic functions on arbitrary disks in the complex plane,
formulated with the Poisson kernel of integration.
-/
theorem HarmonicContOnCl.circleAverage_poissonKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ ↦ by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

end InnerProductSpace
