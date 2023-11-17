/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Adomas Baliuka, Moritz Doll
-/
import Mathlib.Tactic.Differentiability
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Series
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.NumberTheory.ZetaFunction

import Mathlib.Util.Time

-- TODO note uncommenting all of them makes the following lemma fail!
attribute [differentiabilitySBE]
-- concrete functions
    differentiable_id
    differentiable_id'
    differentiable_const
    differentiable_fst
    differentiable_snd
    Differentiable.fst
    Differentiable.snd
    Differentiable.prod
    Differentiable.restrictScalars
    differentiable_neg
    differentiable_tsum--TODO can use?
    Differentiable.sqrt
    Differentiable.norm_sq
    Differentiable.norm
    Differentiable.exp
    Differentiable.cexp
    Differentiable.zpow
    Differentiable.clog
    Differentiable.log--TODO can this be used?
    Differentiable.ccos
    Differentiable.ccosh
    Differentiable.cos
    Differentiable.cosh
    Differentiable.csin
    Differentiable.csinh
    Differentiable.sin-----------------------------------todo
    Differentiable.sinh
    Differentiable.dist
    differentiable_inner
    Differentiable.inner
    Differentiable.arsinh
    Differentiable.arctan
    Real.differentiable_exp
    Real.differentiable_cos
    Real.differentiable_cosh
    Real.differentiable_sin
    Real.differentiable_sinh
    Real.differentiable_arctan
    Real.differentiable_arsinh
    Complex.differentiable_exp
    Complex.differentiable_cos
    Complex.differentiable_cosh
    Complex.differentiable_sin
    Complex.differentiable_sinh
    Complex.differentiable_one_div_Gamma
    differentiable_circleMap
-- more general operations (better to match concrete function, therefore try later)
    Differentiable.const_smul
    Differentiable.div_const
    Differentiable.const_sub
    Differentiable.sub_const
    Differentiable.add_const
    Differentiable.const_add
    Real.differentiable_rpow_const
    Differentiable.rpow_const
    Differentiable.const_mul
    Differentiable.mul_const
    Differentiable.smul_const
    Differentiable.inv-- TODO can this be used?
    Differentiable.div
    differentiable_pow
    Differentiable.inverse
    Differentiable.mul
    Differentiable.inv'
    Differentiable.pow
    Differentiable.neg
    Differentiable.sum
    Differentiable.sub
    Differentiable.add
    Differentiable.rpow
    Differentiable.smul
    Differentiable.star
    Differentiable.iterate
    Differentiable.comp
-- infer from other property. Better match operation therefore try later.
    HasFTaylorSeriesUpTo.differentiable
    LinearIsometryEquiv.differentiable
    AffineMap.differentiable
    MDifferentiable.differentiable
    SchwartzMap.differentiable
    differentiable_completed_zeta₀
    differentiable_mellin_zetaKernel₂
    Differentiable.inversion
    IsBoundedBilinearMap.differentiable
    IsBoundedLinearMap.differentiable
    ContinuousLinearMap.differentiable
    Differentiable.clm_apply
    Differentiable.clm_comp
    ContinuousLinearEquiv.differentiable
    expNegInvGlue.differentiable_polynomial_eval_inv_mul
    Polynomial.differentiable
    Polynomial.differentiable_aeval
    ContDiff.differentiable_iteratedDeriv
    Conformal.differentiable
    ContDiff.differentiable
    ContDiff.differentiable_iteratedFDeriv

section RealExamplesAndTests

open Real

set_option trace.Meta.Tactic.solveByElim true


#time example : Differentiable ℝ (fun (x : ℝ) ↦ x) := by
    solve_by_elim (config:={maxDepth:=10}) using differentiabilitySBE

set_option maxHeartbeats 10000000 in
#time example : Differentiable ℝ (fun (x : ℝ) ↦ sin x) := by
    solve_by_elim (config:={maxDepth:=10}) using differentiabilitySBE

#time example : Differentiable ℝ (fun (x : ℝ) ↦ exp x) := by
    solve_by_elim (config:={maxDepth:=10}) using differentiabilitySBE

#time example : Differentiable ℝ (fun (x : ℝ) ↦ exp x + sin x) := by
    solve_by_elim (config:={maxDepth:=10}) using differentiabilitySBE


#time example : Differentiable ℝ (fun x ↦ x * 999 * cosh x + 3) := by
-- this would just work:
    -- apply Differentiable.add_const
    -- apply Differentiable.mul
    -- apply Differentiable.mul_const
    -- apply differentiable_id'
    -- apply differentiable_cosh
-- try automation.
    -- solve_by_elim (config:={maxDepth:=10}) using differentiabilitySBE
-- this says:    [] ❌ trying to apply: @Differentiable.mul
-- which doesn't make sense, because applying that lemma works above.

-- and this does work after all:
    solve_by_elim [Differentiable.add_const,
        Differentiable.mul,
        Differentiable.mul_const,
        differentiable_id',
        differentiable_cosh]


#time example : Differentiable ℝ (fun x ↦ ( sin (sin x))) := by
    solve_by_elim (config:={maxDepth:=10}) using differentiabilitySBE

-- this is way faster but need to spell out lemmas
#time example : Differentiable ℝ (fun x ↦ ( sin (sin x))) := by
    solve_by_elim (config:={maxDepth:=10}) [
        Differentiable.sin, differentiable_id, differentiable_id'
        ]


-- ISSUE TODO:
-- apparantly, this solves a subgoal and then doesn't go back to the start of the list of tactics?
-- concretely, applies `Differentiable.mul` and never tries it again in subgoals
#time example : Differentiable ℝ (fun (x : ℝ) ↦
(sin x * exp x + 3) * 999 * (cosh (cos x)))
:= by
    solve_by_elim (config:={maxDepth:=10}) using differentiabilitySBE


section ComplexExamplesAndTestsdifferentiabilitySBE

open Complex

-- fails to apply `@Differentiable.mul` but this *should* apply!
example : Differentiable ℂ (fun (x : ℂ) ↦
(sin x * exp x + 3) * 999 * (cosh (cos x)))
:= by
    -- solve_by_elim (config:={maxDepth:=10}) using differentiabilitySBE
    apply @Differentiable.mul
    sorry
