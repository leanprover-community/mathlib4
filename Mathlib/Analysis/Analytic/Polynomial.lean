/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Polynomials are analytic

This file combines the analysis and algebra libraries and shows that evaluation of a polynomial
is an analytic function.
-/
set_option backward.defeqAttrib.useBackward true

public section

variable {𝕜 E A B : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CommSemiring A] {z : E} {s : Set E}

section Polynomial
open Polynomial

variable [NormedRing B] [NormedAlgebra 𝕜 B] [Algebra A B] {f : E → B}

theorem AnalyticWithinAt.aeval_polynomial (hf : AnalyticWithinAt 𝕜 f s z) (p : A[X]) :
    AnalyticWithinAt 𝕜 (fun x ↦ aeval (f x) p) s z := by
  refine p.induction_on (fun k ↦ ?_) (fun p q hp hq ↦ ?_) fun p i hp ↦ ?_
  · simp_rw [aeval_C]; apply analyticWithinAt_const
  · simp_rw [aeval_add]; exact hp.add hq
  · convert hp.mul hf
    simp_rw [pow_succ, aeval_mul, ← mul_assoc, aeval_X]

theorem AnalyticAt.aeval_polynomial (hf : AnalyticAt 𝕜 f z) (p : A[X]) :
    AnalyticAt 𝕜 (fun x ↦ aeval (f x) p) z := by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.aeval_polynomial p

theorem AnalyticOnNhd.aeval_polynomial (hf : AnalyticOnNhd 𝕜 f s) (p : A[X]) :
    AnalyticOnNhd 𝕜 (fun x ↦ aeval (f x) p) s := fun x hx ↦ (hf x hx).aeval_polynomial p

theorem AnalyticOn.aeval_polynomial (hf : AnalyticOn 𝕜 f s) (p : A[X]) :
    AnalyticOn 𝕜 (fun x ↦ aeval (f x) p) s := fun x hx ↦ (hf x hx).aeval_polynomial p

theorem AnalyticOnNhd.eval_polynomial {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X]) :
    AnalyticOnNhd 𝕜 (eval · p) Set.univ := analyticOnNhd_id.aeval_polynomial p

theorem AnalyticOn.eval_polynomial {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X]) :
    AnalyticOn 𝕜 (eval · p) Set.univ := analyticOn_id.aeval_polynomial p

end Polynomial

section MvPolynomial
open MvPolynomial

variable [NormedCommRing B] [NormedAlgebra 𝕜 B] [Algebra A B] {σ : Type*} {f : E → σ → B}

theorem AnalyticAt.aeval_mvPolynomial (hf : ∀ i, AnalyticAt 𝕜 (f · i) z) (p : MvPolynomial σ A) :
    AnalyticAt 𝕜 (fun x ↦ aeval (f x) p) z := by
  apply p.induction_on (fun k ↦ ?_) (fun p q hp hq ↦ ?_) fun p i hp ↦ ?_ -- `refine` doesn't work
  · simp_rw [aeval_C]; apply analyticAt_const
  · simp_rw [map_add]; exact hp.add hq
  · simp_rw [map_mul, aeval_X]; exact hp.mul (hf i)

theorem AnalyticOnNhd.aeval_mvPolynomial
    (hf : ∀ i, AnalyticOnNhd 𝕜 (f · i) s) (p : MvPolynomial σ A) :
    AnalyticOnNhd 𝕜 (fun x ↦ aeval (f x) p) s := fun x hx ↦ .aeval_mvPolynomial (hf · x hx) p

theorem AnalyticOnNhd.eval_continuousLinearMap (f : E →L[𝕜] σ → B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x ↦ eval (f x) p) Set.univ :=
  fun x _ ↦ .aeval_mvPolynomial (fun i ↦ ((ContinuousLinearMap.proj i).comp f).analyticAt x) p

theorem AnalyticOnNhd.eval_continuousLinearMap' (f : σ → E →L[𝕜] B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x ↦ eval (f · x) p) Set.univ :=
  fun x _ ↦ .aeval_mvPolynomial (fun i ↦ (f i).analyticAt x) p

variable [CompleteSpace 𝕜] [T2Space E] [FiniteDimensional 𝕜 E]

theorem AnalyticOnNhd.eval_linearMap (f : E →ₗ[𝕜] σ → B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x ↦ eval (f x) p) Set.univ :=
  AnalyticOnNhd.eval_continuousLinearMap { f with cont := f.continuous_of_finiteDimensional } p

theorem AnalyticOnNhd.eval_linearMap' (f : σ → E →ₗ[𝕜] B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x ↦ eval (f · x) p) Set.univ := AnalyticOnNhd.eval_linearMap (.pi f) p

theorem AnalyticOnNhd.eval_mvPolynomial [Fintype σ] (p : MvPolynomial σ 𝕜) :
    AnalyticOnNhd 𝕜 (eval · p) Set.univ :=
  AnalyticOnNhd.eval_linearMap (.id (R := 𝕜) (M := σ → 𝕜)) p

end MvPolynomial
