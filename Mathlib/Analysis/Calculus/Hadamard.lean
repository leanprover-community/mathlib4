/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hadamard's lemma
Here we prove a variant of Hadamard's lemma. In its simplest form, Hadamard's lemma states that any
smooth function `f : ℝⁿ → ℝ` with `f x = 0` can be written as `f y = ∑ i, (y i - x i) * g i y`
for a family of smooth functions `g i : ℝⁿ → ℝ`, i.e. that smooth functions behave like polynomials
in that at their zeroes linear terms can be factored out. Here we prove the result for functions
from a finite-dimensional normed space with a choice of basis to a Banach space that are Cⁿ on an
open star-convex set around `x`. We do this by providing explicit functions `hadamardFun f x (b i)`
to serve as the `g i`, characterising their smoothness and showing that `f` can be written in terms
of them.

See https://en.wikipedia.org/wiki/Hadamard%27s_lemma and https://ncatlab.org/nlab/show/Hadamard+lemma.

## Main definitions and results
* `hadamardFun f x (b i)`: the `i`th *Hadamard quotient* of `f` at `x`, i.e. the `i`th function
  appearing in Hadamard's lemma when applied to `f` at `x` for a basis `b`.
* `ContDiffOn.hadamardFun`: when `f` is Cⁿ on an open set `s` that is star-convex around `x`,
  `hadamardFun f x (b i)` is Cⁿ⁻¹ on `s`.
* `eqOn_add_sum_hadamardFun`: when `f` is at least C¹ on an open set `s` that is star-convex
  around `x`, it can be written on `s` as
  `y ↦ f x + ∑ i : ι, b.repr (y - x) i • hadamardFun f x (b i) y`.

## TODOs
* Show that if `f` is analytic, all of its Hadamard quotients are analytic too.
-/

universe u

@[expose] public section

open ContDiff

open scoped Interval

variable {E F : Type u} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- The `i`th *Hadamard quotient* of `f` at `x`, i.e. the `i`th function appearing in
Hadamard's lemma when applied to `f` at `x` for a basis `b`. -/
noncomputable def hadamardFun (f : E → F) (x b : E) : E → F :=
    fun y ↦ ∫ t in (0 : ℝ)..1, lineDeriv ℝ f (x + t • (y - x)) b

protected lemma ContDiffOn.hadamardFun {x : E} {s : Set E} (hs : IsOpen s) (hs' : StarConvex ℝ x s)
    {f : E → F} {n m : ℕ∞} (hf : ContDiffOn ℝ n f s) (hm : m + 1 ≤ n) (b : E) :
    ContDiffOn ℝ m (hadamardFun f x b) s := by
  unfold hadamardFun
  refine ContDiffOn.parametric_intervalIntegral
    (f := fun y ↦ lineDeriv ℝ f (x + y.2 • (y.1 - x)) b) hs ?_
  rw [Set.uIcc_of_le zero_le_one]
  refine .congr ?_ (fun y hy ↦ DifferentiableAt.lineDeriv_eq_fderiv <|
    (hf.differentiableOn <| by simp [le_of_add_le_right hm]).differentiableAt <|
      hs.mem_nhds <| hs'.add_smul_sub_mem hy.1 hy.2.1 hy.2.2)
  refine .mono ?_ (s := (fun y : E × ℝ ↦ x + y.2 • (y.1 - x)) ⁻¹' s)
    fun y hy ↦ hs'.add_smul_sub_mem hy.1 hy.2.1 hy.2.2
  exact (ContinuousLinearMap.apply ℝ F b).contDiff.comp_contDiffOn <|
    (hf.fderiv_of_isOpen hs <| WithTop.coe_le_coe.2 hm).comp (by fun_prop) <| s.mapsTo_preimage _

protected lemma ContDiff.hadamardFun {f : E → F} {n m : ℕ∞} (hf : ContDiff ℝ n f)
    (hm : m + 1 ≤ n) (x b : E) : ContDiff ℝ m (hadamardFun f x b) :=
  contDiffOn_univ.1 <| (contDiffOn_univ.2 hf).hadamardFun isOpen_univ (starConvex_univ x) hm b

variable [CompleteSpace F]

open intervalIntegral in
lemma eqOn_add_sum_hadamardFun {x : E} {s : Set E} (hs : IsOpen s) (hs' : StarConvex ℝ x s)
    {f : E → F} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s) (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) :
    s.EqOn f (fun y ↦ f x + ∑ i : ι, b.repr (y - x) i • hadamardFun f x (b i) y) := by
  intro y hy
  have hs'' : ∀ t ∈ Set.uIcc (0 : ℝ) 1, x + t • (y - x) ∈ s := fun t ht ↦ by
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hs'.add_smul_sub_mem hy ht.1 ht.2
  refine sub_eq_iff_eq_add'.1 <| Eq.trans (by simp) <| (integral_deriv_eq_sub
    (a := 0) (b := 1) (f := f ∘ fun t ↦ x + t • (y - x)) ?_ ?_).symm.trans ?_
  · intro t ht
    have := (hf.differentiableOn hn).differentiableAt <| hs.mem_nhds <| hs'' _ ht
    fun_prop
  · refine ContinuousOn.intervalIntegrable ?_
    exact ((hf.comp (by fun_prop) <| s.mapsTo_preimage _).continuousOn_deriv_of_isOpen
      (hs.preimage <| by fun_prop) hn).mono fun t ht ↦ hs'' _ ht
  · unfold hadamardFun
    simp_rw [← integral_smul]
    rw [← integral_finset_sum]
    · refine integral_congr fun t ht ↦ ?_
      rw [← fderiv_deriv, fderiv_comp]
      · simp_rw [DifferentiableAt.lineDeriv_eq_fderiv <|
          (hf.differentiableOn hn).differentiableAt <| hs.mem_nhds <| hs'' _ ht]
        simp_rw [← ContinuousLinearMap.map_smul, ← map_sum]
        simp [deriv_smul_const, - map_sub]
      · refine (hf.differentiableOn hn).differentiableAt <| hs.mem_nhds <| hs'' _ ht
      · simp
    · intro i _
      refine (continuousOn_const.smul ?_).intervalIntegrable
      refine .congr ?_ (fun t ht ↦ DifferentiableAt.lineDeriv_eq_fderiv <|
          (hf.differentiableOn hn).differentiableAt <| hs.mem_nhds <| hs'' _ ht)
      refine .mono ?_  (s := (fun t ↦ x + t • (y - x)) ⁻¹' s) fun t ht ↦ hs'' _ ht
      exact (ContinuousLinearMap.apply ℝ F _).continuous.comp_continuousOn <|
        (hf.continuousOn_fderiv_of_isOpen hs hn).comp (by fun_prop) <| s.mapsTo_preimage _

lemma eq_add_sum_hadamardFun {x : E} {f : E → F} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hn : 1 ≤ n) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) :
    f = (fun y ↦ f x + ∑ i : ι, b.repr (y - x) i • hadamardFun f x (b i) y) := by
  simpa using eqOn_add_sum_hadamardFun isOpen_univ (starConvex_univ x) hf.contDiffOn hn b
