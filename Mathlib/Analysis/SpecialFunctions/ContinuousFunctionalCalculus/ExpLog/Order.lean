/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Order properties of the operator logarithm

This file shows that the logarithm is operator monotone, i.e. that `CFC.log` is monotone on
the strictly positive elements of a unital C⋆-algebra.

## Main declarations

* `CFC.log_monotoneOn`: the logarithm is operator monotone

## TODO

* Show that the log is operator concave
* Show that `x => x * log x` is operator convex
-/

open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter in
lemma CFC.tendsto_cfc_rpow_sub_one_log {a : A} (ha : IsStrictlyPositive a) :
    Tendsto (fun p : ℝ => cfc (fun x => p⁻¹ * (x ^ p - 1)) a) (𝓝[>] 0) (𝓝 (CFC.log a)) := by
  refine tendsto_cfc_fun ?tendsto ?cont
  case cont =>
    refine Eventually.of_forall ?_
    intro p
    refine ContinuousOn.mul (by fun_prop) ?_
    refine ContinuousOn.sub ?_ (by fun_prop)
    exact ContinuousOn.rpow_const (by fun_prop) (by grind)
  case tendsto =>
    let s := {a : A | IsStrictlyPositive a}
    let f (p : ℝ) (x : ℝ) := if p > 0 then p⁻¹ * (x ^ p - 1) else Real.log x
    exact tendstoUniformlyOn_rpow_sub_one_log (by grind) (by grind)

open Classical Real in
/-- `log` is operator monotone. -/
lemma CFC.log_monotoneOn : MonotoneOn log {a : A | IsStrictlyPositive a} := by
  /- We have that `log x = lim_{p → 0} p⁻¹ * (x^p - 1)` with uniform convergence on the spectrum of
  any positive definite operator, which means that `CFC.log a = lim_{p→0} p⁻¹ * (a^p - 1)` by the
  continuity of the CFC (`tendsto_cfc_fun`). Then, we use the fact that `x^p` is monotone for
  `p ∈ [0,1]` (`CFC.monotone_nnrpow`) and that the set of monotone functions is closed
  (`isClosed.monotoneOn`) to conclude the proof. -/
  let s := {a : A | IsStrictlyPositive a}
  let f (p : ℝ) := fun a => if a ∈ s then cfc (A := A) (fun x => p⁻¹ * (x ^ p - 1)) a else 0
  let g := fun a => if a ∈ s then log (A := A) a else 0
  have hg : s.EqOn g (log (A := A)) := by
    intro p hp
    simp [g, hp]
  refine MonotoneOn.congr ?_ hg
  refine isClosed_monotoneOn.mem_of_tendsto (f := f) (b := (𝓝[>] 0)) ?tendsto ?eventually
  case tendsto =>
    rw [tendsto_pi_nhds]
    intro a
    by_cases ha : a ∈ s
    · have hf : ∀ p, cfc (fun x => p⁻¹ * (x ^ p - 1)) a = f p a := by intro p; simp [f, ha]
      refine Filter.Tendsto.congr hf ?_
      have : g a = log a := by simp [g, ha]
      rw [this]
      exact tendsto_cfc_rpow_sub_one_log ha
    · have hg' : g a = 0 := by simp [g, ha]
      have hf' : ∀ i, f i a = 0 := by simp [f, ha]
      simp [hg', hf']
  case eventually =>
    have h₁ : ∀ᶠ (p : ℝ) in 𝓝[>] 0, p < 1 := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      exact eventually_lt_nhds (b := 1) (by norm_num)
    have hp' : ∀ᶠ (p : ℝ) in 𝓝[>] 0, 0 < p := eventually_nhdsWithin_of_forall fun x a => a
    filter_upwards [h₁, hp'] with p hp hp'
    have hf : s.EqOn (fun a : A => p⁻¹ • (a ^ p - 1)) (f p) := by
      intro a ha
      simp only [ha, ↓reduceIte, f, ← smul_eq_mul]
      have h₁ : ContinuousOn (fun x => x ^ p) (spectrum ℝ a) := by
        refine ContinuousOn.rpow_const (by fun_prop) ?_
        have : IsUnit a := ha.2
        grind [= spectrum.zero_notMem_iff]
      have h₂ : ContinuousOn (fun x => x ^ p - 1) (spectrum ℝ a) :=
        ContinuousOn.sub h₁ (by fun_prop)
      rw [cfc_smul _ _ _ h₂, cfc_sub _ _ _ h₁ (by fun_prop)]
      congr
      · rw [CFC.rpow_def, cfc_nnreal_eq_real ..]
        refine cfc_congr ?_
        intro x hx
        simp only [NNReal.coe_rpow, coe_toNNReal']
        grind [= max_eq_left]
      · rw [cfc_const_one (a := a) _]
    refine MonotoneOn.congr ?_ hf
    intro a ha b hb hab
    simp only
    gcongr
    grind

@[gcongr]
lemma CFC.log_le_log {a b : A} (ha : IsStrictlyPositive a) (hab : a ≤ b) : log a ≤ log b :=
  log_monotoneOn ha (ha.of_le hab) hab
