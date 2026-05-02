/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.FunctionTopology

/-!
# Order properties of the operator logarithm

This file shows that the logarithm is operator monotone and concave, i.e. that `CFC.log` is
monotone and concave on the strictly positive elements of a unital C⋆-algebra.

## Main declarations

* `CFC.log_monotoneOn`: the logarithm is operator monotone
* `CFC.concaveOn_log`: the logarithm is operator concave

## TODO

* Show that `x => x * log x` is operator convex
-/

public section

open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter in
lemma CFC.tendsto_cfc_rpow_sub_one_log {a : A} (ha : IsStrictlyPositive a := by cfc_tac) :
    Tendsto (fun p : ℝ => cfc (fun x => p⁻¹ * (x ^ p - 1)) a) (𝓝[>] 0) (𝓝 (CFC.log a)) := by
  refine tendsto_cfc_fun ?tendsto ?cont
  case cont =>
    exact .of_forall fun p ↦ by fun_prop (disch := grind -abstractProof)
  case tendsto =>
    let s := {a : A | IsStrictlyPositive a}
    let f (p : ℝ) (x : ℝ) := if p > 0 then p⁻¹ * (x ^ p - 1) else Real.log x
    have hmain := Real.tendstoLocallyUniformlyOn_rpow_sub_one_log
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi] at hmain
    exact hmain (spectrum ℝ a) (by grind) (by grind)

open Filter Classical Real in
lemma CFC.tendsto_ite_cfc_rpow_sub_one_ite_log :
    Tendsto (fun (p : ℝ) (a : A) =>
      if a ∈ {b : A | IsStrictlyPositive b} then cfc (fun x => p⁻¹ * (x ^ p - 1)) a else 0) (𝓝[>] 0)
      (𝓝 (fun a => if a ∈ {b : A | IsStrictlyPositive b} then CFC.log a else 0)) := by
  rw [tendsto_pi_nhds]
  intro a
  by_cases ha : IsStrictlyPositive a
  · simpa [ha] using CFC.tendsto_cfc_rpow_sub_one_log ha
  · simp_all

open Classical in
private lemma CFC.cfc_rpow_sub_one_eqOn {p : ℝ} :
    {a : A | IsStrictlyPositive a}.EqOn
      (fun a => if a ∈ {b : A | IsStrictlyPositive b}
        then cfc (fun x => p⁻¹ * (x ^ p - 1)) a else 0) (fun a => p⁻¹ • (a ^ p - (1 : A))) := by
  intro a ha
  simp only [ha, ↓reduceIte, ← smul_eq_mul]
  rw [cfc_smul _ (hf := by fun_prop (disch := grind)),
    cfc_sub _ _ (hf := by fun_prop (disch := grind)),
    cfc_const_one .., rpow_eq_cfc_real ..]

open Classical Real in
/-- `log` is operator monotone. -/
lemma CFC.log_monotoneOn : MonotoneOn log {a : A | IsStrictlyPositive a} := by
  /- We have that `log x = lim_{p → 0} p⁻¹ * (x ^ p - 1)` with uniform convergence on the spectrum
  of any positive definite operator, which means that `CFC.log a = lim_{p → 0} p⁻¹ * (a ^ p - 1)`
  by the continuity of the continuous functional calculus (`tendsto_cfc_fun`). Then, we use the
  fact that `x^p` is monotone for `p ∈ [0,1]` (`CFC.monotone_nnrpow`) and that the set of
  monotone functions is closed (`isClosed_monotoneOn`) to conclude the proof. -/
  let s := {a : A | IsStrictlyPositive a}
  let f (p : ℝ) := fun a => if a ∈ s then cfc (A := A) (fun x => p⁻¹ * (x ^ p - 1)) a else 0
  let g := fun a => if a ∈ s then log (A := A) a else 0
  have hg : s.EqOn g (log (A := A)) := by simp +contextual [g, Set.EqOn]
  refine MonotoneOn.congr ?_ hg
  refine isClosed_monotoneOn.mem_of_tendsto (f := f) (b := (𝓝[>] 0))
    tendsto_ite_cfc_rpow_sub_one_ite_log ?_
  have h₁ : ∀ᶠ (p : ℝ) in 𝓝[>] 0, 0 < p ∧ p < 1 := nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [h₁] with p ⟨hp, hp'⟩
  refine MonotoneOn.congr (fun a ha b hb hab ↦ ?_) CFC.cfc_rpow_sub_one_eqOn.symm
  gcongr
  grind

@[gcongr]
lemma CFC.log_le_log {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a := by cfc_tac) :
    log a ≤ log b :=
  log_monotoneOn ha (ha.of_le hab) hab

open Classical Real Set in
/-- `log` is operator concave. -/
lemma CFC.concaveOn_log : ConcaveOn ℝ {a : A | IsStrictlyPositive a} log := by
  /- We have that `log x = lim_{p → 0} p⁻¹ * (x ^ p - 1)` with uniform convergence on the spectrum
  of any positive definite operator, which means that `CFC.log a = lim_{p → 0} p⁻¹ * (a ^ p - 1)`
  by the continuity of the continuous functional calculus (`tendsto_cfc_fun`). Then, we use the
  fact that `x^p` is concave for `p ∈ [0,1]` (`CFC.concaveOn_rpow`) and that the set of
  concave functions is closed (`isClosed_setOf_concaveOn`) to conclude the proof. -/
  set s := {a : A | IsStrictlyPositive a}
  let f (p : ℝ) := fun a => if a ∈ s then cfc (A := A) (fun x => p⁻¹ * (x ^ p - 1)) a else 0
  let g := fun a => if a ∈ s then log (A := A) a else 0
  have hg : s.EqOn g (log (A := A)) := by simp +contextual [g, Set.EqOn]
  refine ConcaveOn.congr ?_ hg
  apply isClosed_setOf_concaveOn.mem_of_tendsto (f := f) (b := (𝓝[>] (0 : ℝ)))
    tendsto_ite_cfc_rpow_sub_one_ite_log ?_
  have h₁ : ∀ᶠ (p : ℝ) in 𝓝[>] 0, 0 < p ∧ p < 1 := nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [h₁] with p ⟨hp, hp'⟩
  refine ConcaveOn.congr ?_ CFC.cfc_rpow_sub_one_eqOn.symm
  refine ConcaveOn.smul (by positivity) ?_
  have h_convex : Convex ℝ s := by grind [convex_iff_forall_pos]
  refine ConcaveOn.sub ?_ (convexOn_const _ h_convex)
  refine ConcaveOn.subset (t := Ici 0) ?_ (by grind) h_convex
  exact CFC.concaveOn_rpow (by grind)
