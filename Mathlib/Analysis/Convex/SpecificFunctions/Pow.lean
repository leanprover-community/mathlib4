/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
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
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike

/-!
# Convexity properties of `rpow`

We prove basic convexity properties of the `rpow` function. The proofs are elementary and do not
require calculus, and as such this file has only moderate dependencies.

## Main declarations

* `NNReal.strictConcaveOn_rpow`, `Real.strictConcaveOn_rpow`: strict concavity of
  `fun x ↦ x ^ p` for p ∈ (0,1)
* `NNReal.concaveOn_rpow`, `Real.concaveOn_rpow`: concavity of `fun x ↦ x ^ p` for p ∈ [0,1]

Note that convexity for `p > 1` can be found in `Analysis.Convex.SpecificFunctions.Basic`, which
requires slightly less imports.

## TODO

* Prove convexity for negative powers.
-/

public section

open Set

namespace NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ≥0 univ fun x : ℝ≥0 ↦ x ^ p := by
  have hp₀' : 0 < 1 / p := div_pos zero_lt_one hp₀
  have hp₁' : 1 < 1 / p := by rw [one_lt_div hp₀]; exact hp₁
  let f := NNReal.orderIsoRpow (1 / p) hp₀'
  have h₁ : StrictConvexOn ℝ≥0 univ f := by
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    exact (strictConvexOn_rpow hp₁').2 x.2 y.2 (by simp [hxy]) ha hb (by simp; norm_cast)
  have h₂ : ∀ x, f.symm x = x ^ p := by simp [f, NNReal.orderIsoRpow_symm_eq]
  refine ⟨convex_univ, fun x mx y my hxy a b ha hb hab => ?_⟩
  simp only [← h₂]
  exact (f.strictConcaveOn_symm h₁).2 mx my hxy ha hb hab

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ConcaveOn ℝ≥0 univ fun x : ℝ≥0 ↦ x ^ p := by
  rcases eq_or_lt_of_le hp₀ with (rfl | hp₀)
  · simpa only [rpow_zero] using concaveOn_const (c := 1) convex_univ
  rcases eq_or_lt_of_le hp₁ with (rfl | hp₁)
  · simpa only [rpow_one] using concaveOn_id convex_univ
  exact (strictConcaveOn_rpow hp₀ hp₁).concaveOn

lemma strictConcaveOn_sqrt : StrictConcaveOn ℝ≥0 univ NNReal.sqrt := by
  have : NNReal.sqrt = fun x : ℝ≥0 ↦ x ^ (1 / (2 : ℝ)) := by
    ext x; exact mod_cast NNReal.sqrt_eq_rpow x
  rw [this]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

end NNReal

namespace Real

open NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ p := by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let x' : ℝ≥0 := .mk x hx
  let y' : ℝ≥0 := .mk y hy
  let a' : ℝ≥0 := .mk a ha.le
  let b' : ℝ≥0 := .mk b hb.le
  have hxy' : x' ≠ y' := Subtype.coe_ne_coe.1 hxy
  have hab' : a' + b' = 1 := by ext; simp [a', b', hab]
  exact_mod_cast (NNReal.strictConcaveOn_rpow hp₀ hp₁).2 (Set.mem_univ x') (Set.mem_univ y')
    hxy' (mod_cast ha) (mod_cast hb) hab'

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ p := by
  rcases eq_or_lt_of_le hp₀ with (rfl | hp₀)
  · simpa only [rpow_zero] using concaveOn_const (c := 1) (convex_Ici _)
  rcases eq_or_lt_of_le hp₁ with (rfl | hp₁)
  · simpa only [rpow_one] using concaveOn_id (convex_Ici _)
  exact (strictConcaveOn_rpow hp₀ hp₁).concaveOn

lemma strictConcaveOn_sqrt : StrictConcaveOn ℝ (Set.Ici 0) (√· : ℝ → ℝ) := by
  rw [funext Real.sqrt_eq_rpow]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

end Real
