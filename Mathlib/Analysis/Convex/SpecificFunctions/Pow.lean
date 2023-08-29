/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

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

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open Set

namespace NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ≥0 univ fun x : ℝ≥0 ↦ x ^ p := by
  have hp₀' : 0 < 1 / p := by positivity
  -- ⊢ StrictConcaveOn ℝ≥0 univ fun x => x ^ p
  have hp₁' : 1 < 1 / p := by rw [one_lt_div hp₀]; exact hp₁
  -- ⊢ StrictConcaveOn ℝ≥0 univ fun x => x ^ p
  let f := NNReal.orderIsoRpow (1 / p) hp₀'
  -- ⊢ StrictConcaveOn ℝ≥0 univ fun x => x ^ p
  have h₁ : StrictConvexOn ℝ≥0 univ f := by
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    exact (strictConvexOn_rpow hp₁').2 (by positivity : 0 ≤ x) (by positivity : 0 ≤ y)
      (by simp [hxy]) ha hb (by simp; norm_cast)
  have h₂ : ∀ x, f.symm x = x ^ p := by simp [NNReal.orderIsoRpow_symm_eq]
  -- ⊢ StrictConcaveOn ℝ≥0 univ fun x => x ^ p
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  simp only [←h₂]
  -- ⊢ a • ↑(OrderIso.symm (orderIsoRpow (1 / p) hp₀')) x + b • ↑(OrderIso.symm (or …
  exact (f.strictConcaveOn_symm h₁).2 (Set.mem_univ x) (Set.mem_univ y) hxy ha hb hab
  -- 🎉 no goals

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ConcaveOn ℝ≥0 univ fun x : ℝ≥0 ↦ x ^ p := by
  by_cases hp : p = 0
  -- ⊢ ConcaveOn ℝ≥0 univ fun x => x ^ p
  case pos => exact ⟨convex_univ, fun _ _ _ _ _ _ _ _ hab => by simp [hp, hab]⟩
  -- ⊢ ConcaveOn ℝ≥0 univ fun x => x ^ p
  -- 🎉 no goals
  case neg =>
    push_neg at hp
    by_cases hp' : p = 1
    case pos => exact ⟨convex_univ, by simp [hp']⟩
    case neg =>
      push_neg at hp'
      exact (strictConcaveOn_rpow (by positivity) (lt_of_le_of_ne hp₁ hp')).concaveOn

lemma strictConcaveOn_sqrt : StrictConcaveOn ℝ≥0 univ NNReal.sqrt := by
  have : NNReal.sqrt = fun (x:ℝ≥0) ↦ x ^ (1 / (2:ℝ)) := by
    ext x; exact_mod_cast NNReal.sqrt_eq_rpow x
  rw [this]
  -- ⊢ StrictConcaveOn ℝ≥0 univ fun x => x ^ (1 / 2)
  exact strictConcaveOn_rpow (by positivity) (by linarith)
  -- 🎉 no goals

end NNReal

namespace Real

open NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ p := by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  let x' : ℝ≥0 := ⟨x, hx⟩
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  let y' : ℝ≥0 := ⟨y, hy⟩
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  let a' : ℝ≥0 := ⟨a, by positivity⟩
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  let b' : ℝ≥0 := ⟨b, by positivity⟩
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  have hx' : (fun z => z ^ p) x = (fun z => z ^ p) x' := rfl
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  have hy' : (fun z => z ^ p) y = (fun z => z ^ p) y' := rfl
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  have hxy' : x' ≠ y' := Subtype.ne_of_val_ne hxy
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  have hab' : a' + b' = 1 := by ext; simp [hab]
  -- ⊢ a • (fun x => x ^ p) x + b • (fun x => x ^ p) y < (fun x => x ^ p) (a • x +  …
  rw [hx', hy']
  -- ⊢ a • ↑((fun z => z ^ p) x') + b • ↑((fun z => z ^ p) y') < (fun x => x ^ p) ( …
  exact (NNReal.strictConcaveOn_rpow hp₀ hp₁).2 (Set.mem_univ x') (Set.mem_univ y')
    hxy' (by exact_mod_cast ha) (by exact_mod_cast hb) hab'

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ p := by
  by_cases hp : p = 0
  -- ⊢ ConcaveOn ℝ (Ici 0) fun x => x ^ p
  case pos => exact ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ hab => by simp [hp, hab]⟩
  -- ⊢ ConcaveOn ℝ (Ici 0) fun x => x ^ p
  -- 🎉 no goals
  case neg =>
    push_neg at hp
    by_cases hp' : p = 1
    case pos => exact ⟨convex_Ici 0, by simp [hp']⟩
    case neg =>
      push_neg at hp'
      exact (strictConcaveOn_rpow (by positivity) (lt_of_le_of_ne hp₁ hp')).concaveOn

lemma strictConcaveOn_sqrt : StrictConcaveOn ℝ (Set.Ici 0) Real.sqrt := by
  have : Real.sqrt = fun (x:ℝ) ↦ x ^ (1 / (2:ℝ)) := by
    ext x; exact Real.sqrt_eq_rpow x
  rw [this]
  -- ⊢ StrictConcaveOn ℝ (Ici 0) fun x => x ^ (1 / 2)
  exact strictConcaveOn_rpow (by positivity) (by linarith)
  -- 🎉 no goals

end Real
