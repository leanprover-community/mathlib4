/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

open Set

namespace NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ≥0 univ fun x : ℝ≥0 => x ^ p := by
  have hp₀' : 0 < 1 / p := by positivity
  have hp₁' : 1 < 1 / p := by rw [one_lt_div hp₀]; exact hp₁
  let f := NNReal.orderIsoRpow (1 / p) hp₀'
  have h₁ : StrictConvexOn ℝ≥0 univ f := by
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    exact (strictConvexOn_rpow hp₁').2 (by positivity : 0 ≤ x) (by positivity : 0 ≤ y)
      (by simp [hxy]) ha hb (by simp; norm_cast)
  have h₂ : ∀ x, f.symm x = x ^ p := by simp [NNReal.orderIsoRpow_symm_eq]
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  simp only [←h₂]
  exact (strictConcaveOn_orderIso_symm f h₁).2 (Set.mem_univ x) (Set.mem_univ y) hxy ha hb hab

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ConcaveOn ℝ≥0 univ fun x : ℝ≥0 => x ^ p := by
  by_cases hp : p = 0
  case pos => exact ⟨convex_univ, fun _ _ _ _ _ _ _ _ hab => by simp [hp, hab]⟩
  case neg =>
    push_neg at hp
    by_cases hp' : p = 1
    case pos => exact ⟨convex_univ, by simp [hp']⟩
    case neg =>
      push_neg at hp'
      exact (strictConcaveOn_rpow (by positivity) (lt_of_le_of_ne hp₁ hp')).concaveOn

lemma strictConcaveOn_sqrt : StrictConcaveOn ℝ≥0 univ NNReal.sqrt := by
  have : NNReal.sqrt = fun (x:ℝ≥0) => x ^ (1 / (2:ℝ)) := by
    ext x; exact_mod_cast NNReal.sqrt_eq_rpow x
  rw [this]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

lemma strictConvexOn_inv : StrictConvexOn ℝ≥0 (Set.Ioi 0) fun x : ℝ≥0 => x⁻¹ := by
  refine ⟨convex_Ioi 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hpos : 0 < a * x + b * y := by positivity
  have hxinv : x⁻¹ * x = 1 := inv_mul_cancel (by positivity)
  have hyinv : y⁻¹ * y = 1 := inv_mul_cancel (by positivity)
  have h_main : 1 < (a * x⁻¹ + b * y⁻¹) * (a * x + b * y) := by
    calc
      (a * x⁻¹ + b * y⁻¹) * (a * x + b * y)
        = a^2 * x⁻¹ * x + b^2 * y⁻¹ * y + a * b * (x⁻¹ * y + y⁻¹ * x)
                  := by ring
      _ = a^2 + b^2 + a * b * (x⁻¹ * y + y⁻¹ * x)
                  := by simp only [ne_eq, mul_assoc (a ^ 2), hxinv, mul_one, mul_assoc (b ^ 2), hyinv]
      _ = a^2 + b^2 + a * b * ((x^2 + y^2) / (x * y))
                  := by sorry
      _ > a^2 + b^2 + a * b * 2
                  := by sorry
      _ = (a + b)^2
                  := by sorry
      _ = 1
                  := by sorry
  simp [inv_pos_lt_iff_one_lt_mul hpos, h_main]

lemma strictConvexOn_rpow_of_neg {p : ℝ} (hp₀ : p < 0) :
    StrictConvexOn ℝ≥0 (Set.Ioi 0) fun x : ℝ≥0 => x ^ p := by
  -- use two_mul_le_add_sq
  sorry

end NNReal

namespace Real

open NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ (Set.Ici 0) fun x : ℝ => x ^ p := by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let x' : ℝ≥0 := ⟨x, hx⟩
  let y' : ℝ≥0 := ⟨y, hy⟩
  let a' : ℝ≥0 := ⟨a, by positivity⟩
  let b' : ℝ≥0 := ⟨b, by positivity⟩
  have hx' : (fun z => z ^ p) x = (fun z => z ^ p) x' := rfl
  have hy' : (fun z => z ^ p) y = (fun z => z ^ p) y' := rfl
  have hxy' : x' ≠ y' := Subtype.ne_of_val_ne hxy
  have hab' : a' + b' = 1 := by ext; simp [hab]
  rw [hx', hy']
  exact (NNReal.strictConcaveOn_rpow hp₀ hp₁).2 (Set.mem_univ x') (Set.mem_univ y')
    hxy' (by exact_mod_cast ha) (by exact_mod_cast hb) hab'

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ConcaveOn ℝ (Set.Ici 0) fun x : ℝ => x ^ p := by
  by_cases hp : p = 0
  case pos => exact ⟨convex_Ici 0, fun _ _ _ _ _ _ _ _ hab => by simp [hp, hab]⟩
  case neg =>
    push_neg at hp
    by_cases hp' : p = 1
    case pos => exact ⟨convex_Ici 0, by simp [hp']⟩
    case neg =>
      push_neg at hp'
      exact (strictConcaveOn_rpow (by positivity) (lt_of_le_of_ne hp₁ hp')).concaveOn

lemma strictConcaveOn_sqrt : StrictConcaveOn ℝ (Set.Ici 0) Real.sqrt := by
  have : Real.sqrt = fun (x:ℝ) => x ^ (1 / (2:ℝ)) := by
    ext x; exact Real.sqrt_eq_rpow x
  rw [this]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

lemma strictConvexOn_rpow_of_neg {p : ℝ} (hp₀ : p < 0) :
    StrictConvexOn ℝ (Set.Ioi 0) fun x : ℝ => x ^ p := by
  sorry

end Real
