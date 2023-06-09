/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : 1 < p) :
    StrictConcaveOn ℝ (Set.Ici 0) fun x : ℝ => x ^ p := by
  sorry

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : 1 ≤ p) :
    ConcaveOn ℝ (Set.Ici 0) fun x : ℝ => x ^ p := by
  sorry
