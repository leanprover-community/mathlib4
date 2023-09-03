/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
-/

variable {α E : Type*} [NormedAddCommGroup E]

theorem dist_birkhoffSum_apply_birkhoffSum (f : α → α) (g : α → E) (n : ℕ) (x : α) :
    dist (birkhoffSum f g n (f x)) (birkhoffSum f g n x) = dist (g (f^[n] x)) (g x) := by
  simp only [dist_eq_norm, birkhoffSum_apply_sub_birkhoffSum]

variable (𝕜 : Type*) [NormedDivisionRing 𝕜] [NormedAlgebra ℚ 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

#check Rat.norm_cast
theorem dist_birkhoffAverage_apply_birkhoffAverage (f : α → α) (g : α → E) (n : ℕ) (x : α) :
    dist (birkhoffAverage 𝕜 f g n (f x)) (birkhoffAverage 𝕜 f g n x) =
      dist (g (f^[n] x)) (g x) / n := by
  simp [birkhoffAverage, dist_smul₀, dist_birkhoffSum_apply_birkhoffSum]
