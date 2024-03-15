/-
Copyright (c) 2023 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Basic

/-!
# Theorems about convexity on the complex plane
-/

open Set
open scoped ComplexOrder

namespace Complex

/-- A version of `convexHull_prod` for `Set.reProdIm`. -/
lemma convexHull_reProdIm (s t : Set ℝ) :
    convexHull ℝ (s ×ℂ t) = convexHull ℝ s ×ℂ convexHull ℝ t :=
  calc
    convexHull ℝ (equivRealProdLm ⁻¹' (s ×ˢ t)) = equivRealProdLm ⁻¹' convexHull ℝ (s ×ˢ t) := by
      simpa only [← LinearEquiv.image_symm_eq_preimage]
        using ((equivRealProdLm.symm.toLinearMap).image_convexHull (s ×ˢ t)).symm
    _ = convexHull ℝ s ×ℂ convexHull ℝ t := by rw [convexHull_prod]; rfl

/-- The slit plane is star-convex at a positive number. -/
lemma starConvex_slitPlane {z : ℂ} (hz : 0 < z) : StarConvex ℝ z slitPlane :=
  Complex.compl_Iic_zero ▸ starConvex_compl_Iic hz

/-- The slit plane is star-shaped at a positive real number. -/
lemma starConvex_ofReal_slitPlane {x : ℝ} (hx : 0 < x) : StarConvex ℝ ↑x slitPlane :=
  starConvex_slitPlane <| zero_lt_real.2 hx

/-- The slit plane is star-shaped at `1`. -/
lemma starConvex_one_slitPlane : StarConvex ℝ 1 slitPlane := starConvex_slitPlane one_pos
