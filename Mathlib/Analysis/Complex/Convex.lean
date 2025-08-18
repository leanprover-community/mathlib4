/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.PathConnected

/-!
# Theorems about convexity on the complex plane

We show that the open and closed half-spaces in ℂ given by an inequality on either the real or
imaginary part are all convex over ℝ. We also prove some results on star-convexity for the
slit plane.
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

end Complex

open Complex

variable (r : ℝ)

theorem convex_halfSpace_re_lt : Convex ℝ { c : ℂ | c.re < r } :=
  convex_halfSpace_lt (.mk add_re smul_re) _
theorem convex_halfSpace_re_le : Convex ℝ { c : ℂ | c.re ≤ r } :=
  convex_halfSpace_le (.mk add_re smul_re) _
theorem convex_halfSpace_re_gt : Convex ℝ { c : ℂ | r < c.re } :=
  convex_halfSpace_gt (.mk add_re smul_re) _
theorem convex_halfSpace_re_ge : Convex ℝ { c : ℂ | r ≤ c.re } :=
  convex_halfSpace_ge (.mk add_re smul_re) _
theorem convex_halfSpace_im_lt : Convex ℝ { c : ℂ | c.im < r } :=
  convex_halfSpace_lt (.mk add_im smul_im) _
theorem convex_halfSpace_im_le : Convex ℝ { c : ℂ | c.im ≤ r } :=
  convex_halfSpace_le (.mk add_im smul_im) _
theorem convex_halfSpace_im_gt : Convex ℝ { c : ℂ | r < c.im } :=
  convex_halfSpace_gt (.mk add_im smul_im) _
theorem convex_halfSpace_im_ge : Convex ℝ { c : ℂ | r ≤ c.im } :=
  convex_halfSpace_ge (.mk add_im smul_im) _
lemma Complex.isConnected_of_upperHalfPlane {r} {s : Set ℂ} (hs₁ : {z | r < z.im} ⊆ s)
    (hs₂ : s ⊆ {z | r ≤ z.im}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOf_lt_im] using hs₂)
  exact (convex_halfSpace_im_gt r).isConnected ⟨(r + 1) * I, by simp⟩

lemma Complex.isConnected_of_lowerHalfPlane {r} {s : Set ℂ} (hs₁ : {z | z.im < r} ⊆ s)
    (hs₂ : s ⊆ {z | z.im ≤ r}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOf_im_lt] using hs₂)
  exact (convex_halfSpace_im_lt r).isConnected ⟨(r - 1) * I, by simp⟩
