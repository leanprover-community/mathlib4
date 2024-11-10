/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Module

/-!
# Convexity of half spaces in ℂ

The open and closed half-spaces in ℂ given by an inequality on either the real or imaginary part
are all convex over ℝ.
-/

open Complex

theorem convex_halfspace_re_lt (r : ℝ) : Convex ℝ { c : ℂ | c.re < r } :=
  convex_halfspace_lt (IsLinearMap.mk Complex.add_re Complex.smul_re) _

theorem convex_halfspace_re_le (r : ℝ) : Convex ℝ { c : ℂ | c.re ≤ r } :=
  convex_halfspace_le (IsLinearMap.mk Complex.add_re Complex.smul_re) _

theorem convex_halfspace_re_gt (r : ℝ) : Convex ℝ { c : ℂ | r < c.re } :=
  convex_halfspace_gt (IsLinearMap.mk Complex.add_re Complex.smul_re) _

theorem convex_halfspace_re_ge (r : ℝ) : Convex ℝ { c : ℂ | r ≤ c.re } :=
  convex_halfspace_ge (IsLinearMap.mk Complex.add_re Complex.smul_re) _

theorem convex_halfspace_im_lt (r : ℝ) : Convex ℝ { c : ℂ | c.im < r } :=
  convex_halfspace_lt (IsLinearMap.mk Complex.add_im Complex.smul_im) _

theorem convex_halfspace_im_le (r : ℝ) : Convex ℝ { c : ℂ | c.im ≤ r } :=
  convex_halfspace_le (IsLinearMap.mk Complex.add_im Complex.smul_im) _

theorem convex_halfspace_im_gt (r : ℝ) : Convex ℝ { c : ℂ | r < c.im } :=
  convex_halfspace_gt (IsLinearMap.mk Complex.add_im Complex.smul_im) _

theorem convex_halfspace_im_ge (r : ℝ) : Convex ℝ { c : ℂ | r ≤ c.im } :=
  convex_halfspace_ge (IsLinearMap.mk Complex.add_im Complex.smul_im) _

lemma Complex.isConnected_of_upperHalfPlane {s : Set ℂ} (hs₁ : {z | 0 < z.im} ⊆ s)
    (hs₂ : s ⊆ {z | 0 ≤ z.im}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOf_lt_im] using hs₂)
  exact (convex_halfspace_im_gt 0).isConnected ⟨I, Set.mem_setOf.mpr (I_im ▸ zero_lt_one' ℝ)⟩

lemma Complex.isConnected_of_lowerHalfPlane {s : Set ℂ} (hs₁ : {z | z.im < 0} ⊆ s)
    (hs₂ : s ⊆ {z | z.im ≤ 0}) : IsConnected s := by
  rw [← Equiv.star.surjective.image_preimage s]
  refine IsConnected.image (f := Equiv.star) ?_ continuous_star.continuousOn
  apply Complex.isConnected_of_upperHalfPlane
  · exact fun z hz ↦ hs₁ <| show star z ∈ _ by simpa
  · exact fun z hz ↦ by simpa using show (star z).im ≤ 0 from hs₂ hz
