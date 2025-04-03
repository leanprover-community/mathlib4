/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Complex.Module

/-!
# Convexity of half spaces in ℂ

The open and closed half-spaces in ℂ given by an inequality on either the real or imaginary part
are all convex over ℝ.
-/


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
