/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Complex.Module

#align_import analysis.convex.complex from "leanprover-community/mathlib"@"15730e8d0af237a2ebafeb8cfbbcf71f6160c2e9"

/-!
# Convexity of half spaces in ℂ

The open and closed half-spaces in ℂ given by an inequality on either the real or imaginary part
are all convex over ℝ.
-/


theorem convex_halfspace_re_lt (r : ℝ) : Convex ℝ { c : ℂ | c.re < r } :=
  convex_halfspace_lt (IsLinearMap.mk Complex.add_re Complex.smul_re) _
#align convex_halfspace_re_lt convex_halfspace_re_lt

theorem convex_halfspace_re_le (r : ℝ) : Convex ℝ { c : ℂ | c.re ≤ r } :=
  convex_halfspace_le (IsLinearMap.mk Complex.add_re Complex.smul_re) _
#align convex_halfspace_re_le convex_halfspace_re_le

theorem convex_halfspace_re_gt (r : ℝ) : Convex ℝ { c : ℂ | r < c.re } :=
  convex_halfspace_gt (IsLinearMap.mk Complex.add_re Complex.smul_re) _
#align convex_halfspace_re_gt convex_halfspace_re_gt

theorem convex_halfspace_re_ge (r : ℝ) : Convex ℝ { c : ℂ | r ≤ c.re } :=
  convex_halfspace_ge (IsLinearMap.mk Complex.add_re Complex.smul_re) _
#align convex_halfspace_re_ge convex_halfspace_re_ge

theorem convex_halfspace_im_lt (r : ℝ) : Convex ℝ { c : ℂ | c.im < r } :=
  convex_halfspace_lt (IsLinearMap.mk Complex.add_im Complex.smul_im) _
#align convex_halfspace_im_lt convex_halfspace_im_lt

theorem convex_halfspace_im_le (r : ℝ) : Convex ℝ { c : ℂ | c.im ≤ r } :=
  convex_halfspace_le (IsLinearMap.mk Complex.add_im Complex.smul_im) _
#align convex_halfspace_im_le convex_halfspace_im_le

theorem convex_halfspace_im_gt (r : ℝ) : Convex ℝ { c : ℂ | r < c.im } :=
  convex_halfspace_gt (IsLinearMap.mk Complex.add_im Complex.smul_im) _
#align convex_halfspace_im_gt convex_halfspace_im_gt

theorem convex_halfspace_im_ge (r : ℝ) : Convex ℝ { c : ℂ | r ≤ c.im } :=
  convex_halfspace_ge (IsLinearMap.mk Complex.add_im Complex.smul_im) _
#align convex_halfspace_im_ge convex_halfspace_im_ge
