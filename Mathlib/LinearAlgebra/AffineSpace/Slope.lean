/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.FieldSimp

#align_import linear_algebra.affine_space.slope from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Slope of a function

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some basic theorems about `slope`. The `slope` function naturally appears in the Mean
Value Theorem, and in the proof of the fact that a function with nonnegative second derivative on an
interval is convex on this interval.

## Tags

affine space, slope
-/

open AffineMap

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

/-- `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval
`[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`. -/
def slope (f : k → PE) (a b : k) : E :=
  (b - a)⁻¹ • (f b -ᵥ f a)
#align slope slope

theorem slope_fun_def (f : k → PE) : slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a) :=
  rfl
#align slope_fun_def slope_fun_def

theorem slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm
#align slope_def_field slope_def_field

theorem slope_fun_def_field (f : k → k) (a : k) : slope f a = fun b => (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm
#align slope_fun_def_field slope_fun_def_field

@[simp]
theorem slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 := by
  rw [slope, sub_self, inv_zero, zero_smul]
  -- 🎉 no goals
#align slope_same slope_same

theorem slope_def_module (f : k → E) (a b : k) : slope f a b = (b - a)⁻¹ • (f b - f a) :=
  rfl
#align slope_def_module slope_def_module

@[simp]
theorem sub_smul_slope (f : k → PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f a := by
  rcases eq_or_ne a b with (rfl | hne)
  -- ⊢ (a - a) • slope f a a = f a -ᵥ f a
  · rw [sub_self, zero_smul, vsub_self]
    -- 🎉 no goals
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]
    -- 🎉 no goals
#align sub_smul_slope sub_smul_slope

theorem sub_smul_slope_vadd (f : k → PE) (a b : k) : (b - a) • slope f a b +ᵥ f a = f b := by
  rw [sub_smul_slope, vsub_vadd]
  -- 🎉 no goals
#align sub_smul_slope_vadd sub_smul_slope_vadd

@[simp]
theorem slope_vadd_const (f : k → E) (c : PE) : (slope fun x => f x +ᵥ c) = slope f := by
  ext a b
  -- ⊢ slope (fun x => f x +ᵥ c) a b = slope f a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]
  -- 🎉 no goals
#align slope_vadd_const slope_vadd_const

@[simp]
theorem slope_sub_smul (f : k → E) {a b : k} (h : a ≠ b) :
    slope (fun x => (x - a) • f x) a b = f b := by
  simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]
  -- 🎉 no goals
#align slope_sub_smul slope_sub_smul

theorem eq_of_slope_eq_zero {f : k → PE} {a b : k} (h : slope f a b = (0 : E)) : f a = f b := by
  rw [← sub_smul_slope_vadd f a b, h, smul_zero, zero_vadd]
  -- 🎉 no goals
#align eq_of_slope_eq_zero eq_of_slope_eq_zero

theorem AffineMap.slope_comp {F PF : Type*} [AddCommGroup F] [Module k F] [AddTorsor F PF]
    (f : PE →ᵃ[k] PF) (g : k → PE) (a b : k) : slope (f ∘ g) a b = f.linear (slope g a b) := by
  simp only [slope, (· ∘ ·), f.linear.map_smul, f.linearMap_vsub]
  -- 🎉 no goals
#align affine_map.slope_comp AffineMap.slope_comp

theorem LinearMap.slope_comp {F : Type*} [AddCommGroup F] [Module k F] (f : E →ₗ[k] F) (g : k → E)
    (a b : k) : slope (f ∘ g) a b = f (slope g a b) :=
  f.toAffineMap.slope_comp g a b
#align linear_map.slope_comp LinearMap.slope_comp

theorem slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a := by
  rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]
  -- 🎉 no goals
#align slope_comm slope_comm

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `lineMap_slope_slope_sub_div_sub`. -/
theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k) :
    ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c := by
  by_cases hab : a = b
  -- ⊢ ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slop …
  · subst hab
    -- ⊢ ((a - a) / (c - a)) • slope f a a + ((c - a) / (c - a)) • slope f a c = slop …
    rw [sub_self, zero_div, zero_smul, zero_add]
    -- ⊢ ((c - a) / (c - a)) • slope f a c = slope f a c
    by_cases hac : a = c
    -- ⊢ ((c - a) / (c - a)) • slope f a c = slope f a c
    · simp [hac]
      -- 🎉 no goals
    · rw [div_self (sub_ne_zero.2 <| Ne.symm hac), one_smul]
      -- 🎉 no goals
  by_cases hbc : b = c;
  -- ⊢ ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slop …
  · subst hbc
    -- ⊢ ((b - a) / (b - a)) • slope f a b + ((b - b) / (b - a)) • slope f b b = slop …
    simp [sub_ne_zero.2 (Ne.symm hab)]
    -- 🎉 no goals
  rw [add_comm]
  -- ⊢ ((c - b) / (c - a)) • slope f b c + ((b - a) / (c - a)) • slope f a b = slop …
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hab), smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hbc),
    vsub_add_vsub_cancel]
#align sub_div_sub_smul_slope_add_sub_div_sub_smul_slope sub_div_sub_smul_slope_add_sub_div_sub_smul_slope

/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`lineMap` to express this property. -/
theorem lineMap_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
    lineMap (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c := by
  field_simp [sub_ne_zero.2 h.symm, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
    lineMap_apply_module]
#align line_map_slope_slope_sub_div_sub lineMap_slope_slope_sub_div_sub

/-- `slope f a b` is an affine combination of `slope f a (lineMap a b r)` and
`slope f (lineMap a b r) b`. We use `lineMap` to express this property. -/
theorem lineMap_slope_lineMap_slope_lineMap (f : k → PE) (a b r : k) :
    lineMap (slope f (lineMap a b r) b) (slope f a (lineMap a b r)) r = slope f a b := by
  obtain rfl | hab : a = b ∨ a ≠ b := Classical.em _; · simp
  -- ⊢ ↑(lineMap (slope f (↑(lineMap a a) r) a) (slope f a (↑(lineMap a a) r))) r = …
                                                        -- 🎉 no goals
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b]
  -- ⊢ ↑(lineMap (slope f b (↑(lineMap a b) r)) (slope f (↑(lineMap a b) r) a)) r = …
  convert lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hab.symm using 2
  -- ⊢ r = (a - ↑(lineMap a b) r) / (a - b)
  rw [lineMap_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]
#align line_map_slope_line_map_slope_line_map lineMap_slope_lineMap_slope_lineMap
