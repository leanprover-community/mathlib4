/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

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

theorem slope_fun_def (f : k → PE) : slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a) :=
  rfl

theorem slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm

theorem slope_fun_def_field (f : k → k) (a : k) : slope f a = fun b => (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm

@[simp]
theorem slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 := by
  rw [slope, sub_self, inv_zero, zero_smul]

theorem slope_def_module (f : k → E) (a b : k) : slope f a b = (b - a)⁻¹ • (f b - f a) :=
  rfl

@[simp]
theorem sub_smul_slope (f : k → PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f a := by
  rcases eq_or_ne a b with (rfl | hne)
  · rw [sub_self, zero_smul, vsub_self]
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]

theorem sub_smul_slope_vadd (f : k → PE) (a b : k) : (b - a) • slope f a b +ᵥ f a = f b := by
  rw [sub_smul_slope, vsub_vadd]

@[simp]
theorem slope_vadd_const (f : k → E) (c : PE) : (slope fun x => f x +ᵥ c) = slope f := by
  ext a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

@[simp]
theorem slope_sub_smul (f : k → E) {a b : k} (h : a ≠ b) :
    slope (fun x => (x - a) • f x) a b = f b := by
  simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]

theorem eq_of_slope_eq_zero {f : k → PE} {a b : k} (h : slope f a b = (0 : E)) : f a = f b := by
  rw [← sub_smul_slope_vadd f a b, h, smul_zero, zero_vadd]

theorem AffineMap.slope_comp {F PF : Type*} [AddCommGroup F] [Module k F] [AddTorsor F PF]
    (f : PE →ᵃ[k] PF) (g : k → PE) (a b : k) : slope (f ∘ g) a b = f.linear (slope g a b) := by
  simp only [slope, (· ∘ ·), f.linear.map_smul, f.linearMap_vsub]

theorem LinearMap.slope_comp {F : Type*} [AddCommGroup F] [Module k F] (f : E →ₗ[k] F) (g : k → E)
    (a b : k) : slope (f ∘ g) a b = f (slope g a b) :=
  f.toAffineMap.slope_comp g a b

theorem slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a := by
  rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]

@[simp] lemma slope_neg (f : k → E) (x y : k) : slope (fun t ↦ -f t) x y = -slope f x y := by
  simp only [slope_def_module, neg_sub_neg, ← smul_neg, neg_sub]

@[simp] lemma slope_neg_fun (f : k → E) : slope (-f) = -slope f := by
  ext x y; exact slope_neg f x y

lemma slope_eq_zero_iff {f : k → E} {a b : k} : slope f a b = 0 ↔ f a = f b := by
  simp [slope, sub_eq_zero, eq_comm, or_iff_right_of_imp (congr_arg _)]

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `lineMap_slope_slope_sub_div_sub`. -/
theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k) :
    ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c := by
  by_cases hab : a = b
  · subst hab
    rw [sub_self, zero_div, zero_smul, zero_add]
    by_cases hac : a = c
    · simp [hac]
    · rw [div_self (sub_ne_zero.2 <| Ne.symm hac), one_smul]
  by_cases hbc : b = c
  · subst hbc
    simp [sub_ne_zero.2 (Ne.symm hab)]
  rw [add_comm]
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hab), smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hbc),
    vsub_add_vsub_cancel]

set_option linter.unusedSimpArgs false in
/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`lineMap` to express this property. -/
theorem lineMap_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
    lineMap (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c := by
  simp [← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c, lineMap_apply_module]
  match_scalars
  field_simp [sub_ne_zero.2 h.symm]
  ring

/-- `slope f a b` is an affine combination of `slope f a (lineMap a b r)` and
`slope f (lineMap a b r) b`. We use `lineMap` to express this property. -/
theorem lineMap_slope_lineMap_slope_lineMap (f : k → PE) (a b r : k) :
    lineMap (slope f (lineMap a b r) b) (slope f a (lineMap a b r)) r = slope f a b := by
  obtain rfl | hab : a = b ∨ a ≠ b := Classical.em _; · simp
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b]
  convert lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hab.symm using 2
  rw [lineMap_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]

section Order

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

lemma slope_nonneg_iff_of_le (hxy : x ≤ y) : 0 ≤ slope f x y ↔ f x ≤ f y := by
  by_cases hxeqy : x = y
  · simp [hxeqy]
  refine ⟨fun h ↦ ?_, fun h ↦ smul_nonneg (inv_nonneg.2 (sub_nonneg.2 hxy)) ?_⟩
  · have := smul_nonneg (sub_nonneg.2 hxy) h
    rwa [slope, ← mul_smul, mul_inv_cancel₀ (mt sub_eq_zero.1 (Ne.symm hxeqy)), one_smul,
      vsub_eq_sub, sub_nonneg] at this
  · rwa [vsub_eq_sub, sub_nonneg]

lemma slope_nonpos_iff_of_le (hxy : x ≤ y) : slope f x y ≤ 0 ↔ f y ≤ f x := by
  simpa using slope_nonneg_iff_of_le (f := -f) hxy

lemma slope_pos_iff_of_le (hxy : x ≤ y) : 0 < slope f x y ↔ f x < f y := by
  simp_rw [lt_iff_le_and_ne, slope_nonneg_iff_of_le hxy, Ne, eq_comm, slope_eq_zero_iff]

lemma slope_neg_iff_of_le (hxy : x ≤ y) : slope f x y < 0 ↔ f y < f x := by
  simpa using slope_pos_iff_of_le (f := -f) hxy

end Order
