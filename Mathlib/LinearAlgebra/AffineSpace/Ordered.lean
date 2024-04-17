/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Order.Invertible
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Tactic.FieldSimp

#align_import linear_algebra.affine_space.ordered from "leanprover-community/mathlib"@"78261225eb5cedc61c5c74ecb44e5b385d13b733"

/-!
# Ordered modules as affine spaces

In this file we prove some theorems about `slope` and `lineMap` in the case when the module `E`
acting on the codomain `PE` of a function is an ordered module over its domain `k`. We also prove
inequalities that can be used to link convexity of a function on an interval to monotonicity of the
slope, see section docstring below for details.

## Implementation notes

We do not introduce the notion of ordered affine spaces (yet?). Instead, we prove various theorems
for an ordered module interpreted as an affine space.

## Tags

affine space, ordered module, slope
-/


open AffineMap

variable {k E PE : Type*}

/-!
### Monotonicity of `lineMap`

In this section we prove that `lineMap a b r` is monotone (strictly or not) in its arguments if
other arguments belong to specific domains.
-/


section OrderedRing

variable [OrderedRing k] [OrderedAddCommGroup E] [Module k E] [OrderedSMul k E]
variable {a a' b b' : E} {r r' : k}

theorem lineMap_mono_left (ha : a ≤ a') (hr : r ≤ 1) : lineMap a b r ≤ lineMap a' b r := by
  simp only [lineMap_apply_module]
  exact add_le_add_right (smul_le_smul_of_nonneg_left ha (sub_nonneg.2 hr)) _
#align line_map_mono_left lineMap_mono_left

theorem lineMap_strict_mono_left (ha : a < a') (hr : r < 1) : lineMap a b r < lineMap a' b r := by
  simp only [lineMap_apply_module]
  exact add_lt_add_right (smul_lt_smul_of_pos_left ha (sub_pos.2 hr)) _
#align line_map_strict_mono_left lineMap_strict_mono_left

theorem lineMap_mono_right (hb : b ≤ b') (hr : 0 ≤ r) : lineMap a b r ≤ lineMap a b' r := by
  simp only [lineMap_apply_module]
  exact add_le_add_left (smul_le_smul_of_nonneg_left hb hr) _
#align line_map_mono_right lineMap_mono_right

theorem lineMap_strict_mono_right (hb : b < b') (hr : 0 < r) : lineMap a b r < lineMap a b' r := by
  simp only [lineMap_apply_module]
  exact add_lt_add_left (smul_lt_smul_of_pos_left hb hr) _
#align line_map_strict_mono_right lineMap_strict_mono_right

theorem lineMap_mono_endpoints (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r ≤ lineMap a' b' r :=
  (lineMap_mono_left ha h₁).trans (lineMap_mono_right hb h₀)
#align line_map_mono_endpoints lineMap_mono_endpoints

theorem lineMap_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r < lineMap a' b' r := by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (lineMap_mono_left ha.le h₁).trans_lt (lineMap_strict_mono_right hb h₀)
#align line_map_strict_mono_endpoints lineMap_strict_mono_endpoints

theorem lineMap_lt_lineMap_iff_of_lt (h : r < r') : lineMap a b r < lineMap a b r' ↔ a < b := by
  simp only [lineMap_apply_module]
  rw [← lt_sub_iff_add_lt, add_sub_assoc, ← sub_lt_iff_lt_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_lt_smul_iff_of_pos_left (sub_pos.2 h)]
#align line_map_lt_line_map_iff_of_lt lineMap_lt_lineMap_iff_of_lt

theorem left_lt_lineMap_iff_lt (h : 0 < r) : a < lineMap a b r ↔ a < b :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_lt_lineMap_iff_of_lt h)
#align left_lt_line_map_iff_lt left_lt_lineMap_iff_lt

theorem lineMap_lt_left_iff_lt (h : 0 < r) : lineMap a b r < a ↔ b < a :=
  left_lt_lineMap_iff_lt (E := Eᵒᵈ) h
#align line_map_lt_left_iff_lt lineMap_lt_left_iff_lt

theorem lineMap_lt_right_iff_lt (h : r < 1) : lineMap a b r < b ↔ a < b :=
  Iff.trans (by rw [lineMap_apply_one]) (lineMap_lt_lineMap_iff_of_lt h)
#align line_map_lt_right_iff_lt lineMap_lt_right_iff_lt

theorem right_lt_lineMap_iff_lt (h : r < 1) : b < lineMap a b r ↔ b < a :=
  lineMap_lt_right_iff_lt (E := Eᵒᵈ) h
#align right_lt_line_map_iff_lt right_lt_lineMap_iff_lt

end OrderedRing

section LinearOrderedRing

variable [LinearOrderedRing k] [OrderedAddCommGroup E] [Module k E] [OrderedSMul k E]
  [Invertible (2 : k)] {a a' b b' : E} {r r' : k}

theorem midpoint_le_midpoint (ha : a ≤ a') (hb : b ≤ b') : midpoint k a b ≤ midpoint k a' b' :=
  lineMap_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) <| invOf_le_one one_le_two
#align midpoint_le_midpoint midpoint_le_midpoint

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField k] [OrderedAddCommGroup E]
variable [Module k E] [OrderedSMul k E]

section

variable {a b : E} {r r' : k}

theorem lineMap_le_lineMap_iff_of_lt (h : r < r') : lineMap a b r ≤ lineMap a b r' ↔ a ≤ b := by
  simp only [lineMap_apply_module]
  rw [← le_sub_iff_add_le, add_sub_assoc, ← sub_le_iff_le_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_le_smul_iff_of_pos_left (sub_pos.2 h)]
#align line_map_le_line_map_iff_of_lt lineMap_le_lineMap_iff_of_lt

theorem left_le_lineMap_iff_le (h : 0 < r) : a ≤ lineMap a b r ↔ a ≤ b :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt h)
#align left_le_line_map_iff_le left_le_lineMap_iff_le

@[simp]
theorem left_le_midpoint : a ≤ midpoint k a b ↔ a ≤ b :=
  left_le_lineMap_iff_le <| inv_pos.2 zero_lt_two
#align left_le_midpoint left_le_midpoint

theorem lineMap_le_left_iff_le (h : 0 < r) : lineMap a b r ≤ a ↔ b ≤ a :=
  left_le_lineMap_iff_le (E := Eᵒᵈ) h
#align line_map_le_left_iff_le lineMap_le_left_iff_le

@[simp]
theorem midpoint_le_left : midpoint k a b ≤ a ↔ b ≤ a :=
  lineMap_le_left_iff_le <| inv_pos.2 zero_lt_two
#align midpoint_le_left midpoint_le_left

theorem lineMap_le_right_iff_le (h : r < 1) : lineMap a b r ≤ b ↔ a ≤ b :=
  Iff.trans (by rw [lineMap_apply_one]) (lineMap_le_lineMap_iff_of_lt h)
#align line_map_le_right_iff_le lineMap_le_right_iff_le

@[simp]
theorem midpoint_le_right : midpoint k a b ≤ b ↔ a ≤ b :=
  lineMap_le_right_iff_le <| inv_lt_one one_lt_two
#align midpoint_le_right midpoint_le_right

theorem right_le_lineMap_iff_le (h : r < 1) : b ≤ lineMap a b r ↔ b ≤ a :=
  lineMap_le_right_iff_le (E := Eᵒᵈ) h
#align right_le_line_map_iff_le right_le_lineMap_iff_le

@[simp]
theorem right_le_midpoint : b ≤ midpoint k a b ↔ b ≤ a :=
  right_le_lineMap_iff_le <| inv_lt_one one_lt_two
#align right_le_midpoint right_le_midpoint

end

/-!
### Convexity and slope

Given an interval `[a, b]` and a point `c ∈ (a, b)`, `c = lineMap a b r`, there are a few ways to
say that the point `(c, f c)` is above/below the segment `[(a, f a), (b, f b)]`:

* compare `f c` to `lineMap (f a) (f b) r`;
* compare `slope f a c` to `slope f a b`;
* compare `slope f c b` to `slope f a b`;
* compare `slope f a c` to `slope f c b`.

In this section we prove equivalence of these four approaches. In order to make the statements more
readable, we introduce local notation `c = lineMap a b r`. Then we prove lemmas like

```
lemma map_le_lineMap_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f a b :=
```

For each inequality between `f c` and `lineMap (f a) (f b) r` we provide 3 lemmas:

* `*_left` relates it to an inequality on `slope f a c` and `slope f a b`;
* `*_right` relates it to an inequality on `slope f a b` and `slope f c b`;
* no-suffix version relates it to an inequality on `slope f a c` and `slope f c b`.

These inequalities can be used to restate `convexOn` in terms of monotonicity of the slope.
-/


variable {f : k → E} {a b r : k}

local notation "c" => lineMap a b r

/-- Given `c = lineMap a b r`, `a < c`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f a b`. -/
theorem map_le_lineMap_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f a b := by
  rw [lineMap_apply, lineMap_apply, slope, slope, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub,
    vadd_eq_add, vadd_eq_add, smul_eq_mul, add_sub_cancel_right, smul_sub, smul_sub, smul_sub,
    sub_le_iff_le_add, mul_inv_rev, mul_smul, mul_smul, ← smul_sub, ← smul_sub, ← smul_add,
    smul_smul, ← mul_inv_rev, inv_smul_le_iff_of_pos h, smul_smul,
    mul_inv_cancel_right₀ (right_ne_zero_of_mul h.ne'), smul_add,
    smul_inv_smul₀ (left_ne_zero_of_mul h.ne')]
#align map_le_line_map_iff_slope_le_slope_left map_le_lineMap_iff_slope_le_slope_left

/-- Given `c = lineMap a b r`, `a < c`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f a c`. -/
theorem lineMap_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f a b ≤ slope f a c :=
  map_le_lineMap_iff_slope_le_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h
#align line_map_le_map_iff_slope_le_slope_left lineMap_le_map_iff_slope_le_slope_left

/-- Given `c = lineMap a b r`, `a < c`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f a b`. -/
theorem map_lt_lineMap_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
    f c < lineMap (f a) (f b) r ↔ slope f a c < slope f a b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_left h)
    (map_le_lineMap_iff_slope_le_slope_left h)
#align map_lt_line_map_iff_slope_lt_slope_left map_lt_lineMap_iff_slope_lt_slope_left

/-- Given `c = lineMap a b r`, `a < c`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f a c`. -/
theorem lineMap_lt_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r < f c ↔ slope f a b < slope f a c :=
  map_lt_lineMap_iff_slope_lt_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h
#align line_map_lt_map_iff_slope_lt_slope_left lineMap_lt_map_iff_slope_lt_slope_left

/-- Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f c b`. -/
theorem map_le_lineMap_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a b ≤ slope f c b := by
  rw [← lineMap_apply_one_sub, ← lineMap_apply_one_sub _ _ r]
  revert h; generalize 1 - r = r'; clear! r; intro h
  simp_rw [lineMap_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  rw [sub_add_eq_sub_sub_swap, sub_self, zero_sub, neg_mul_eq_mul_neg, neg_sub,
    le_inv_smul_iff_of_pos h, smul_smul, mul_inv_cancel_right₀, le_sub_comm, ← neg_sub (f b),
    smul_neg, neg_add_eq_sub]
  · exact right_ne_zero_of_mul h.ne'
#align map_le_line_map_iff_slope_le_slope_right map_le_lineMap_iff_slope_le_slope_right

/-- Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a b`. -/
theorem lineMap_le_map_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a b :=
  map_le_lineMap_iff_slope_le_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h
#align line_map_le_map_iff_slope_le_slope_right lineMap_le_map_iff_slope_le_slope_right

/-- Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f c b`. -/
theorem map_lt_lineMap_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
    f c < lineMap (f a) (f b) r ↔ slope f a b < slope f c b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_right h)
    (map_le_lineMap_iff_slope_le_slope_right h)
#align map_lt_line_map_iff_slope_lt_slope_right map_lt_lineMap_iff_slope_lt_slope_right

/-- Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a b`. -/
theorem lineMap_lt_map_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a b :=
  map_lt_lineMap_iff_slope_lt_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h
#align line_map_lt_map_iff_slope_lt_slope_right lineMap_lt_map_iff_slope_lt_slope_right

/-- Given `c = lineMap a b r`, `a < c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f c b`. -/
theorem map_le_lineMap_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f c b := by
  rw [map_le_lineMap_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab)), ←
    lineMap_slope_lineMap_slope_lineMap f a b r, right_le_lineMap_iff_le h₁]
#align map_le_line_map_iff_slope_le_slope map_le_lineMap_iff_slope_le_slope

/-- Given `c = lineMap a b r`, `a < c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a c`. -/
theorem lineMap_le_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a c :=
  map_le_lineMap_iff_slope_le_slope (E := Eᵒᵈ) hab h₀ h₁
#align line_map_le_map_iff_slope_le_slope lineMap_le_map_iff_slope_le_slope

/-- Given `c = lineMap a b r`, `a < c < b`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f c b`. -/
theorem map_lt_lineMap_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    f c < lineMap (f a) (f b) r ↔ slope f a c < slope f c b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope hab h₀ h₁)
    (map_le_lineMap_iff_slope_le_slope hab h₀ h₁)
#align map_lt_line_map_iff_slope_lt_slope map_lt_lineMap_iff_slope_lt_slope

/-- Given `c = lineMap a b r`, `a < c < b`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a c`. -/
theorem lineMap_lt_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a c :=
  map_lt_lineMap_iff_slope_lt_slope (E := Eᵒᵈ) hab h₀ h₁
#align line_map_lt_map_iff_slope_lt_slope lineMap_lt_map_iff_slope_lt_slope

end LinearOrderedField
