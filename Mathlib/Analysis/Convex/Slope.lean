/-
Copyright (c) 2021 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Malo Jaffré
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

#align_import analysis.convex.slope from "leanprover-community/mathlib"@"a8b2226cfb0a79f5986492053fc49b1a0c6aeffb"

/-!
# Slopes of convex functions

This file relates convexity/concavity of functions in a linearly ordered field and the monotonicity
of their slopes.

The main use is to show convexity/concavity from monotonicity of the derivative.
-/

variable {𝕜 : Type*} [LinearOrderedField 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜}

#adaptation_note /-- after v4.7.0-rc1, there is a performance problem in `field_simp`.
(Part of the code was ignoring the `maxDischargeDepth` setting:
 now that we have to increase it, other paths become slow.) -/
/-- If `f : 𝕜 → 𝕜` is convex, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
theorem ConvexOn.slope_mono_adjacent (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) := by
  have hxz := hxy.trans hyz
  rw [← sub_pos] at hxy hxz hyz
  suffices f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y) by
    ring_nf at this ⊢
    linarith
  set a := (z - y) / (z - x)
  set b := (y - x) / (z - x)
  have hy : a • x + b • z = y := by field_simp [a, b]; ring
  have key :=
    hf.2 hx hz (show 0 ≤ a by apply div_nonneg <;> linarith)
      (show 0 ≤ b by apply div_nonneg <;> linarith)
      (show a + b = 1 by field_simp [a, b])
  rw [hy] at key
  replace key := mul_le_mul_of_nonneg_left key hxz.le
  field_simp [a, b, mul_comm (z - x) _] at key ⊢
  rw [div_le_div_right]
  · linarith
  · nlinarith
#align convex_on.slope_mono_adjacent ConvexOn.slope_mono_adjacent

/-- If `f : 𝕜 → 𝕜` is concave, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
theorem ConcaveOn.slope_anti_adjacent (hf : ConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) := by
  have := neg_le_neg (ConvexOn.slope_mono_adjacent hf.neg hx hz hxy hyz)
  simp only [Pi.neg_apply, ← neg_div, neg_sub', neg_neg] at this
  exact this
#align concave_on.slope_anti_adjacent ConcaveOn.slope_anti_adjacent

/-- If `f : 𝕜 → 𝕜` is strictly convex, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
theorem StrictConvexOn.slope_strict_mono_adjacent (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜}
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
    (f y - f x) / (y - x) < (f z - f y) / (z - y) := by
  have hxz := hxy.trans hyz
  have hxz' := hxz.ne
  rw [← sub_pos] at hxy hxz hyz
  suffices f y / (y - x) + f y / (z - y) < f x / (y - x) + f z / (z - y) by
    ring_nf at this ⊢
    linarith
  set a := (z - y) / (z - x)
  set b := (y - x) / (z - x)
  have hy : a • x + b • z = y := by field_simp [a, b]; ring
  have key :=
    hf.2 hx hz hxz' (div_pos hyz hxz) (div_pos hxy hxz)
      (show a + b = 1 by field_simp [a, b])
  rw [hy] at key
  replace key := mul_lt_mul_of_pos_left key hxz
  field_simp [mul_comm (z - x) _] at key ⊢
  rw [div_lt_div_right]
  · linarith
  · nlinarith
#align strict_convex_on.slope_strict_mono_adjacent StrictConvexOn.slope_strict_mono_adjacent

/-- If `f : 𝕜 → 𝕜` is strictly concave, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
theorem StrictConcaveOn.slope_anti_adjacent (hf : StrictConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) < (f y - f x) / (y - x) := by
  have := neg_lt_neg (StrictConvexOn.slope_strict_mono_adjacent hf.neg hx hz hxy hyz)
  simp only [Pi.neg_apply, ← neg_div, neg_sub', neg_neg] at this
  exact this
#align strict_concave_on.slope_anti_adjacent StrictConcaveOn.slope_anti_adjacent

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
less than the slope of the secant line of `f` on `[x, z]`, then `f` is convex. -/
theorem convexOn_of_slope_mono_adjacent (hs : Convex 𝕜 s)
    (hf :
      ∀ {x y z : 𝕜},
        x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
    ConvexOn 𝕜 s f :=
  LinearOrder.convexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    let y := a * x + b * z
    have hxy : x < y := by
      rw [← one_mul x, ← hab, add_mul]
      exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _
    have hyz : y < z := by
      rw [← one_mul z, ← hab, add_mul]
      exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _
    have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x) :=
      (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz)
    have hxz : 0 < z - x := sub_pos.2 (hxy.trans hyz)
    have ha : (z - y) / (z - x) = a := by
      rw [eq_comm, ← sub_eq_iff_eq_add'] at hab
      dsimp [y]
      simp_rw [div_eq_iff hxz.ne', ← hab]
      ring
    have hb : (y - x) / (z - x) = b := by
      rw [eq_comm, ← sub_eq_iff_eq_add] at hab
      dsimp [y]
      simp_rw [div_eq_iff hxz.ne', ← hab]
      ring
    rwa [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_add,
      sub_add_sub_cancel, ← le_div_iff hxz, add_div, mul_div_assoc, mul_div_assoc, mul_comm (f x),
      mul_comm (f z), ha, hb] at this
#align convex_on_of_slope_mono_adjacent convexOn_of_slope_mono_adjacent

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
greater than the slope of the secant line of `f` on `[x, z]`, then `f` is concave. -/
theorem concaveOn_of_slope_anti_adjacent (hs : Convex 𝕜 s)
    (hf :
      ∀ {x y z : 𝕜},
        x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :
    ConcaveOn 𝕜 s f := by
  rw [← neg_convexOn_iff]
  refine convexOn_of_slope_mono_adjacent hs fun hx hz hxy hyz => ?_
  rw [← neg_le_neg_iff]
  simp_rw [← neg_div, neg_sub, Pi.neg_apply, neg_sub_neg]
  exact hf hx hz hxy hyz
#align concave_on_of_slope_anti_adjacent concaveOn_of_slope_anti_adjacent

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly less than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly convex. -/
theorem strictConvexOn_of_slope_strict_mono_adjacent (hs : Convex 𝕜 s)
    (hf :
      ∀ {x y z : 𝕜},
        x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) < (f z - f y) / (z - y)) :
    StrictConvexOn 𝕜 s f :=
  LinearOrder.strictConvexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    let y := a * x + b * z
    have hxy : x < y := by
      rw [← one_mul x, ← hab, add_mul]
      exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _
    have hyz : y < z := by
      rw [← one_mul z, ← hab, add_mul]
      exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _
    have : (f y - f x) * (z - y) < (f z - f y) * (y - x) :=
      (div_lt_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz)
    have hxz : 0 < z - x := sub_pos.2 (hxy.trans hyz)
    have ha : (z - y) / (z - x) = a := by
      rw [eq_comm, ← sub_eq_iff_eq_add'] at hab
      dsimp [y]
      simp_rw [div_eq_iff hxz.ne', ← hab]
      ring
    have hb : (y - x) / (z - x) = b := by
      rw [eq_comm, ← sub_eq_iff_eq_add] at hab
      dsimp [y]
      simp_rw [div_eq_iff hxz.ne', ← hab]
      ring
    rwa [sub_mul, sub_mul, sub_lt_iff_lt_add', ← add_sub_assoc, lt_sub_iff_add_lt, ← mul_add,
      sub_add_sub_cancel, ← lt_div_iff hxz, add_div, mul_div_assoc, mul_div_assoc, mul_comm (f x),
      mul_comm (f z), ha, hb] at this
#align strict_convex_on_of_slope_strict_mono_adjacent strictConvexOn_of_slope_strict_mono_adjacent

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly greater than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly concave.
-/
theorem strictConcaveOn_of_slope_strict_anti_adjacent (hs : Convex 𝕜 s)
    (hf :
      ∀ {x y z : 𝕜},
        x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) < (f y - f x) / (y - x)) :
    StrictConcaveOn 𝕜 s f := by
  rw [← neg_strictConvexOn_iff]
  refine strictConvexOn_of_slope_strict_mono_adjacent hs fun hx hz hxy hyz => ?_
  rw [← neg_lt_neg_iff]
  simp_rw [← neg_div, neg_sub, Pi.neg_apply, neg_sub_neg]
  exact hf hx hz hxy hyz
#align strict_concave_on_of_slope_strict_anti_adjacent strictConcaveOn_of_slope_strict_anti_adjacent

/-- A function `f : 𝕜 → 𝕜` is convex iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
theorem convexOn_iff_slope_mono_adjacent :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄,
          x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_mono_adjacent⟩, fun h =>
    convexOn_of_slope_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩
#align convex_on_iff_slope_mono_adjacent convexOn_iff_slope_mono_adjacent

/-- A function `f : 𝕜 → 𝕜` is concave iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
theorem concaveOn_iff_slope_anti_adjacent :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y z : 𝕜⦄,
          x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    concaveOn_of_slope_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩
#align concave_on_iff_slope_anti_adjacent concaveOn_iff_slope_anti_adjacent

/-- A function `f : 𝕜 → 𝕜` is strictly convex iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strictConvexOn_iff_slope_strict_mono_adjacent :
    StrictConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y z : 𝕜⦄,
          x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) < (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_strict_mono_adjacent⟩, fun h =>
    strictConvexOn_of_slope_strict_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩
#align strict_convex_on_iff_slope_strict_mono_adjacent strictConvexOn_iff_slope_strict_mono_adjacent

/-- A function `f : 𝕜 → 𝕜` is strictly concave iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strictConcaveOn_iff_slope_strict_anti_adjacent :
    StrictConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y z : 𝕜⦄,
          x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.1, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    strictConcaveOn_of_slope_strict_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩
#align strict_concave_on_iff_slope_strict_anti_adjacent strictConcaveOn_iff_slope_strict_anti_adjacent

theorem ConvexOn.secant_mono_aux1 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (z - x) * f y ≤ (z - y) * f x + (y - x) * f z := by
  have hxy' : 0 < y - x := by linarith
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  rw [← le_div_iff' hxz']
  have ha : 0 ≤ (z - y) / (z - x) := by positivity
  have hb : 0 ≤ (y - x) / (z - x) := by positivity
  calc
    f y = f ((z - y) / (z - x) * x + (y - x) / (z - x) * z) := ?_
    _ ≤ (z - y) / (z - x) * f x + (y - x) / (z - x) * f z := hf.2 hx hz ha hb ?_
    _ = ((z - y) * f x + (y - x) * f z) / (z - x) := ?_
  · congr 1
    field_simp
    ring
  · -- Porting note: this `show` wasn't needed in Lean 3
    show (z - y) / (z - x) + (y - x) / (z - x) = 1
    field_simp
  · field_simp
#align convex_on.secant_mono_aux1 ConvexOn.secant_mono_aux1

theorem ConvexOn.secant_mono_aux2 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) ≤ (f z - f x) / (z - x) := by
  have hxy' : 0 < y - x := by linarith
  have hxz' : 0 < z - x := by linarith
  rw [div_le_div_iff hxy' hxz']
  linarith only [hf.secant_mono_aux1 hx hz hxy hyz]
#align convex_on.secant_mono_aux2 ConvexOn.secant_mono_aux2

theorem ConvexOn.secant_mono_aux3 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (f z - f x) / (z - x) ≤ (f z - f y) / (z - y) := by
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  rw [div_le_div_iff hxz' hyz']
  linarith only [hf.secant_mono_aux1 hx hz hxy hyz]
#align convex_on.secant_mono_aux3 ConvexOn.secant_mono_aux3

theorem ConvexOn.secant_mono (hf : ConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a ∈ s) (hx : x ∈ s)
    (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x ≤ y) :
    (f x - f a) / (x - a) ≤ (f y - f a) / (y - a) := by
  rcases eq_or_lt_of_le hxy with (rfl | hxy)
  · simp
  cases' lt_or_gt_of_ne hxa with hxa hxa
  · cases' lt_or_gt_of_ne hya with hya hya
    · convert hf.secant_mono_aux3 hx ha hxy hya using 1 <;> rw [← neg_div_neg_eq] <;> field_simp
    · convert hf.slope_mono_adjacent hx hy hxa hya using 1
      rw [← neg_div_neg_eq]; field_simp
  · exact hf.secant_mono_aux2 ha hy hxa hxy
#align convex_on.secant_mono ConvexOn.secant_mono

theorem StrictConvexOn.secant_strict_mono_aux1 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) : (z - x) * f y < (z - y) * f x + (y - x) * f z := by
  have hxy' : 0 < y - x := by linarith
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  rw [← lt_div_iff' hxz']
  have ha : 0 < (z - y) / (z - x) := by positivity
  have hb : 0 < (y - x) / (z - x) := by positivity
  calc
    f y = f ((z - y) / (z - x) * x + (y - x) / (z - x) * z) := ?_
    _ < (z - y) / (z - x) * f x + (y - x) / (z - x) * f z := hf.2 hx hz (by linarith) ha hb ?_
    _ = ((z - y) * f x + (y - x) * f z) / (z - x) := ?_
  · congr 1
    field_simp
    ring
  · -- Porting note: this `show` wasn't needed in Lean 3
    show (z - y) / (z - x) + (y - x) / (z - x) = 1
    field_simp
  · field_simp
#align strict_convex_on.secant_strict_mono_aux1 StrictConvexOn.secant_strict_mono_aux1

theorem StrictConvexOn.secant_strict_mono_aux2 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) < (f z - f x) / (z - x) := by
  have hxy' : 0 < y - x := by linarith
  have hxz' : 0 < z - x := by linarith
  rw [div_lt_div_iff hxy' hxz']
  linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz]
#align strict_convex_on.secant_strict_mono_aux2 StrictConvexOn.secant_strict_mono_aux2

theorem StrictConvexOn.secant_strict_mono_aux3 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) : (f z - f x) / (z - x) < (f z - f y) / (z - y) := by
  have hyz' : 0 < z - y := by linarith
  have hxz' : 0 < z - x := by linarith
  rw [div_lt_div_iff hxz' hyz']
  linarith only [hf.secant_strict_mono_aux1 hx hz hxy hyz]
#align strict_convex_on.secant_strict_mono_aux3 StrictConvexOn.secant_strict_mono_aux3

theorem StrictConvexOn.secant_strict_mono (hf : StrictConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a ∈ s)
    (hx : x ∈ s) (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x < y) :
    (f x - f a) / (x - a) < (f y - f a) / (y - a) := by
  cases' lt_or_gt_of_ne hxa with hxa hxa
  · cases' lt_or_gt_of_ne hya with hya hya
    · convert hf.secant_strict_mono_aux3 hx ha hxy hya using 1 <;> rw [← neg_div_neg_eq] <;>
        field_simp
    · convert hf.slope_strict_mono_adjacent hx hy hxa hya using 1
      rw [← neg_div_neg_eq]; field_simp
  · exact hf.secant_strict_mono_aux2 ha hy hxa hxy
#align strict_convex_on.secant_strict_mono StrictConvexOn.secant_strict_mono

theorem StrictConcaveOn.secant_strict_mono (hf : StrictConcaveOn 𝕜 s f) {a x y : 𝕜} (ha : a ∈ s)
    (hx : x ∈ s) (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x < y) :
    (f y - f a) / (y - a) < (f x - f a) / (x - a) := by
  have key := hf.neg.secant_strict_mono ha hx hy hxa hya hxy
  simp only [Pi.neg_apply] at key
  rw [← neg_lt_neg_iff]
  convert key using 1 <;> field_simp <;> ring
#align strict_concave_on.secant_strict_mono StrictConcaveOn.secant_strict_mono

/-- If `f` is convex on a set `s` in a linearly ordered field, and `f x < f y` for two points
`x < y` in `s`, then `f` is strictly monotone on `s ∩ [y, ∞)`. -/
theorem ConvexOn.strict_mono_of_lt (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hx : x ∈ s) (hxy : x < y)
    (hxy' : f x < f y) : StrictMonoOn f (s ∩ Set.Ici y) := by
  intro u hu v hv huv
  have step1 : ∀ {z : 𝕜}, z ∈ s ∩ Set.Ioi y → f y < f z := by
    intros z hz
    refine hf.lt_right_of_left_lt hx hz.1 ?_ hxy'
    rw [openSegment_eq_Ioo (hxy.trans hz.2)]
    exact ⟨hxy, hz.2⟩
  rcases eq_or_lt_of_le hu.2 with (rfl | hu2)
  · exact step1 ⟨hv.1, huv⟩
  · refine hf.lt_right_of_left_lt ?_ hv.1 ?_ (step1 ⟨hu.1, hu2⟩)
    · apply hf.1.segment_subset hx hu.1
      rw [segment_eq_Icc (hxy.le.trans hu.2)]
      exact ⟨hxy.le, hu.2⟩
    · rw [openSegment_eq_Ioo (hu2.trans huv)]
      exact ⟨hu2, huv⟩
#align convex_on.strict_mono_of_lt ConvexOn.strict_mono_of_lt
