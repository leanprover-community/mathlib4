/-
Copyright (c) 2024 Ian Jauslin and Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Jauslin, Alex Kontorovich
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# Primitives of Holomorphic Functions

In this file, we give conditions under which holomorphic functions have primitives. The main goal
is to prove that holomorphic functions on simply connected domains have primitives. As a first step,
we prove that holomorphic functions on discs have primitives. The approach is based on Moreira's
theorem, that a continuous function (on a disc) whose `RectangleIntegral` vanishes on all
rectangles contained in the disc has a primitive. (Coupled with the fact that holomorphic functions
satisfy this propoerty.) To prove Moreira's theorem, we first define the `WedgeInt`, which is the
integral of a function over a "wedge" (a horizontal segment followed by a vertical segment in the
disc), and compute its derivative.

## Main results

* `VanishesOnRectanglesInDisc.diff_of_wedges`: If a function `f` vanishes on all rectangles in a
  disc with center `c`, then the wedge integral from `c` to `w` minus the wedge integral from
  `c` to `z` is equal to the wedge integral from `z` to `w`.

* `deriv_of_wedgeInt`: The derivative of the wedge integral is the function being integrated.

* `VanishesOnRectanglesInDisc.hasPrimitive`: **Moreira's Theorem**: A function which is 
  continuous on a disc and whose integral on rectangles in the disc vanishes has a primitive
  on the disc (defined by the wedge integral).

* `hasPrimitives_on_disc`: A holomorphic function on a disc has primitives.

## Tags
  Holomorphic functions, primitives

TODO: Extend to holomorphic functions on simply connected domains. (In particular, this allows one
to define the complex logarithm of a nonvanishing function on a simply connected domain.)
-/

open Complex Topology Set Metric

set_option autoImplicit true

open scoped Interval

namespace Complex

section Asymptotics

/-- As `w → z`, `w.re - z.re` is big-O of `w - z`. -/
lemma re_isBigO {z : ℂ} : (fun (w : ℂ) ↦ w.re - z.re) =O[𝓝 z] fun w ↦ w - z := by
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp only [Real.norm_eq_abs, Complex.norm_eq_abs, one_mul]
  rw [← Complex.sub_re]
  exact Complex.abs_re_le_abs (w - z)

/-- As `w → z`, `w.im - z.im` is big-O of `w - z`. -/
lemma im_isBigO {z : ℂ} : (fun (w : ℂ) ↦ w.im - z.im) =O[𝓝 z] fun w ↦ w - z := by
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp only [Real.norm_eq_abs, Complex.norm_eq_abs, one_mul]
  rw [← Complex.sub_im]
  exact Complex.abs_im_le_abs (w - z)

end Asymptotics

section reProdIm

/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  rw [← @preimage_equivRealProd_prod s t, ← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert prod_subset_prod_iff
  exact reProdIm_subset_iff

end reProdIm

section Rectangle

/-- A `Rectangle` is an axis-parallel rectangle with corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. -/
lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair,
    insert_union, ← insert_eq, preimage_equiv_eq_image_symm, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. -/
lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  rw [Rectangle, segment_reProdIm_segment_eq_convexHull]
  convert convexHull_min ?_ (U_convex)
  refine insert_subset hz (insert_subset hzw (insert_subset hwz ?_))
  exact singleton_subset_iff.mpr hw

/-- If `z` is in a ball centered at `c`, then `z.re + c.im * I` is in the ball. -/
lemma cornerRectangle_in_disc {c : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ ball c r) :
    z.re + c.im * I ∈ ball c r := by
  simp only [mem_ball] at hz ⊢
  rw [dist_of_im_eq] <;> simp only [add_re, I_re, mul_zero, I_im, zero_add, add_im,
    add_zero, sub_self, mul_re, mul_one, ofReal_im, mul_im, ofReal_re]
  apply lt_of_le_of_lt ?_ hz
  rw [dist_eq_re_im, Real.dist_eq]
  apply Real.le_sqrt_of_sq_le
  simp only [_root_.sq_abs, le_add_iff_nonneg_right, ge_iff_le, sub_nonneg]
  exact sq_nonneg _

end Rectangle

section Segments

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment. -/
lemma horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

/-- A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment. -/
lemma verticalSegment_eq (a b₁ b₂ : ℝ) :
    (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] = {a} ×ℂ [[b₁, b₂]] := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

end Segments

section SubsetBall_Aux

/- Auxiliary lemmata about subsets of balls -/

lemma mem_ball_re_aux {c : ℂ} {r : ℝ} {z : ℂ} :
    (Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) ×ℂ {z.im} ⊆ ball z (r - dist z c) := by
  intro x hx
  obtain ⟨xRe, xIm⟩ := hx
  simp only [mem_preimage, mem_singleton_iff, mem_Ioo] at xRe xIm
  simp only [mem_ball]
  rw [dist_eq_re_im, xIm]
  simp only [sub_self, ne_eq, not_false_eq_true, zero_pow', add_zero, Real.sqrt_sq_eq_abs, abs_lt]
  refine ⟨by linarith, by linarith⟩

lemma mem_ball_re_aux' {c : ℂ} {r : ℝ} {z : ℂ} {x : ℝ}
    (hx : x ∈ Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) :
    x + z.im * I ∈ ball c r := by
  set r₁ := r - dist z c
  set s := Ioo (z.re - r₁) (z.re + r₁)
  have s_ball₁ : s ×ℂ {z.im} ⊆ ball z r₁ := mem_ball_re_aux
  have s_ball : s ×ℂ {z.im} ⊆ ball c r := s_ball₁.trans (by apply ball_subset_ball'; simp)
  apply s_ball
  rw [mem_reProdIm]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, gt_iff_lt, not_lt, ge_iff_le, mem_Ioo, add_im, mul_im, zero_add, mem_singleton_iff,
    and_true]
  apply hx

lemma mem_closedBall_aux {c : ℂ} {r : ℝ} {z : ℂ} (z_in_ball : z ∈ closedBall c r)
    {y : ℝ} (y_in_I : y ∈ Ι c.im z.im) : z.re + y * I ∈ closedBall c r := by
  rw [mem_closedBall] at z_in_ball ⊢
  rw [mem_uIoc] at y_in_I
  apply le_trans ?_ z_in_ball
  rw [dist_eq_re_im, dist_eq_re_im]
  apply Real.le_sqrt_of_sq_le
  rw [Real.sq_sqrt (by positivity)]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, add_le_add_iff_left]
  cases y_in_I <;> nlinarith

lemma mem_ball_of_map_re_aux {c : ℂ} {r : ℝ} {a₁ a₂ b : ℝ} (ha₁ : a₁ + b * I ∈ ball c r)
    (ha₂ : a₂ + b * I ∈ ball c r) : (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] ⊆ ball c r := by
  convert rectangle_in_convex (convex_ball c r) ha₁ ha₂ ?_ ?_ using 1 <;>
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, ha₁, ha₂, Rectangle]
  simp [horizontalSegment_eq a₁ a₂ b]

lemma mem_ball_of_map_im_aux {c : ℂ} {r : ℝ} {a b₁ b₂ : ℝ} (hb₁ : a + b₁ * I ∈ ball c r)
    (hb₂ : a + b₂ * I ∈ ball c r) : (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] ⊆ ball c r := by
  convert rectangle_in_convex (convex_ball c r) hb₁ hb₂ ?_ ?_ using 1 <;>
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, hb₁, hb₂, Rectangle]
  simp [verticalSegment_eq a b₁ b₂]
-- NOTE: I don't know why these `simp`s can't be combined.

lemma mem_ball_of_map_im_aux' {c : ℂ} {r : ℝ} {z : ℂ} {w : ℂ} (hw : w ∈ ball z (r - dist z c)) :
    (fun (y : ℝ) ↦ w.re + y * I) '' [[z.im, w.im]] ⊆ ball c r := by
  apply mem_ball_of_map_im_aux <;>
  apply mem_of_subset_of_mem (ball_subset_ball' (by simp) : ball z (r - dist z c) ⊆ ball c r)
  · exact cornerRectangle_in_disc hw
  · convert hw; simp

end SubsetBall_Aux

end Complex

section ContinuousOn_Aux
/- Auxiliary lemmata about continuity of various occurring functions -/

variable {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f (ball c r))

lemma ContinuousOn.re_aux_1 {z : ℂ} :
    ContinuousOn (fun (x : ℝ) ↦ f (x + z.im * I))
      (Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) := by
  apply (hf.comp ((continuous_add_right _).comp continuous_ofReal).continuousOn)
  intro x hx
  change x + z.im * I ∈ ball c r
  exact mem_ball_re_aux' hx

lemma ContinuousOn.re_aux_2 {a₁ a₂ b : ℝ} (ha₁ : a₁ + b * I ∈ ball c r)
    (ha₂ : a₂ + b * I ∈ ball c r) : ContinuousOn (fun (x : ℝ) ↦ f (x + b * I)) [[a₁, a₂]] := by
  convert ContinuousOn.comp (g := f) (f := fun (x : ℝ) ↦ (x : ℂ) + b * I) (s := uIcc a₁ a₂)
    (t := (fun (x : ℝ) ↦ (x : ℂ) + b * I) '' (uIcc a₁ a₂)) ?_ ?_ (mapsTo_image _ _)
  · apply hf.mono (mem_ball_of_map_re_aux ha₁ ha₂)
  · exact Continuous.continuousOn (Continuous.comp (continuous_add_right _) continuous_ofReal)

lemma ContinuousOn.im_aux_1 {z : ℂ} {w : ℂ} (hw : w ∈ ball z (r - dist z c)) :
    ContinuousOn (fun (y : ℝ) ↦ f (w.re + y * I)) [[z.im, w.im]] := by
  convert ContinuousOn.comp (g := f) (f := fun (y : ℝ) ↦ (w.re : ℂ) + y * I) (s := uIcc z.im w.im)
    (t := (fun (y : ℝ) ↦ (w.re : ℂ) + y * I) '' (uIcc z.im w.im)) ?_ ?_ (mapsTo_image _ _)
  · apply hf.mono (mem_ball_of_map_im_aux' hw)
  · apply Continuous.continuousOn
    exact ((continuous_add_left _).comp (continuous_mul_right _)).comp continuous_ofReal

lemma ContinuousOn.im_aux {a b₁ b₂ : ℝ} (hb₁ : a + b₁ * I ∈ ball c r)
    (hb₂ : a + b₂ * I ∈ ball c r) : ContinuousOn (fun (y : ℝ) ↦ f (a + y * I)) [[b₁, b₂]] := by
  convert ContinuousOn.comp (g := f) (f := fun (y : ℝ) ↦ (a : ℂ) + y * I) (s := uIcc b₁ b₂)
    (t := (fun (y : ℝ) ↦ (a : ℂ) + y * I) '' (uIcc b₁ b₂)) ?_ ?_ (mapsTo_image _ _)
  · apply hf.mono (mem_ball_of_map_im_aux hb₁ hb₂)
  · apply Continuous.continuousOn
    exact ((continuous_add_left _).comp (continuous_mul_right _)).comp continuous_ofReal

end ContinuousOn_Aux

namespace Complex

section MainDefinitions

/-- A set `U` `HasPrimitives` if, every holomorphic function on `U` has a primitive -/
def HasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn f U → ∃ g : ℂ → ℂ, ∀ z ∈ U, HasDerivAt g (f z) z

/-- The wedge integral from `z` to `w` of a function `f` -/
noncomputable def WedgeInt (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))

/-- A `RectangleIntegral` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

/-- A function `f` `VanishesOnRectanglesInDisc` if, for any rectangle contained in a disc,
  the integral of `f` over the rectangle is zero. -/
def VanishesOnRectanglesInDisc (c : ℂ) (r : ℝ) (f : ℂ → ℂ) : Prop :=
    ∀ z w, z ∈ ball c r → w ∈ ball c r → (z.re + w.im * I) ∈ ball c r →
    (w.re + z.im * I) ∈ ball c r → RectangleIntegral f z w = 0

end MainDefinitions

section WedgeIntDeriv

variable {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (f_cont : ContinuousOn f (ball c r)) {z : ℂ}
  (hz : z ∈ ball c r)

/-- If a function `f` `VanishesOnRectanglesInDisc` of center `c`, then, for all `w` in a
  neighborhood of `z`, the wedge integral from `c` to `w` minus the wedge integral from `c` to `z`
  is equal to the wedge integral from `z` to `w`. -/
lemma VanishesOnRectanglesInDisc.diff_of_wedges (hf : VanishesOnRectanglesInDisc c r f) :
    ∀ᶠ (w : ℂ) in 𝓝 z,
      WedgeInt c w f - WedgeInt c z f = WedgeInt z w f := by
  have hr : 0 < r := pos_of_mem_ball hz
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simp only [mem_ball, gt_iff_lt] at hz ⊢; linarith
  have z_ball : ball z r₁ ⊆ ball c r := ball_subset_ball' (by simp)
  filter_upwards [ball_mem_nhds z r₁_pos]
  intro w w_in_z_ball
  have hzPlusH : w ∈ ball c r := mem_of_subset_of_mem z_ball w_in_z_ball
  simp only [WedgeInt]
  set intI := ∫ x : ℝ in c.re..(w).re, f (x + c.im * I)
  set intII := I • ∫ y : ℝ in c.im..w.im, f (w.re + y * I)
  set intIII := ∫ x : ℝ in c.re..z.re, f (x + c.im * I)
  set intIV := I • ∫ y : ℝ in c.im..z.im, f (z.re + y * I)
  set intV := ∫ x : ℝ in z.re..w.re, f (x + z.im * I)
  set intVI := I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I)
  let intVII := ∫ x : ℝ in z.re..w.re, f (x + c.im * I)
  let intVIII := I • ∫ y : ℝ in c.im..z.im, f (w.re + y * I)
  have integrableHoriz : ∀ a₁ a₂ b : ℝ, a₁ + b * I ∈ ball c r → a₂ + b * I ∈ ball c r
    → IntervalIntegrable (fun x ↦ f (x + b * I)) MeasureTheory.volume a₁ a₂ :=
      fun a₁ a₂ b ha₁ ha₂ ↦
        ContinuousOn.intervalIntegrable (f_cont.re_aux_2 ha₁ ha₂)
  have integrableVert : ∀ a b₁ b₂ : ℝ, a + b₁ * I ∈ ball c r → a + b₂ * I ∈ ball c r
    → IntervalIntegrable (fun y ↦ f (a + y * I)) MeasureTheory.volume b₁ b₂
  · intro a b₁ b₂ hb₁ hb₂
    apply ContinuousOn.intervalIntegrable (f_cont.im_aux hb₁ hb₂)
  have intIdecomp : intI = intIII + intVII
  · rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
    · simp only [re_add_im, mem_ball, dist_self, hr]
    · exact cornerRectangle_in_disc hz
    · exact cornerRectangle_in_disc hz
    · exact cornerRectangle_in_disc hzPlusH
  have intIIdecomp : intII = intVIII + intVI
  · rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · exact cornerRectangle_in_disc hzPlusH
    · apply mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
    · apply mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
    · convert hzPlusH; simp
  have rectZero : intVIII = - intVII + intV + intIV
  · rw [← sub_eq_zero]
    have : intVII - intV + intVIII - intIV = 0 := by
      have wzInBall : w.re + z.im * I ∈ ball c r :=
        by exact mem_of_subset_of_mem z_ball (cornerRectangle_in_disc w_in_z_ball)
      have wcInBall : w.re + c.im * I ∈ ball c r := cornerRectangle_in_disc hzPlusH
      convert hf (z.re + c.im * I) (w.re + z.im * I) (cornerRectangle_in_disc hz) wzInBall
          (by simpa using hz) (by simpa using wcInBall) using 1
      rw [RectangleIntegral]
      congr <;> simp
    rw [← this]
    ring
  rw [intIdecomp, intIIdecomp, rectZero]
  ring

/-- The integral of a continuous function `f` from `z` to `x + z.im * I` is equal to
  `(x - z.re) * f z` up to `o(x - z.re)`. -/
lemma deriv_of_wedgeInt_re' : (fun (x : ℝ) ↦ (∫ t in z.re..x, f (t + z.im * I)) - (x - z.re) * f z)
    =o[𝓝 z.re] (fun (x : ℝ)  ↦ x - z.re) := by
  let r₁ := r - dist z c
  let s : Set ℝ := Ioo (z.re - r₁) (z.re + r₁)
  have zRe_mem_s : z.re ∈ s := by simp [mem_ball.mp hz]
  have s_open : IsOpen s := isOpen_Ioo
  have f_contOn : ContinuousOn (fun (x : ℝ) ↦ f (x + z.im * I)) s := f_cont.re_aux_1
  have int1 : IntervalIntegrable (fun (x : ℝ) ↦ f (x + z.im * I)) MeasureTheory.volume z.re z.re
  · apply ContinuousOn.intervalIntegrable
    apply f_contOn.mono
    simp [mem_ball.mp hz]
  have int2 : StronglyMeasurableAtFilter (fun (x : ℝ) ↦ f (x + z.im * I)) (𝓝 z.re) :=
    ContinuousOn.stronglyMeasurableAtFilter s_open f_contOn _ zRe_mem_s
  have int3 : ContinuousAt (fun (x : ℝ) ↦ f (x + z.im * I)) z.re :=
    s_open.continuousOn_iff.mp f_contOn zRe_mem_s
  have := @intervalIntegral.integral_hasDerivAt_right (f := fun (x : ℝ) ↦ f (x + z.im * I))
    (a := z.re) (b := z.re) _ _ _ int1 int2 int3
  dsimp [HasDerivAt, HasDerivAtFilter] at this
  rw [hasFDerivAtFilter_iff_isLittleO] at this
  simp only [intervalIntegral.integral_same, sub_zero, re_add_im, map_sub] at this
  convert this using 3
  ring_nf
  congr

/- The horizontal integral of `f` from `z` to `z.re + w.im * I` is equal to `(w - z).re * f z`
  up to `o(w - z)`, as `w` tends to `z`. -/
lemma deriv_of_wedgeInt_re :
    (fun (w : ℂ) ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - ((w - z).re) * f z)
      =o[𝓝 z] (fun w ↦ w - z) := by
  have zReTendsTo : Filter.Tendsto (fun (w : ℂ) ↦ w.re) (𝓝 z) (𝓝 z.re) :=
    by apply Continuous.tendsto Complex.continuous_re
  have := (deriv_of_wedgeInt_re' f_cont hz).comp_tendsto zReTendsTo
  have := this.trans_isBigO re_isBigO
  convert this using 2
  congr
  simp

/-- If `f` is continuous on a ball containing `z`, then the integral from `z.im` to `w.im` of
  `f (w.re + y * I)` is equal to `(w - z).im * f z` up to `o(w - z)`, as `w` tends to `z`. -/
lemma deriv_of_wedgeInt_im' : (fun w ↦ ∫ y in z.im..w.im, f (w.re + y * I) - f z)
    =o[𝓝 z] fun w ↦ w - z := by
  have : (fun w ↦ f w - f z) =o[𝓝 z] fun (_ : ℂ) ↦ (1 : ℂ)
  · refine (Asymptotics.continuousAt_iff_isLittleO (f := f) (x := z)).mp
      ((f_cont z hz).continuousAt ?_)
    exact (IsOpen.mem_nhds_iff isOpen_ball).mpr hz
  rw [Asymptotics.IsLittleO] at this ⊢
  intro ε ε_pos
  have := this ε_pos
  simp only [Asymptotics.isBigOWith_iff, Pi.one_apply, norm_one, mul_one ] at this ⊢
  have : ∀ᶠ (w : ℂ) in 𝓝 z, ∀ y ∈ Ι z.im w.im, ‖f (w.re + y * I) - f z‖ ≤ ε
  · rw [Metric.nhds_basis_closedBall.eventually_iff] at this ⊢
    obtain ⟨i, i_pos, hi⟩ := this
    refine ⟨i, i_pos, fun w w_in_ball y y_in_I ↦ hi (mem_closedBall_aux w_in_ball y_in_I)⟩
  apply this.mono (fun w hw ↦ ?_)
  calc
    _ ≤ ε * |w.im - z.im|  := intervalIntegral.norm_integral_le_of_norm_le_const hw
    _ = ε * |(w - z).im| := by simp
    _ ≤ ε  * ‖w - z‖ := by gcongr; apply abs_im_le_abs

/--   The vertical integral of `f` from `w.re + z.im * I` to `w` is equal to `(w - z).im * f z`
  up to `o(w - z)`, as `w` tends to `z`. -/
lemma deriv_of_wedgeInt_im : (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im * f z)
    =o[𝓝 z] fun w ↦ w - z := by
  calc
    _ = (fun w:ℂ ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ _ in z.im..w.im, f z)) :=
      by congr! 2; simp
    _ =ᶠ[𝓝 z] (fun w ↦ ∫ y in z.im..w.im, f (w.re + y * I) - f z) := ?_
    _ =o[𝓝 z] fun w ↦ w - z := deriv_of_wedgeInt_im' f_cont hz
  let r₁ := r - dist z c
  have : 0 < r₁ := by simp only [mem_ball, gt_iff_lt] at hz ⊢; linarith
  filter_upwards [ball_mem_nhds z this]
  intro w hw
  rw [intervalIntegral.integral_sub ?_ continuousOn_const.intervalIntegrable]
  exact (f_cont.im_aux_1 hw).intervalIntegrable

/-- The `WedgeInt` has derivative at `z` equal to `f z`. -/
theorem deriv_of_wedgeInt (hf : VanishesOnRectanglesInDisc c r f) :
    HasDerivAt (fun w ↦ WedgeInt c w f) (f z) z := by
  dsimp [HasDerivAt, HasDerivAtFilter]
  rw [hasFDerivAtFilter_iff_isLittleO]
  calc
    _ =ᶠ[𝓝 z] (fun w ↦ WedgeInt z w f - (w - z) * f z) := ?_
    _ = (fun w ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re * f z)
        + I • (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im * f z) := ?_
    _ =o[𝓝 z] fun w ↦ w - z :=
      (deriv_of_wedgeInt_re f_cont hz).add ((deriv_of_wedgeInt_im f_cont hz).const_smul_left I)
  · filter_upwards [VanishesOnRectanglesInDisc.diff_of_wedges f_cont hz hf]
    exact fun _ ha ↦ by rw [ha]; congr
  ext1 w
  simp only [WedgeInt, smul_eq_mul, sub_re, ofReal_sub, sub_im, Pi.add_apply, Pi.smul_apply]
  set intI := ∫ (x : ℝ) in z.re..w.re, f (x + z.im * I)
  set intII := ∫ (y : ℝ) in z.im..w.im, f (w.re + y * I)
  calc
    _ = intI + I * intII - ((w - z).re + (w - z).im * I) * f z := by congr; rw [re_add_im]
    _ = intI + I * intII - ((w.re - z.re) + (w.im - z.im) * I) * f z := by simp
    _ = intI - (w.re - z.re) * f z + I * (intII - (w.im - z.im) * f z) := by ring

end WedgeIntDeriv

/-- *** Moreira's theorem *** A function which is continuous on a disc and whose integral on
  rectangles in the disc vanishes has a primitive on the disc. -/
theorem VanishesOnRectanglesInDisc.hasPrimitive {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (ball c r)) (hf : VanishesOnRectanglesInDisc c r f) :
    ∃ g : ℂ → ℂ, ∀ z ∈ (ball c r), HasDerivAt g (f z) z :=
  ⟨fun z ↦ WedgeInt c z f, fun _ hz ↦ deriv_of_wedgeInt f_cont hz hf⟩

/-- If `f` is holomorphic a set `U`, then the rectangle integral of `f` vanishes, for any
  rectangle in `U`. -/
theorem HolomorphicOn.vanishesOnRectangle {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (f_holo : HolomorphicOn f U) (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 := by
  convert integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ (by simp)
    ((f_holo.mono hU).continuousOn) ?_ using 1
  intro x hx
  apply f_holo.differentiableAt
  rw [_root_.mem_nhds_iff]
  refine ⟨Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im), ?_, ?_, ?_⟩
  · apply subset_trans ?_ hU
    rw [Rectangle]
    apply reProdIm_subset_iff'.mpr
    left
    constructor <;> convert uIoo_subset_uIcc _ _ using 1
  · exact IsOpen.reProdIm isOpen_Ioo isOpen_Ioo
  · convert hx using 1; simp

/-- If `f` is holomorphic a disc, then `f` vanishes on rectangles in the disc. -/
theorem vanishesOnRectanglesInDisc_of_holomorphic {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (f_holo : HolomorphicOn f (ball c r)) :
    VanishesOnRectanglesInDisc c r f := fun _ _ hz hw hz' hw' ↦
  f_holo.vanishesOnRectangle (rectangle_in_convex (convex_ball c r) hz hw hz' hw')

/-- *** Holomorphic functions on discs have Primitives *** A holomorphic function on a disc has
  primitives. -/
theorem hasPrimitives_on_disc (c : ℂ) {r : ℝ} : HasPrimitives (ball c r) := fun _ f_holo ↦
  (vanishesOnRectanglesInDisc_of_holomorphic f_holo).hasPrimitives f_holo.continuousOn

end Complex
