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
we prove that holomorphic functions on disks have primitives. The approach is based on Morera's
theorem, that a continuous function (on a disk) whose `Complex.rectangleIntegral` vanishes on all
rectangles contained in the disk has a primitive. (Coupled with the fact that holomorphic functions
satisfy this property.) To prove Morera's theorem, we first define the `Complex.wedgeIntegral`,
which is the integral of a function over a "wedge" (a horizontal segment followed by a vertical
segment in the disk), and compute its derivative.

## Main results

* `Complex.IsExactOn.exists_forall_mem_ball_hasDerivAt`: **Morera's Theorem**: On a disk, a
  continuous function whose integrals on rectangles vanish, has primitives.
* `Complex.HolomorphicOn.exists_forall_mem_ball_hasDerivAt`: On a disk, a holomorphic function has
  primitives.

TODO: Extend to holomorphic functions on simply connected domains. (In particular, this allows one
to define the complex logarithm of a nonvanishing function on a simply connected domain.)
-/

noncomputable section

open Complex MeasureTheory Metric Set Topology

open scoped Interval

namespace Complex

section Asymptotics

/-- As `w → z`, `w.re - z.re` is big-O of `w - z`. -/
lemma re_isBigO {z : ℂ} : (fun (w : ℂ) ↦ w.re - z.re) =O[𝓝 z] fun w ↦ w - z := by
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp only [Real.norm_eq_abs, one_mul]
  rw [← Complex.sub_re]
  exact abs_re_le_norm (w - z)

/-- As `w → z`, `w.im - z.im` is big-O of `w - z`. -/
lemma im_isBigO {z : ℂ} : (fun (w : ℂ) ↦ w.im - z.im) =O[𝓝 z] fun w ↦ w - z := by
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp only [Real.norm_eq_abs, one_mul]
  rw [← Complex.sub_im]
  exact abs_im_le_norm (w - z)

end Asymptotics

section Rectangle

/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. -/
lemma uIcc_re_prod_uIcc_im_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair,
    insert_union, ← insert_eq, preimage_equiv_eq_image_symm, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. -/
lemma Convex.rectangle_subset {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  rw [Rectangle, uIcc_re_prod_uIcc_im_eq_convexHull]
  convert convexHull_min ?_ (U_convex)
  refine insert_subset hz (insert_subset hzw (insert_subset hwz ?_))
  exact singleton_subset_iff.mpr hw

/-- If `z` is in a ball centered at `c`, then `z.re + c.im * I` is in the ball. -/
lemma re_add_im_mul_mem_ball {c : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ ball c r) :
    z.re + c.im * I ∈ ball c r := by
  simp only [mem_ball] at hz ⊢
  rw [dist_of_im_eq] <;> simp only [add_re, I_re, mul_zero, I_im, zero_add, add_im,
    add_zero, sub_self, mul_re, mul_one, ofReal_im, mul_im, ofReal_re]
  apply lt_of_le_of_lt ?_ hz
  rw [dist_eq_re_im, Real.dist_eq]
  apply Real.le_sqrt_of_sq_le
  simp only [_root_.sq_abs, le_add_iff_nonneg_right]
  exact sq_nonneg _

end Rectangle

section SubsetBall_Aux

/- Auxiliary lemmata about subsets of balls -/

private lemma mem_ball_re_aux {c z : ℂ} {r : ℝ} :
    (Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) ×ℂ {z.im} ⊆ ball z (r - dist z c) := by
  intro x hx
  obtain ⟨xRe, xIm⟩ := hx
  simp only [mem_preimage, mem_singleton_iff, mem_Ioo] at xRe xIm
  simp only [mem_ball]
  rw [dist_eq_re_im, xIm]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_sq_eq_abs, abs_lt, neg_sub]
  refine ⟨by linarith, by linarith⟩

lemma mem_ball_re_aux' {c : ℂ} {r : ℝ} {z : ℂ} {x : ℝ}
    (hx : x ∈ Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) :
    x + z.im * I ∈ ball c r := by
  set r₁ := r - dist z c
  set s := Ioo (z.re - r₁) (z.re + r₁)
  have s_ball₁ : s ×ℂ {z.im} ⊆ ball z r₁ := mem_ball_re_aux
  have s_ball : s ×ℂ {z.im} ⊆ ball c r := s_ball₁.trans (by apply ball_subset_ball'; simp [r₁])
  apply s_ball
  rw [mem_reProdIm]
  simp [hx]

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
  convert Convex.rectangle_subset (convex_ball c r) ha₁ ha₂ ?_ ?_ using 1 <;>
  simp [horizontalSegment_eq a₁ a₂ b, ha₁, ha₂, Rectangle]

lemma mem_ball_of_map_im_aux {c : ℂ} {r : ℝ} {a b₁ b₂ : ℝ} (hb₁ : a + b₁ * I ∈ ball c r)
    (hb₂ : a + b₂ * I ∈ ball c r) : (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] ⊆ ball c r := by
  convert Convex.rectangle_subset (convex_ball c r) hb₁ hb₂ ?_ ?_ using 1 <;>
  simp [verticalSegment_eq a b₁ b₂, hb₁, hb₂, Rectangle]

lemma mem_ball_of_map_im_aux' {c : ℂ} {r : ℝ} {z : ℂ} {w : ℂ} (hw : w ∈ ball z (r - dist z c)) :
    (fun (y : ℝ) ↦ w.re + y * I) '' [[z.im, w.im]] ⊆ ball c r := by
  apply mem_ball_of_map_im_aux <;>
  apply mem_of_subset_of_mem (ball_subset_ball' (by simp) : ball z (r - dist z c) ⊆ ball c r)
  · exact re_add_im_mul_mem_ball hw
  · convert hw; simp

end SubsetBall_Aux

end Complex

section ContinuousOn_Aux
/- Auxiliary lemmata about continuity of various occurring functions -/

variable {E : Type*} [NormedAddCommGroup E] {c : ℂ} {r : ℝ}
  {f : ℂ → E} (hf : ContinuousOn f (ball c r))

include hf

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

variable {E : Type*} [NormedRing E] [NormedSpace ℂ E]

/-- The `z`-`w`-`wedgeIntegral` of `f`, is the integral of `f` over two sides of the rectangle
  determined by `z` and `w`. -/
def wedgeIntegral (z w : ℂ) (f : ℂ → E) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))

/-- The `z`-`w`-`rectangleIntegral` of `f`, is the integral of `f` around the rectangle determined
  by `z` and `w`. -/
def rectangleIntegral (z w : ℂ) (f : ℂ → E) : E :=
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

lemma rectangleIntegral_eq_wedgeIntegral_add_wedgeIntegral (z w : ℂ) (f : ℂ → E) :
    rectangleIntegral z w f = wedgeIntegral z w f + wedgeIntegral w z f := by
  simp only [rectangleIntegral, wedgeIntegral, intervalIntegral.integral_symm z.re w.re,
    intervalIntegral.integral_symm z.im w.im, smul_neg]
  abel

/-- A function `f` `IsExactOn` in `U` if, for any rectangle contained in `U`
  the integral of `f` over the rectangle is zero. -/
def IsExactOn (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ᵉ (z ∈ U) (w ∈ U), Rectangle z w ⊆ U → rectangleIntegral z w f = 0

variable {c : ℂ} {r : ℝ} {f : ℂ → E}

section ContinuousOnBall

variable (f_cont : ContinuousOn f (ball c r)) {z : ℂ} (hz : z ∈ ball c r)
include f_cont hz

/-- If a function `f` `IsExactOn` of center `c`, then, for all `w` in a
  neighborhood of `z`, the wedge integral from `c` to `w` minus the wedge integral from `c` to `z`
  is equal to the wedge integral from `z` to `w`. -/
lemma IsExactOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral
    (hf : IsExactOn f (ball c r)) :
    ∀ᶠ w in 𝓝 z, wedgeIntegral c w f - wedgeIntegral c z f = wedgeIntegral z w f := by
  have hr : 0 < r := pos_of_mem_ball hz
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simp only [mem_ball, r₁] at hz ⊢; linarith
  have z_ball : ball z r₁ ⊆ ball c r := ball_subset_ball' (by simp [r₁])
  filter_upwards [ball_mem_nhds z r₁_pos]
  intro w w_in_z_ball
  have hzPlusH : w ∈ ball c r := mem_of_subset_of_mem z_ball w_in_z_ball
  simp only [wedgeIntegral]
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
    → IntervalIntegrable (fun y ↦ f (a + y * I)) MeasureTheory.volume b₁ b₂ := by
    intro a b₁ b₂ hb₁ hb₂
    apply ContinuousOn.intervalIntegrable (f_cont.im_aux hb₁ hb₂)
  have intIdecomp : intI = intIII + intVII := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
    · simp only [re_add_im, mem_ball, dist_self, hr]
    · exact re_add_im_mul_mem_ball hz
    · exact re_add_im_mul_mem_ball hz
    · exact re_add_im_mul_mem_ball hzPlusH
  have intIIdecomp : intII = intVIII + intVI := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · exact re_add_im_mul_mem_ball hzPlusH
    · apply mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    · apply mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    · convert hzPlusH; simp
  have rectZero : intVIII = - intVII + intV + intIV := by
    rw [← sub_eq_zero]
    have : intVII - intV + intVIII - intIV = 0 := by
      have wzInBall : w.re + z.im * I ∈ ball c r :=
        mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
      have wcInBall : w.re + c.im * I ∈ ball c r := re_add_im_mul_mem_ball hzPlusH
      have hU : Rectangle (z.re + c.im * I) (w.re + z.im * I) ⊆ ball c r :=
        (convex_ball c r).rectangle_subset (re_add_im_mul_mem_ball hz) wzInBall
          (by simpa using hz) (by simpa using wcInBall)
      convert hf (z.re + c.im * I) (re_add_im_mul_mem_ball hz) (w.re + z.im * I) wzInBall hU using 1
      rw [rectangleIntegral]
      congr
      · simp [intVII]
      · simp [intV]
      · simp [intVIII]
      · simp [intIV]
    rw [← this]
    abel
  rw [intIdecomp, intIIdecomp, rectZero]
  abel

variable [CompleteSpace E]

/- The horizontal integral of `f` from `z` to `z.re + w.im * I` is equal to `(w - z).re * f z`
  up to `o(w - z)`, as `w` tends to `z`. -/
lemma deriv_of_wedgeIntegral_re :
    (fun w ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z) =o[𝓝 z] fun w ↦ w - z := by
  suffices (fun x ↦ (∫ t in z.re..x, f (t + z.im * I)) - (x - z.re) • f z) =o[𝓝 z.re]
      fun x ↦ x - z.re from this.comp_tendsto (continuous_re.tendsto z) |>.trans_isBigO re_isBigO
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simpa only [mem_ball, sub_pos, r₁] using hz
  let s : Set ℝ := Ioo (z.re - r₁) (z.re + r₁)
  have zRe_mem_s : z.re ∈ s := by simp [s, r₁_pos]
  have f_contOn : ContinuousOn (fun (x : ℝ) ↦ f (x + z.im * I)) s := f_cont.re_aux_1
  have int1 : IntervalIntegrable (fun (x : ℝ) ↦ f (x + z.im * I)) volume z.re z.re :=
    ContinuousOn.intervalIntegrable <| f_contOn.mono <| by simpa
  have int2 : StronglyMeasurableAtFilter (fun (x : ℝ) ↦ f (x + z.im * I)) (𝓝 z.re) :=
    f_contOn.stronglyMeasurableAtFilter isOpen_Ioo _ zRe_mem_s
  have int3 : ContinuousAt (fun (x : ℝ) ↦ f (x + z.im * I)) z.re :=
    isOpen_Ioo.continuousOn_iff.mp f_contOn zRe_mem_s
  simpa [HasDerivAt, HasDerivAtFilter, hasFDerivAtFilter_iff_isLittleO] using
    intervalIntegral.integral_hasDerivAt_right int1 int2 int3

variable [NormOneClass E]

/-- The vertical integral of `f` from `w.re + z.im * I` to `w` is equal to `(w - z).im * f z`
  up to `o(w - z)`, as `w` tends to `z`. -/
lemma deriv_of_wedgeIntegral_im :
    (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) =o[𝓝 z] fun w ↦ w - z := by
  suffices (fun w ↦ ∫ y in z.im..w.im, f (w.re + y * I) - f z) =o[𝓝 z] fun w ↦ w - z by
    calc
      _ = fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ _ in z.im..w.im, f z) := by simp
      _ =ᶠ[𝓝 z] fun w ↦ ∫ y in z.im..w.im, f (w.re + y * I) - f z := ?_
      _ =o[𝓝 z] fun w ↦ w - z := this
    replace hz : 0 < r - dist z c := by simpa only [mem_ball, sub_pos] using hz
    filter_upwards [ball_mem_nhds z hz] with w hw using (intervalIntegral.integral_sub
      (f_cont.im_aux_1 hw).intervalIntegrable intervalIntegrable_const).symm
  have : (fun w ↦ f w - f z) =o[𝓝 z] fun _ ↦ (1 : E) :=
    Asymptotics.continuousAt_iff_isLittleO.mp <| (f_cont z hz).continuousAt <|
      isOpen_ball.mem_nhds_iff.mpr hz
  rw [Asymptotics.IsLittleO] at this ⊢
  intro ε ε_pos
  replace := this ε_pos
  simp only [Asymptotics.isBigOWith_iff, norm_one, mul_one] at this ⊢
  replace this : ∀ᶠ w in 𝓝 z, ∀ y ∈ Ι z.im w.im, ‖f (w.re + y * I) - f z‖ ≤ ε := by
    rw [Metric.nhds_basis_closedBall.eventually_iff] at this ⊢
    obtain ⟨i, i_pos, hi⟩ := this
    exact ⟨i, i_pos, fun w w_in_ball y y_in_I ↦ hi (mem_closedBall_aux w_in_ball y_in_I)⟩
  filter_upwards [this] with w hw
  calc
    _ ≤ ε * ‖w.im - z.im‖ := intervalIntegral.norm_integral_le_of_norm_le_const hw
    _ = ε * ‖(w - z).im‖ := by simp
    _ ≤ ε * ‖w - z‖ := (mul_le_mul_iff_of_pos_left ε_pos).mpr (abs_im_le_norm _)

/-- The `wedgeIntegral` has derivative at `z` equal to `f z`. -/
theorem IsExactOn.hasDerivAt_wedgeIntegral (h : IsExactOn f (ball c r)) :
    HasDerivAt (fun w ↦ wedgeIntegral c w f) (f z) z := by
  rw [hasDerivAt_iff_isLittleO]
  calc
    _ =ᶠ[𝓝 z] (fun w ↦ wedgeIntegral z w f - (w - z) • f z) := ?_
    _ = (fun w ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z)
        + I • (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) := ?_
    _ =o[𝓝 z] fun w ↦ w - z := (deriv_of_wedgeIntegral_re f_cont hz).add
        ((deriv_of_wedgeIntegral_im f_cont hz).const_smul_left I)
  · exact (h.eventually_nhds_wedgeIntegral_sub_wedgeIntegral f_cont hz).mono <| by simp
  ext w
  set I₁ := ∫ x in z.re..w.re, f (x + z.im * I)
  set I₂ := ∫ y in z.im..w.im, f (w.re + y * I)
  calc
    _ = I₁ + I • I₂ - ((w - z).re + (w - z).im * I) • f z := by congr; rw [re_add_im]
    _ = I₁ + I • I₂ - ((w.re - z.re : ℂ) + (w.im - z.im) * I) • f z := by simp
    _ = I₁ - (w.re - z.re : ℂ) • f z + I • (I₂ - (w.im - z.im : ℂ) • f z) := ?_
  · rw [add_smul, smul_sub, smul_smul, mul_comm I]; abel
  · congr <;> simp

end ContinuousOnBall

/-- If `f` is holomorphic a disk, then `f` vanishes on rectangles in the disk. -/
theorem HolomorphicOn.isExactOn (hf : HolomorphicOn f (ball c r)) :
    IsExactOn f (ball c r) :=
  fun z _ w _ hzw ↦ integral_boundary_rect_eq_zero_of_differentiableOn f z w <| hf.mono hzw

variable [CompleteSpace E] [NormOneClass E]

/-- **Morera's theorem for a disk** On a disk, a continuous function whose integrals on rectangles
  vanish, has primitives. -/
theorem IsExactOn.exists_forall_mem_ball_hasDerivAt
    (f_cont : ContinuousOn f (ball c r)) (hf : IsExactOn f (ball c r)) :
    ∃ g, ∀ z ∈ ball c r, HasDerivAt g (f z) z :=
  ⟨fun z ↦ wedgeIntegral c z f, fun _ ↦ hf.hasDerivAt_wedgeIntegral f_cont⟩

/-- **Morera's theorem for a disk** On a disk, a holomorphic function has primitives. -/
theorem HolomorphicOn.exists_forall_mem_ball_hasDerivAt (hf : HolomorphicOn f (ball c r)) :
    ∃ g, ∀ z ∈ ball c r, HasDerivAt g (f z) z :=
  hf.isExactOn.exists_forall_mem_ball_hasDerivAt hf.continuousOn

end Complex
