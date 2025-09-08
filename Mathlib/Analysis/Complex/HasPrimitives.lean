/-
Copyright (c) 2024 Ian Jauslin and Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Jauslin, Alex Kontorovich, Oliver Nash
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# Primitives of Holomorphic Functions

In this file, we give conditions under which holomorphic functions have primitives. The main goal
is to prove that holomorphic functions on simply connected domains have primitives. As a first step,
we prove that holomorphic functions on disks have primitives. The approach is based on Morera's
theorem, that a continuous function (on a disk) whose integral round a rectangle vanishes on all
rectangles contained in the disk has a primitive. (Coupled with the fact that holomorphic functions
satisfy this property.) To prove Morera's theorem, we first define the `Complex.wedgeIntegral`,
which is the integral of a function over a "wedge" (a horizontal segment followed by a vertical
segment in the disk), and compute its derivative.

## Main results

* `Complex.IsClosedOn.isExactOn_ball`: **Morera's Theorem**: On a disk, a continuous function whose
  integrals on rectangles vanish, has primitives.
* `Complex.HolomorphicOn.isExactOn_ball`: On a disk, a holomorphic function has primitives.

TODO: Extend to holomorphic functions on simply connected domains. (In particular, this allows one
to define the complex logarithm of a nonvanishing function on a simply connected domain.)
-/

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E]

namespace Complex

/-- If `z` is in a ball centered at `c`, then `z.re + c.im * I` is in the ball. -/
lemma re_add_im_mul_mem_ball {c : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ ball c r) :
    z.re + c.im * I ∈ ball c r := by
  suffices dist (z.re + c.im * I) c ≤ dist z c from lt_of_le_of_lt this hz
  simp only [dist_eq_re_im]
  apply Real.le_sqrt_of_sq_le
  rw [Real.sq_sqrt (by positivity)]
  simp [sq_nonneg _]

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

variable {c : ℂ} {r : ℝ} {f : ℂ → E} (hf : ContinuousOn f (ball c r))
include hf

lemma ContinuousOn.re_aux_1 {z : ℂ} :
    ContinuousOn (fun (x : ℝ) ↦ f (x + z.im * I))
      (Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) :=
  hf.comp ((continuous_add_right _).comp continuous_ofReal).continuousOn <| fun _ ↦ mem_ball_re_aux'

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

variable [NormedSpace ℂ E]

/-- The `(z, w)`-wedge-integral of `f`, is the integral of `f` over two sides of the rectangle
  determined by `z` and `w`. -/
def wedgeIntegral (z w : ℂ) (f : ℂ → E) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I))

lemma wedgeIntegral_add_wedgeIntegral_eq (z w : ℂ) (f : ℂ → E) :
    wedgeIntegral z w f + wedgeIntegral w z f =
      (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) := by
  simp only [wedgeIntegral, intervalIntegral.integral_symm z.re w.re,
    intervalIntegral.integral_symm z.im w.im, smul_neg]
  abel

/-- A function `f` `IsClosedOn` in `U` if, for any rectangle contained in `U`
  the integral of `f` over the rectangle is zero. -/
def IsClosedOn (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ z w, Rectangle z w ⊆ U → wedgeIntegral z w f = - wedgeIntegral w z f

/-- A function `f` `IsExactOn` in `U` if it is the complex derivative of a function on `U`.

In complex variable theory, this is also referred to as "having a primitive". -/
def IsExactOn (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∃ g, ∀ z ∈ U, HasDerivAt g (f z) z

variable {c : ℂ} {r : ℝ} {f : ℂ → E}

theorem HolomorphicOn.isClosedOn {U : Set ℂ} (hf : HolomorphicOn f U) :
    IsClosedOn f U := by
  rintro z w hzw
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  exact integral_boundary_rect_eq_zero_of_differentiableOn f z w <| hf.mono hzw

variable [CompleteSpace E]

lemma IsExactOn.isClosedOn_of_isOpen
    {U : Set ℂ} (hU : IsOpen U) (hf : IsExactOn f U) :
    IsClosedOn f U := by
  obtain ⟨g, hg⟩ := hf
  have hg' : DifferentiableOn ℂ g U := fun z hz ↦ (hg z hz).differentiableAt.differentiableWithinAt
  apply HolomorphicOn.isClosedOn
  exact (differentiableOn_congr <| fun z hz ↦ (hg z hz).deriv).mp <| hg'.deriv hU

section ContinuousOnBall

variable (f_cont : ContinuousOn f (ball c r)) {z : ℂ} (hz : z ∈ ball c r)
include f_cont hz

omit [CompleteSpace E] in
/-- If a function `f` `IsClosedOn` on a ball of center `c`, then, for all `w` in a
  neighborhood of `z`, the wedge integral from `c` to `w` minus the wedge integral from `c` to `z`
  is equal to the wedge integral from `z` to `w`. -/
lemma IsClosedOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral (hf : IsClosedOn f (ball c r)) :
    ∀ᶠ w in 𝓝 z, wedgeIntegral c w f - wedgeIntegral c z f = wedgeIntegral z w f := by
  refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w w_in_z_ball ↦ ?_⟩
  set I₁ :=     ∫ x in c.re..w.re, f (x + c.im * I)
  set I₂ := I • ∫ y in c.im..w.im, f (w.re + y * I)
  set I₃ :=     ∫ x in c.re..z.re, f (x + c.im * I)
  set I₄ := I • ∫ y in c.im..z.im, f (z.re + y * I)
  set I₅ :=     ∫ x in z.re..w.re, f (x + z.im * I)
  set I₆ := I • ∫ y in z.im..w.im, f (w.re + y * I)
  set I₇ :=     ∫ x in z.re..w.re, f (x + c.im * I)
  set I₈ := I • ∫ y in c.im..z.im, f (w.re + y * I)
  have z_ball : ball z (r - dist z c) ⊆ ball c r := ball_subset_ball' (by simp)
  have w_mem : w ∈ ball c r := mem_of_subset_of_mem z_ball w_in_z_ball
  have integrableHoriz (a₁ a₂ b : ℝ) (ha₁ : a₁ + b * I ∈ ball c r) (ha₂ : a₂ + b * I ∈ ball c r) :
      IntervalIntegrable (fun x ↦ f (x + b * I)) volume a₁ a₂ :=
    (f_cont.re_aux_2 ha₁ ha₂).intervalIntegrable
  have integrableVert (a b₁ b₂ : ℝ) (hb₁ : a + b₁ * I ∈ ball c r) (hb₂ : a + b₂ * I ∈ ball c r) :
      IntervalIntegrable (fun y ↦ f (a + y * I)) volume b₁ b₂ :=
    (f_cont.im_aux hb₁ hb₂).intervalIntegrable
  have hI₁ : I₁ = I₃ + I₇ := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
    · exact re_add_im_mul_mem_ball <| mem_ball_self (pos_of_mem_ball hz)
    · exact re_add_im_mul_mem_ball hz
    · exact re_add_im_mul_mem_ball hz
    · exact re_add_im_mul_mem_ball w_mem
  have hI₂ : I₂ = I₈ + I₆ := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · exact re_add_im_mul_mem_ball w_mem
    · exact mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    · exact mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    · simpa using w_mem
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    have wzInBall : w.re + z.im * I ∈ ball c r :=
      mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    have wcInBall : w.re + c.im * I ∈ ball c r := re_add_im_mul_mem_ball w_mem
    have hU : Rectangle (z.re + c.im * I) (w.re + z.im * I) ⊆ ball c r :=
      (convex_ball c r).rectangle_subset (re_add_im_mul_mem_ball hz) wzInBall
        (by simpa using hz) (by simpa using wcInBall)
    simpa [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] using
      hf (z.re + c.im * I) (w.re + z.im * I) hU
  grind [wedgeIntegral]

/- The horizontal integral of `f` from `z` to `z.re + w.im * I` is equal to `(w - z).re * f z`
  up to `o(w - z)`, as `w` tends to `z`. -/
private lemma hasDerivAt_wedgeIntegral_re_aux :
    (fun w ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z) =o[𝓝 z] fun w ↦ w - z := by
  suffices (fun x ↦ (∫ t in z.re..x, f (t + z.im * I)) - (x - z.re) • f z) =o[𝓝 z.re]
      fun x ↦ x - z.re from
    this.comp_tendsto (continuous_re.tendsto z) |>.trans_isBigO isBigO_re_sub_re
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

/-- The vertical integral of `f` from `w.re + z.im * I` to `w` is equal to `(w - z).im * f z`
  up to `o(w - z)`, as `w` tends to `z`. -/
private lemma hasDerivAt_wedgeIntegral_im_aux :
    (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) =o[𝓝 z] fun w ↦ w - z := by
  suffices (fun w ↦ ∫ y in z.im..w.im, f (w.re + y * I) - f z) =o[𝓝 z] fun w ↦ w - z by
    calc
      _ = fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ _ in z.im..w.im, f z) := by simp
      _ =ᶠ[𝓝 z] fun w ↦ ∫ y in z.im..w.im, f (w.re + y * I) - f z := ?_
      _ =o[𝓝 z] fun w ↦ w - z := this
    refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w hw ↦ ?_⟩
    exact (intervalIntegral.integral_sub
      (f_cont.im_aux_1 hw).intervalIntegrable intervalIntegrable_const).symm
  have : (fun w ↦ f w - f z) =o[𝓝 z] fun _ ↦ (1 : ℝ) := by
    rw [Asymptotics.isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
    exact f_cont.continuousAt <| _root_.mem_nhds_iff.mpr ⟨ball c r, le_refl _, isOpen_ball, hz⟩
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
theorem IsClosedOn.hasDerivAt_wedgeIntegral (h : IsClosedOn f (ball c r)) :
    HasDerivAt (fun w ↦ wedgeIntegral c w f) (f z) z := by
  rw [hasDerivAt_iff_isLittleO]
  calc
    _ =ᶠ[𝓝 z] (fun w ↦ wedgeIntegral z w f - (w - z) • f z) := ?_
    _ = (fun w ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z)
        + I • (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) := ?_
    _ =o[𝓝 z] fun w ↦ w - z := (hasDerivAt_wedgeIntegral_re_aux f_cont hz).add
        ((hasDerivAt_wedgeIntegral_im_aux f_cont hz).const_smul_left I)
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

/-- **Morera's theorem for a disk** On a disk, a continuous function whose integrals on rectangles
  vanish, has primitives. -/
theorem IsClosedOn.isExactOn_ball (hf' : ContinuousOn f (ball c r)) (hf : IsClosedOn f (ball c r)) :
    IsExactOn f (ball c r) :=
  ⟨fun z ↦ wedgeIntegral c z f, fun _ ↦ hf.hasDerivAt_wedgeIntegral hf'⟩

/-- **Morera's theorem for a disk** On a disk, a holomorphic function has primitives. -/
theorem HolomorphicOn.isExactOn_ball (hf : HolomorphicOn f (ball c r)) :
    IsExactOn f (ball c r) :=
  hf.isClosedOn.isExactOn_ball hf.continuousOn

end Complex
