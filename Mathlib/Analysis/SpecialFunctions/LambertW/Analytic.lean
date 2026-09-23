/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.SpecialFunctions.LambertW.Real

/-!
# Analytic

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## TODO

+ prove real version

## Tags

Foobars, barfoos
-/

public noncomputable section

open Set Real Filter Topology

open scoped ComplexLambertW
namespace Complex

variable {α : Type*} {s : Set ℂ} {w z : ℂ} {k : ℤ}

namespace LambertW

/-- TODO doc -/
def branchCut (k : ℤ) : Set ℂ :=
  Iic (if k = 0 then -(rexp 1)⁻¹ else 0) ×ℂ {0}

/-- TODO doc -/
def slitPlane (k : ℤ) : Set ℂ :=
  (branchCut k)ᶜ

/-- TODO doc -/
def openRange (k : ℤ) : Set ℂ :=
  if k = 0 then {w | w.arg + w.im ∈ Ioo (-π) π} ∪ Ioo (-1) 0 ×ℂ {0} else
    {w | w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π)}

theorem openRange_zero : openRange 0 = {w | w.arg + w.im ∈ Ioo (-π) π} ∪ Ioo (-1) 0 ×ℂ {0} := by
  rfl

theorem openRange_of_ne_zero (hk : k ≠ 0) :
    openRange k = {w | w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π)} :=
  ite_eq_right hk

theorem neg_one_notMem_openRange : -1 ∉ openRange k := by
  by_cases hk : k = 0
  · simp [hk, openRange_zero, mem_reProdIm]
  · simp [openRange_of_ne_zero hk, field]
    norm_cast
    omega

theorem openRange_ne_neg_one (hw : w ∈ openRange k) : w ≠ -1 :=
  ne_of_mem_of_not_mem hw neg_one_notMem_openRange

theorem zero_mem_openRange_iff : 0 ∈ openRange k ↔ k = 0 := by
  by_cases hk : k = 0 <;> simp [openRange, hk, pi_pos, mul_neg_iff, pi_pos.not_gt]
  norm_cast
  omega

theorem zero_mem_slitPlane_iff : 0 ∈ slitPlane k ↔ k = 0 := by
  by_cases hk : k = 0 <;> simp [slitPlane, branchCut, mem_reProdIm, hk, Real.exp_pos]

theorem slitPlane_subset_domain : slitPlane k ⊆ domain k := by
  by_cases hk : k = 0 <;> simp [slitPlane, branchCut, domain, hk, mem_reProdIm]

theorem openRange_subset_range : openRange k ⊆ range k := by
  intro z
  by_cases hk : k = 0
  · grind [arg_eq_pi_iff, openRange_zero, mem_range_zero_iff, mem_reProdIm, pi_pos]
  rw [openRange_of_ne_zero hk]
  by_cases hk' : k = -1
  · simp [hk', mem_range_neg_one_iff]
    grind
  simpa only [mem_range_iff_of_ne hk hk'] using fun ⟨hz1, hz2⟩ => ⟨hz1, hz2.le⟩

theorem isOpen_domain : IsOpen (domain k) := by
  by_cases hk : k = 0 <;> simp [domain, hk]

theorem isClosed_branchCut : IsClosed (branchCut k) :=
  isClosed_Iic.reProdIm isClosed_singleton

theorem isOpen_slitPlane : IsOpen (slitPlane k) :=
  isClosed_branchCut.isOpen_compl

private theorem continuousOn_arg_add_im :
    ContinuousOn (fun w : ℂ => w.arg + w.im) Complex.slitPlane :=
  continuousOn_arg.add continuous_im.continuousOn

private theorem _root_.Real.add_sin_mem_Ioo_of_mem_Ioo :
    ∀ ⦃x : ℝ⦄, x ∈ Ioo (-π) π -> x + x.sin ∈ Ioo (-π) π := by
  suffices ∀ x ∈ Ioo (-π) π, x + x.sin < π from fun x ⟨hxl, hxr⟩ =>
    ⟨by grind [this (-x) (by grind), Real.sin_neg x], this x ⟨hxl, hxr⟩⟩
  exact fun x hx => by linarith [Real.sin_lt <| sub_pos_of_lt hx.right, Real.sin_pi_sub x]

--  golf
private theorem isOpen_openRange_zero : IsOpen (openRange 0) := by
  suffices openRange 0 =
      Complex.slitPlane ∩ (fun w => w.arg + w.im) ⁻¹' Ioo (-π) π ∪ Metric.ball 0 1 by
    simpa only [this] using
      continuousOn_arg_add_im.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo |>.union
        Metric.isOpen_ball
  rw [openRange_zero]
  ext w
  constructor
  · rintro (hidx | ⟨hre, him⟩)
    · by_cases hs : w ∈ Complex.slitPlane
      · exact Or.inl ⟨hs, hidx⟩
      rw [Complex.mem_slitPlane_iff, not_or, not_not, not_lt] at hs
      obtain ⟨hre, him⟩ := hs
      rcases lt_or_eq_of_le hre with hre | hre
      · grind [arg_eq_pi_iff]
      · exact Or.inr <| (Complex.ext (w := 0) hre him) ▸ Metric.mem_ball_self zero_lt_one
    · rw [mem_preimage, mem_singleton_iff] at him
      refine Or.inr <| mem_ball_zero_iff.mpr ?_
      rw [Complex.ext (z := w) (w := w.re) rfl him, norm_real, norm_eq_abs, abs_of_neg hre.right]
      linarith [hre.left]
  rintro (⟨-, hidx⟩ | hb)
  · exact Or.inl hidx
  rw [mem_ball_zero_iff] at hb
  by_cases harg : w.arg = π
  · obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp harg
    refine Or.inr ⟨⟨?_, hre⟩, him⟩
    rw [Complex.ext (z := w) (w := w.re) rfl him, norm_real, norm_eq_abs, abs_of_neg hre] at hb
    grind
  left
  replace harg : w.arg ∈ Ioo (-π) π := ⟨neg_pi_lt_arg w, lt_of_le_of_ne (arg_le_pi w) harg⟩
  rw [mem_ofPred, ← norm_mul_sin_arg]
  generalize w.arg = x at *
  rw [show x + ‖w‖ * x.sin = (1 - ‖w‖) * x + ‖w‖ * (x + x.sin) by ring]
  exact (convex_Ioo (-π) π) harg (add_sin_mem_Ioo_of_mem_Ioo harg)
    (sub_nonneg_of_le hb.le) (norm_nonneg w) (sub_add_cancel 1 ‖w‖)

--  golf?
private theorem isOpen_openRange_of_ne (hk : k ≠ 0) : IsOpen (openRange k) := by
  suffices openRange k = Complex.slitPlane ∩
      (fun w => w.arg + w.im) ⁻¹' Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) by
    simpa only [this] using
      continuousOn_arg_add_im.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo
  rw [openRange_of_ne_zero hk]
  ext w
  refine ⟨fun hw => ⟨Classical.byContradiction fun nh => ?_, hw⟩, And.right⟩
  rw [mem_slitPlane_iff_arg, not_and_or, not_not, not_not] at nh
  rw [mem_ofPred] at hw
  rcases nh with nh | nh
  · simp [nh, field, arg_eq_pi_iff.mp nh |>.right] at hw
    norm_cast at hw
    omega
  · simp [nh, field, pi_pos, mul_neg_iff, pi_pos.not_gt] at hw
    norm_cast at hw
    omega

theorem isOpen_openRange : IsOpen (openRange k) :=
  em (k = 0) |>.elim (fun hk => hk ▸ isOpen_openRange_zero) isOpen_openRange_of_ne

private theorem arg_mul_exp_eq_of_mem (hw : w ≠ 0)
    (h : w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π)) :
    (w * cexp w).arg = w.arg + w.im - k * (2 * π) := by
  rw [← exp_log hw, ← exp_add, mul_comm, arg_exp, add_im, log_im, toIocMod_eq_iff, exp_log hw]
  exact ⟨by grind [pi_pos], k, by ring⟩

theorem mapsTo_lambertW_slitPlane : MapsTo (W_ k) (slitPlane k) (openRange k) := by
  have Hw : MapsTo (W_ k) (domain k) (range k) := bijOn_lambertW_domain_range (k := k) |>.mapsTo
  intro z hz
  specialize Hw <| slitPlane_subset_domain hz
  have hwz := lambertW_mul_exp_lambertW_of_mem_domain <| slitPlane_subset_domain hz
  set w := W_ k z
  by_contra nh
  simp only [slitPlane, branchCut, mem_compl_iff, mem_reProdIm, mem_Iic, mem_singleton_iff,
    not_and] at hz
  rcases (show (k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1)) by tauto) with rfl | rfl | ⟨hk, hk'⟩
  · simp only [mem_range_zero_iff, openRange_zero, ite_true, mem_reProdIm, mem_union] at Hw nh hz
    push _ ∈ _ at Hw nh
    push +distrib ¬ _ at Hw nh hz
    have hw1 : w.arg + w.im = π := by grind
    have hw2 : w.im > 0 := by
      rcases lt_trichotomy w.im 0 with hw2 | hw2 | hw2
      · grind [arg_le_pi]
      · simp only [hw2, add_zero] at hw1
        simp [hw1, hw2, pi_pos, arg_eq_pi_iff.mp hw1 |>.left.not_ge] at Hw nh
        have hw : w = -1 := by
          apply Complex.ext
          · grind [neg_re, one_re]
          · simpa
        simp [hw, exp_neg] at hwz
        simp [← hwz, exp_re, normSq, exp_im] at hz
      · exact hw2
    have : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} :=
      hwz ▸ Complex.LambertW.mapsTo_mul_exp_arg_add_im_eq ⟨hw1, hw2⟩
    grind [mem_reProdIm]
  all_goals have hw₀ : w ≠ 0 := by grind [zero_mem_range_iff]
  · simp only [mem_range_neg_one_iff, openRange_of_ne_zero,
      neg_eq_zero, one_ne_zero, ne_eq, not_false_eq_true, ite_false] at Hw nh hz
    rcases Hw with Hw | Hw
    · grind [arg_eq_pi_iff, arg_mul_exp_eq_of_mem hw₀ (k := -1) (by grind [pi_pos])]
    · rw [Complex.ext_iff] at hwz
      simp [Hw, exp_im, exp_re] at hwz
      apply hz ?_ hwz.right.symm
      rw [← hwz.left]
      nlinarith [exp_pos w.re]
  · simp only [mem_range_iff_of_ne hk hk', openRange_of_ne_zero hk, hk, ite_false] at Hw nh hz
    grind [arg_eq_pi_iff, arg_mul_exp_eq_of_mem hw₀ (k := k) (by grind [pi_pos])]

theorem mapsTo_mul_exp_openRange : MapsTo (fun w => w * cexp w) (openRange k) (slitPlane k) := by
  have Hz : MapsTo (fun w => w * cexp w) (range k) (domain k) :=
    bijOn_mul_exp_range_domain (k := k) |>.mapsTo
  intro w hw
  specialize Hz <| openRange_subset_range hw
  dsimp only at Hz ⊢
  have hwz : W_ k (w * cexp w) = w := lambertW_mul_exp_of_mem_range <| openRange_subset_range hw
  set z : ℂ := w * cexp w
  by_contra nh
  simp only [slitPlane, branchCut, mem_compl_iff, not_not] at nh
  by_cases hw₀ : w = 0
  · simp [hw₀, zero_mem_openRange_iff] at hw
    simp [hw, z, hw₀, mem_reProdIm, exp_pos 1 |>.not_ge] at nh
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [↓reduceIte, openRange, mem_Ioo, mem_union, mem_ofPred_eq] at nh hw
    have hz : z.arg = π := arg_eq_pi_iff.mpr ⟨nh.left.trans_lt <| by simp [exp_pos], nh.right⟩
    rcases hw with hw | hw
    · grind [arg_mul_exp_eq_of_mem hw₀ (k := 0) (by grind)]
    · simp only [mem_reProdIm, mem_Ioo, mem_singleton_iff] at hw
      replace nh : w.re * rexp w.re ≤ -(rexp 1)⁻¹ := by
        simpa [z, mem_reProdIm, exp_re, exp_im, hw.right] using nh
      have : (-1) * rexp (-1) < w.re * rexp w.re :=
        Function.strictMonoOn_of_rightInvOn_of_mapsTo Real.strictMonoOn_lambertWZero
          invOn_mul_exp_lambertWZero.right bijOn_mul_exp_Ici.mapsTo
            le_rfl hw.left.left.le hw.left.left
      grind [Real.exp_neg, neg_exp_one_inv_le_mul_exp w.re]
  · simp only [hk, ↓reduceIte, ne_eq, not_false_eq_true, domain_of_ne_zero, mem_compl_iff,
      mem_singleton_iff] at nh Hz
    have hz : z.arg = π :=
      arg_eq_pi_iff.mpr ⟨lt_of_le_of_ne nh.left
        (fun nh' => Hz <| Complex.ext nh' nh.right), nh.right⟩
    rw [openRange_of_ne_zero hk] at hw
    grind [arg_mul_exp_eq_of_mem hw₀ ⟨hw.left, hw.right.le⟩]

end LambertW

open LambertW

-- /-- **TODO** doc -/
-- theorem conj_lambertW_eq_lambertW_neg_conj (hz : z ∈ LambertW.slitPlane k) :
--     conj (W_ k z) = W_ (-k) (conj z) := by
--   sorry

-- use which one? `((1 + W_ k z) * cexp (W_ k z))⁻¹`, `(z + cexp (W_ k z))⁻¹`.
theorem _root_.hasStrictDerivAt_lambertW (hz : z ∈ LambertW.slitPlane k) :
    HasStrictDerivAt (W_ k) (z + cexp (W_ k z))⁻¹ z := by
  set w₀ : ℂ := W_ k z
  have hw₀z : W_ k z * cexp (W_ k z) = z :=
    lambertW_mul_exp_lambertW_of_mem_domain <| slitPlane_subset_domain hz
  have hw₀' : w₀ ∈ openRange k := mapsTo_lambertW_slitPlane hz
  have : HasStrictDerivAt (W_ k) (1 * cexp w₀ + w₀ * cexp w₀)⁻¹ (w₀ * cexp w₀) :=
    HasStrictDerivAt.to_local_left_inverse
      (hasStrictDerivAt_id w₀ |>.mul <| hasStrictDerivAt_exp w₀) ?_ ?_
  · convert this using 2
    · rw [one_mul, hw₀z, add_comm]
    · exact hw₀z.symm
  · simp [← one_add_mul, add_eq_zero_iff_eq_neg', openRange_ne_neg_one hw₀']
  · filter_upwards [isOpen_openRange.eventually_mem hw₀'] with w hw using
      lambertW_mul_exp_of_mem_range <| openRange_subset_range hw

theorem _root_.hasDerivAt_lambertW (hz : z ∈ LambertW.slitPlane k) :
    HasDerivAt (W_ k) (z + cexp (W_ k z))⁻¹ z := hasStrictDerivAt_lambertW hz |>.hasDerivAt

@[fun_prop]
theorem _root_.differentiableAt_lambertW (hz : z ∈ LambertW.slitPlane k) :
    DifferentiableAt ℂ (W_ k) z := hasDerivAt_lambertW hz |>.differentiableAt

theorem _root_.differentiableOn_lambertW (hs : s ⊆ LambertW.slitPlane k) :
    DifferentiableOn ℂ (W_ k) s :=
  fun _x hx => hasDerivAt_lambertW (hs hx) |>.differentiableAt.differentiableWithinAt

theorem _root_.deriv_lambertW (hz : z ∈ LambertW.slitPlane k) :
    deriv (W_ k) z = (z + cexp (W_ k z))⁻¹ := hasDerivAt_lambertW hz |>.deriv

theorem _root_.deriv_lambertW' (hz : z ∈ LambertW.slitPlane k) :
    deriv (W_ k) z = ((1 + W_ k z) * cexp (W_ k z))⁻¹ := by
  rw [deriv_lambertW hz]
  nth_rw 1 [← lambertW_mul_exp_lambertW_of_mem_domain <| slitPlane_subset_domain hz]
  ring

-- TODO : add `continuousAt_lambertWZero` `continuousAt_lambertWNegOne`
-- /-- For real version, see `continuousAt_lambertWZero` or `continuousAt_lambertWNegOne`. -/
theorem _root_.continuousAt_lambertW (hz : z ∈ LambertW.slitPlane k) :
    ContinuousAt (W_ k) z := hasDerivAt_lambertW hz |>.continuousAt

theorem _root_.continuousOn_lambertW : ContinuousOn (W_ k) (LambertW.slitPlane k) :=
  continuousOn_of_forall_continuousAt fun _z => continuousAt_lambertW

theorem _root_.analyticOnNhd_lambertW : AnalyticOnNhd ℂ (W_ k) (LambertW.slitPlane k) :=
  (differentiableOn_lambertW Subset.rfl).analyticOnNhd LambertW.isOpen_slitPlane

theorem _root_.analyticOn_lambertW : AnalyticOn ℂ (W_ k) (LambertW.slitPlane k) :=
  analyticOnNhd_lambertW.analyticOn

open scoped ContDiff in
theorem _root_.contDiffOn_lambertW : ContDiffOn ℂ ω (W_ k) (LambertW.slitPlane k) :=
  differentiableOn_lambertW Subset.rfl |>.contDiffOn LambertW.isOpen_slitPlane

open scoped ContDiff in
theorem _root_.contDiffAt_lambertW (hz : z ∈ LambertW.slitPlane k) : ContDiffAt ℂ ω (W_ k) z :=
  contDiffOn_lambertW z hz |>.contDiffAt <| LambertW.isOpen_slitPlane.mem_nhds hz

theorem _root_.analyticAt_lambertW (hz : z ∈ LambertW.slitPlane k) :
    AnalyticAt ℂ (W_ k) z := contDiffAt_lambertW hz |>.analyticAt

variable {l : Filter α} {f : α -> ℂ}

theorem _root_.Filter.Tendsto.lambertW {x : ℂ} (h : Tendsto f l (𝓝 x))
    (hx : x ∈ LambertW.slitPlane k) : Tendsto (fun t => W_ k (f t)) l (𝓝 <| W_ k x) :=
  (continuousAt_lambertW hx).tendsto.comp h

variable [TopologicalSpace α]

nonrec theorem _root_.ContinuousAt.lambertW {x : α} (h₁ : ContinuousAt f x)
    (h₂ : f x ∈ LambertW.slitPlane k) : ContinuousAt (fun t => W_ k (f t)) x :=
  h₁.lambertW h₂

nonrec theorem _root_.ContinuousWithinAt.lambertW {s : Set α} {x : α}
    (h₁ : ContinuousWithinAt f s x) (h₂ : f x ∈ LambertW.slitPlane k) :
    ContinuousWithinAt (fun t => W_ k (f t)) s x :=
  h₁.lambertW h₂

nonrec theorem _root_.ContinuousOn.lambertW {s : Set α} (h₁ : ContinuousOn f s)
    (h₂ : ∀ x ∈ s, f x ∈ LambertW.slitPlane k) : ContinuousOn (fun t => W_ k (f t)) s :=
  fun x hx => (h₁ x hx).lambertW (h₂ x hx)

nonrec theorem _root_.Continuous.lambertW (h₁ : Continuous f)
    (h₂ : ∀ x, f x ∈ LambertW.slitPlane k) : Continuous fun t => W_ k (f t) :=
  continuous_iff_continuousAt.mpr fun x => h₁.continuousAt.lambertW (h₂ x)

/-- TODO doc -/
def mulExpOpenPartialHomeomorph (k : ℤ) : OpenPartialHomeomorph ℂ ℂ where
  toFun := fun w => w * cexp w
  invFun := W_ k
  source := LambertW.openRange k
  target := LambertW.slitPlane k
  map_source' w h := mapsTo_mul_exp_openRange h
  map_target' z h := mapsTo_lambertW_slitPlane h
  left_inv' _x hx := lambertW_mul_exp_of_mem_range <| openRange_subset_range hx
  right_inv' _x hx := lambertW_mul_exp_lambertW_of_mem_domain <| slitPlane_subset_domain hx
  open_source := LambertW.isOpen_openRange
  open_target := LambertW.isOpen_slitPlane
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := continuousOn_id.lambertW fun _ => id

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem _root_.HasStrictFDerivAt.lambertW {f : E → ℂ} {f' : StrongDual ℂ E} {x : E}
    (h₁ : HasStrictFDerivAt f f' x) (h₂ : f x ∈ LambertW.slitPlane k) :
    HasStrictFDerivAt (fun t => W_ k (f t)) ((f x + cexp (W_ k (f x)))⁻¹ • f') x :=
  (hasStrictDerivAt_lambertW h₂).comp_hasStrictFDerivAt x h₁

theorem _root_.HasStrictDerivAt.lambertW {f : ℂ → ℂ} {f' x : ℂ}
    (h₁ : HasStrictDerivAt f f' x) (h₂ : f x ∈ LambertW.slitPlane k) :
    HasStrictDerivAt (fun t => W_ k (f t)) (f' / (f x + cexp (W_ k (f x)))) x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_lambertW h₂).comp x h₁

theorem _root_.HasFDerivAt.lambertW {f : E → ℂ} {f' : StrongDual ℂ E} {x : E}
    (h₁ : HasFDerivAt f f' x) (h₂ : f x ∈ LambertW.slitPlane k) :
    HasFDerivAt (fun t => W_ k (f t)) ((f x + cexp (W_ k (f x)))⁻¹ • f') x :=
  (hasStrictDerivAt_lambertW h₂).hasDerivAt.comp_hasFDerivAt x h₁

theorem _root_.HasDerivAt.lambertW {f : ℂ → ℂ} {f' x : ℂ}
    (h₁ : HasDerivAt f f' x) (h₂ : f x ∈ LambertW.slitPlane k) :
    HasDerivAt (fun t => W_ k (f t)) (f' / (f x + cexp (W_ k (f x)))) x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_lambertW h₂).hasDerivAt.comp x h₁

theorem _root_.DifferentiableAt.lambertW {f : E → ℂ} {x : E} (h₁ : DifferentiableAt ℂ f x)
    (h₂ : f x ∈ LambertW.slitPlane k) : DifferentiableAt ℂ (fun t => W_ k (f t)) x :=
  (h₁.hasFDerivAt.lambertW h₂).differentiableAt

theorem _root_.HasFDerivWithinAt.lambertW {f : E → ℂ} {f' : StrongDual ℂ E} {s : Set E} {x : E}
    (h₁ : HasFDerivWithinAt f f' s x) (h₂ : f x ∈ LambertW.slitPlane k) :
    HasFDerivWithinAt (fun t => W_ k (f t)) ((f x + cexp (W_ k (f x)))⁻¹ • f') s x :=
  (hasStrictDerivAt_lambertW h₂).hasDerivAt.comp_hasFDerivWithinAt x h₁

theorem _root_.HasDerivWithinAt.lambertW {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}
    (h₁ : HasDerivWithinAt f f' s x) (h₂ : f x ∈ LambertW.slitPlane k) :
    HasDerivWithinAt (fun t => W_ k (f t)) (f' / (f x + cexp (W_ k (f x)))) s x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_lambertW h₂).hasDerivAt.comp_hasDerivWithinAt x h₁

theorem _root_.DifferentiableWithinAt.lambertW {f : E → ℂ} {s : Set E} {x : E}
    (h₁ : DifferentiableWithinAt ℂ f s x) (h₂ : f x ∈ LambertW.slitPlane k) :
    DifferentiableWithinAt ℂ (fun t => W_ k (f t)) s x :=
  (h₁.hasFDerivWithinAt.lambertW h₂).differentiableWithinAt

theorem _root_.DifferentiableOn.lambertW {f : E → ℂ} {s : Set E} (h₁ : DifferentiableOn ℂ f s)
    (h₂ : ∀ x ∈ s, f x ∈ LambertW.slitPlane k) : DifferentiableOn ℂ (fun t => W_ k (f t)) s :=
  fun x hx => (h₁ x hx).lambertW (h₂ x hx)

theorem _root_.Differentiable.lambertW {f : E → ℂ} (h₁ : Differentiable ℂ f)
    (h₂ : ∀ x, f x ∈ LambertW.slitPlane k) : Differentiable ℂ fun t => W_ k (f t) := fun x =>
  (h₁ x).lambertW (h₂ x)

end Complex
