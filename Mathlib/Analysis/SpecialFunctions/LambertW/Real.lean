module

public import Mathlib.Analysis.SpecialFunctions.LambetW.Basic

section TODO
-- /-- **TODO** doc -/
-- theorem conj_lambertW_eq_lambertW_neg_conj (hz : z ∈ LambertW.slitPlane k) :
--     conj (W_ k z) = W_ (-k) (conj z) := by
--   sorry

-- theorem LambertW.isOpen_domain : IsOpen (domain k) := by
--   change (if _ then _ else _ : Set ℂ) ∈ {y | IsOpen y}
--   simp [ite_mem]

-- theorem LambertW.isClosed_branchCut : IsClosed (branchCut k) :=
--   isClosed_Iic.reProdIm isClosed_singleton

-- theorem LambertW.isOpen_slitPlane : IsOpen (slitPlane k) :=
--   isClosed_branchCut.isOpen_compl

-- private theorem LambertW.isOpen_openRange_zero : IsOpen (openRange 0) := by
--   suffices openRange 0 =
--       Complex.slitPlane ∩ (fun w => w.arg + w.im) ⁻¹' Ioo (-π) π ∪ Metric.ball 0 1 by
--     simpa only [this] using
--       continuousOn_arg_add_im.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo |>.union
--         Metric.isOpen_ball
--   rw [openRange_zero]
--   ext w
--   constructor
--   · rintro (hidx | ⟨hre, him⟩)
--     · by_cases hs : w ∈ Complex.slitPlane
--       · exact Or.inl ⟨hs, hidx⟩
--       rw [Complex.mem_slitPlane_iff, not_or, not_not, not_lt] at hs
--       obtain ⟨hre, him⟩ := hs
--       rcases lt_or_eq_of_le hre with hre | hre
--       · exact False.elim <| lt_irrefl π <|
--           arg_add_im_eq_pi_of_arg_eq_pi (arg_eq_pi_iff.mpr ⟨hre, him⟩) ▸ hidx.right
--       · exact Or.inr <| (Complex.ext (w := 0) hre him) ▸ Metric.mem_ball_self zero_lt_one
--     · rw [mem_preimage, mem_singleton_iff] at him
--       refine Or.inr <| mem_ball_zero_iff.mpr ?_
--       rw [Complex.ext (z := w) (w := w.re) rfl him, norm_real, norm_eq_abs, abs_of_neg hre.right]
--       linarith [hre.left]
--   rintro (⟨-, hidx⟩ | hb)
--   · exact Or.inl hidx
--   rw [mem_ball_zero_iff] at hb
--   by_cases harg : w.arg = π
--   · obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp harg
--     refine Or.inr ⟨⟨?_, hre⟩, him⟩
--     rw [Complex.ext (z := w) (w := w.re) rfl him, norm_real, norm_eq_abs, abs_of_neg hre] at hb
--     linarith
--   left
--   replace harg : w.arg ∈ Ioo (-π) π := ⟨neg_pi_lt_arg w, lt_of_le_of_ne (arg_le_pi w) harg⟩
--   rw [mem_ofPred, ← norm_mul_sin_arg]
--   generalize w.arg = x at *
--   rw [show x + ‖w‖ * x.sin = (1 - ‖w‖) * x + ‖w‖ * (x + x.sin) by ring]
--   exact (convex_Ioo (-π) π) harg (add_sin_mem_Ioo_of_mem_Ioo harg)
--     (sub_nonneg_of_le hb.le) (norm_nonneg w) (sub_add_cancel 1 ‖w‖)

-- private theorem LambertW.isOpen_openRange_of_ne (hk : k ≠ 0) : IsOpen (openRange k) := by
--   suffices openRange k = Complex.slitPlane ∩
--       (fun w => w.arg + w.im) ⁻¹' Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) by
--     simpa only [this] using
--       continuousOn_arg_add_im.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo
--   rw [openRange_of_ne_zero hk]
--   ext w
--   refine ⟨fun hw => ⟨Classical.byContradiction fun nh => ?_, hw⟩, And.right⟩
--   rw [mem_slitPlane_iff_arg, not_and_or, not_not, not_not] at nh
--   rw [mem_ofPred] at hw
--   rcases nh with nh | nh
--   · rw [arg_eq_pi_iff.mp nh |>.right, add_zero] at hw
--     simp [nh, field, sub_lt_iff_lt_add, one_add_one_eq_two] at hw
--     norm_cast at hw
--     omega
--   · simp [nh, field, pi_pos, mul_neg_iff, pi_pos.not_gt] at hw
--     norm_cast at hw
--     omega

-- theorem LambertW.isOpen_openRange : IsOpen (openRange k) :=
--   em (k = 0) |>.elim (fun hk => hk ▸ isOpen_openRange_zero) isOpen_openRange_of_ne

-- theorem _root_.continuousAt_clambertW {z : ℂ} (h : z ∈ LambertW.slitPlane k) :
--     ContinuousAt (W_ k) z := by
--   sorry

-- theorem _root_.Filter.Tendsto.clambertW {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x))
--     (hx : x ∈ LambertW.slitPlane k) : Tendsto (fun t => W_ k (f t)) l (𝓝 <| W_ k x) :=
--   (continuousAt_clambertW hx).tendsto.comp h

-- variable [TopologicalSpace α]

-- nonrec theorem _root_.ContinuousAt.clambertW {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x)
--     (h₂ : f x ∈ LambertW.slitPlane k) : ContinuousAt (fun t => W_ k (f t)) x :=
--   h₁.clambertW h₂

-- nonrec theorem _root_.ContinuousWithinAt.clambertW {f : α → ℂ} {s : Set α} {x : α}
--     (h₁ : ContinuousWithinAt f s x) (h₂ : f x ∈ LambertW.slitPlane k) :
--     ContinuousWithinAt (fun t => W_ k (f t)) s x :=
--   h₁.clambertW h₂

-- nonrec theorem _root_.ContinuousOn.clambertW {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
--     (h₂ : ∀ x ∈ s, f x ∈ LambertW.slitPlane k) : ContinuousOn (fun t => W_ k (f t)) s :=
--   fun x hx => (h₁ x hx).clambertW (h₂ x hx)

-- nonrec theorem _root_.Continuous.clambertW {f : α → ℂ} (h₁ : Continuous f)
--     (h₂ : ∀ x, f x ∈ LambertW.slitPlane k) : Continuous fun t => W_ k (f t) :=
--   continuous_iff_continuousAt.mpr fun x => h₁.continuousAt.clambertW (h₂ x)

-- /-- TODO doc -/
-- def mulExpOpenPartialHomeomorph : OpenPartialHomeomorph ℂ ℂ where
--   toFun := fun w => w * cexp w
--   invFun := lambertW k
--   source := LambertW.openRange k
--   target := LambertW.slitPlane k
--   map_source' := by
--     sorry
--   map_target' z h := by
--     sorry
--   left_inv' _x hx := apply_mul_exp_of_mem_range <| openRange_subset_range hx
--   right_inv' _x hx := apply_mul_exp_apply_of_mem_domain <| slitPlane_subset_domain hx
--   open_source := isOpen_openRange
--   open_target := LambertW.isOpen_slitPlane
--   continuousOn_toFun := by fun_prop
--   continuousOn_invFun := continuousOn_id.clambertW fun _ => id
end TODO

namespace Real

open Set

variable {x y : ℝ}

/-- TODO doc -/
def lambertWZero : ℝ -> ℝ := fun x => (Complex.lambertW 0 x).re

/-- TODO doc -/
def lambertWNegOne : ℝ -> ℝ := fun x => (Complex.lambertW (-1) x).re

@[inherit_doc] scoped[RealLambertW] notation "W₀" => Real.lambertWZero
recommended_spelling "lambertWZero" for "W₀" in [lambertWZero, RealLambertW.«termW₀»]

@[inherit_doc] scoped[RealLambertW] notation "W₋₁" => Real.lambertWNegOne
recommended_spelling "lambertWNegOne" for "W₋₁" in [lambertWNegOne, RealLambertW.«termW₋₁»]

open scoped RealLambertW

/-- TODO doc -/
scoped[OmegaConstant] notation "Ω" => W₀ 1
recommended_spelling "omegaConstant" for "Ω" in [OmegaConstant.«termΩ»]

open scoped OmegaConstant

theorem invOn_lambertWZero_mul_exp :
    InvOn W₀ (fun x => x * rexp x) (Ici (-1)) (Ici (-(rexp 1)⁻¹)) := by
  sorry

theorem invOn_mul_exp_lambertWZero :
    InvOn (fun x => x * rexp x) W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) := by
  sorry

theorem invOn_lambertWNegOne_mul_exp :
    InvOn W₋₁ (fun x => x * rexp x) (Iic (-1)) (Ico (-(rexp 1)⁻¹) 0) := by
  sorry

theorem invOn_mul_exp_lambertWNegOne :
    InvOn (fun x => x * rexp x) W₋₁ (Ico (-(rexp 1)⁻¹) 0) (Iic (-1)) := by
  sorry

theorem bijOn_lambertWZero : BijOn W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) := by
  sorry

theorem bijOn_lambertWNegOne : BijOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) (Iic (-1)) := by
  sorry

theorem lambertWZero_mul_exp_of_le (hx : -1 ≤ x) : W₀ (x * rexp x) = x := by
  sorry

theorem lambertWZero_mul_exp_lambertWZero_of_le (hx : -(rexp 1)⁻¹ ≤ x) :
    W₀ x * rexp (W₀ x) = x := by
  sorry

theorem lambertWNegOne_mul_exp_of_le (hx : x ≤ -1) : W₋₁ (x * rexp x) = x := by
  sorry

theorem lambertWNegOne_mul_exp_lambertWNegOne_of_le (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    W₋₁ x * rexp (W₋₁ x) = x := by
  sorry

theorem strictMonoOn_lambertWZero : StrictMonoOn W₀ (Ici (-(rexp 1)⁻¹)) := by
  sorry

theorem strictAntiOn_lambetWNegOne : StrictAntiOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) := by
  sorry

@[simp]
theorem lambertWZero_zero : W₀ 0 = 0 := by
  nth_rw 1 [show 0 = 0 * rexp 0 from zero_mul _ |>.symm, lambertWZero_mul_exp_of_le]
  norm_num

theorem lambertWZero_pos_of_pos (hx : 0 < x) : 0 < W₀ x := by
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  exact lambertWZero_zero ▸ strictMonoOn_lambertWZero this (this.trans hx.le) hx

theorem lambertWZero_nonneg_of_nonneg (hx : 0 ≤ x) : 0 ≤ W₀ x := by
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  exact lambertWZero_zero ▸ strictMonoOn_lambertWZero.monotoneOn this (this.trans hx) hx

theorem lambertWZero_neg_of_lt (hx : x < -(rexp 1)⁻¹) : W₀ x < 0 := by
  sorry

theorem lambertWZero_neg_of_neg (hx : x < 0) : W₀ x < 0 := by
  rcases lt_or_ge x (-(rexp 1)⁻¹) with hx' | hx'
  · exact lambertWZero_neg_of_lt hx'
  · exact lambertWZero_zero ▸ strictMonoOn_lambertWZero hx' (hx'.trans hx.le) hx

theorem lambertWZero_nonpos_of_nonpos (hx : x ≤ 0) : W₀ x ≤ 0 := by
  rcases lt_or_ge x (-(rexp 1)⁻¹) with hx' | hx'
  · exact lambertWZero_neg_of_lt hx' |>.le
  · exact lambertWZero_zero ▸ strictMonoOn_lambertWZero.monotoneOn hx' (hx'.trans hx) hx

theorem lambertWZero_ne_zero_of_ne_zero (hx : x ≠ 0) : W₀ x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact lambertWZero_neg_of_neg hx |>.ne
  · exact lambertWZero_pos_of_pos hx |>.ne'

theorem lambertWNegOne_neg_of_ne_zero (hx : x ≠ 0) : W₋₁ x < 0 := by
  sorry

open Qq Mathlib.Meta.Positivity in
/-- TODO doc -/
@[positivity Real.lambertWZero _]
meta def _root_.Mathlib.Meta.Positivity.evalLambertWZero :
    PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(W₀ $a) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure <| .positive q(lambertWZero_pos_of_pos $pa)
    | .nonnegative pa => pure <| .nonnegative q(lambertWZero_nonneg_of_nonneg $pa)
    | .nonzero pa => pure <| .nonzero q(lambertWZero_ne_zero_of_ne_zero $pa)
    | _ => pure .none
  | _, _, _ => throwError "not Real.lambertWZero"

theorem zero_lt_omegaConstant : 0 < Ω := by
  positivity

theorem omegaConstant_lt_one : Ω < 1 := by
  sorry

--  TODO
-- theorem lambertWZero_add_lambertWZero_of_pos (hx : 0 < x) (hy : 0 < y) :
--     W₀ x + W₀ y = W₀ (x * y / W₀ x + x * y / W₀ y) := by
--   sorry

end Real

#lint
