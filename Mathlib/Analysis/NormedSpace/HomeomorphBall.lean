/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Oliver Nash

! This file was ported from Lean 3 source module analysis.normed_space.basic
! leanprover-community/mathlib commit bc91ed7093bf098d253401e69df601fc33dde156
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Analysis.NormedSpace.AddTorsor
import Mathlib.Analysis.NormedSpace.Pointwise
/-!
# (Local) homeomorphism between a normed space and a ball

In this file we show that a real (semi)normed vector space is homeomorphic to the unit ball.

We formalize it in two ways:

- as a `Homeomorph`, see `Homeomorph.unitBall`;
- as a `LocalHomeomorph` with `source = Set.univ` and `target = Metric.ball (0 : E) 1`.

While the former approach is more natural, the latter approach provides us
with a globally defined inverse function which makes it easier to say
that this homeomorphism is in fact a diffeomorphism.

We also show that the unit ball `Metric.ball (0 : E) 1` is homeomorphic
to a ball of positive radius in an affine space over `E`, see `LocalHomeomorph.unitBallBall`.

## Tags

homeomorphism, ball
-/

open Set Metric Pointwise
variable (E : Type _) [SeminormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

/-- Local homeomorphism between a real (semi)normed space and the unit ball.
See also `Homeomorph.unitBall`. -/
@[simps (config := { isSimp := false })]
protected def LocalHomeomorph.unitBall : LocalHomeomorph E E where
  toFun x := (1 + ‖x‖ ^ 2).sqrt⁻¹ • x
  invFun y := (1 - ‖(y : E)‖ ^ 2).sqrt⁻¹ • (y : E)
  source := univ
  target := ball 0 1
  map_source' x _ := by
    have : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← _root_.div_eq_inv_mul,
      div_lt_one (abs_pos.mpr <| Real.sqrt_ne_zero'.mpr this), ← abs_norm x, ← sq_lt_sq,
      abs_norm, Real.sq_sqrt this.le]
    exact lt_one_add _
  map_target' _ _ := trivial
  left_inv' x _ := by
    field_simp [norm_smul, smul_smul, (zero_lt_one_add_norm_sq x).ne', sq_abs,
      Real.sq_sqrt (zero_lt_one_add_norm_sq x).le, ← Real.sqrt_div (zero_lt_one_add_norm_sq x).le]
  right_inv' y hy := by
    have : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    field_simp [norm_smul, smul_smul, this.ne', sq_abs, Real.sq_sqrt this.le,
      ← Real.sqrt_div this.le]
  open_source := isOpen_univ
  open_target := isOpen_ball
  continuous_toFun := by
    suffices Continuous fun (x:E) => (1 + ‖x‖ ^ 2).sqrt⁻¹
     from (this.smul continuous_id).continuousOn
    refine' Continuous.inv₀ _ fun x => Real.sqrt_ne_zero'.mpr (by positivity)
    continuity
  continuous_invFun := by
    have : ∀ y ∈ ball (0 : E) 1, (1 - ‖(y : E)‖ ^ 2).sqrt ≠ 0 := fun y hy ↦ by
      rw [Real.sqrt_ne_zero']
      nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    exact ContinuousOn.smul (ContinuousOn.inv₀
      (continuousOn_const.sub (continuous_norm.continuousOn.pow _)).sqrt this) continuousOn_id


/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`homeomorphUnitBall_apply_coe` and `homeomorphUnitBall_symm_apply` as `@[simp]`.

See also `contDiff_homeomorphUnitBall` and `contDiffOn_homeomorphUnitBall_symm` for
smoothness properties that hold when `E` is an inner-product space. -/
@[simps! (config := { isSimp := false })]
def Homeomorph.unitBall [NormedSpace ℝ E] : E ≃ₜ ball (0 : E) 1 :=
  (Homeomorph.Set.univ _).symm.trans (LocalHomeomorph.unitBall E).toHomeomorphSourceTarget
#align homeomorph_unit_ball Homeomorph.unitBall

@[simp]
theorem Homeomorph.coe_unitBall_apply_zero [NormedSpace ℝ E] :
    (Homeomorph.unitBall E 0 : E) = 0 := by
  simp [unitBall_apply_coe, LocalHomeomorph.unitBall_apply]
#align coe_homeomorph_unit_ball_apply_zero Homeomorph.coe_unitBall_apply_zero

variable {E} {P : Type _}
variable [PseudoMetricSpace P] [NormedAddTorsor E P]

/-- Affine homeomorphism `(r • · +ᵥ c)` between a normed space and an add torsor over this space,
interpreted as a `LocalHomeomorph` between `Metric.ball 0 1` and `Metric.ball c r`. -/
@[simps!]
def LocalHomeomorph.unitBallBall (c : P) (r : ℝ) (hr : 0 < r) : LocalHomeomorph E P :=
  ((Homeomorph.smulOfNeZero r hr.ne').trans
      (IsometryEquiv.vaddConst c).toHomeomorph).toLocalHomeomorphOfImageEq
      (ball 0 1) isOpen_ball (ball c r) <| by
    change (IsometryEquiv.vaddConst c) ∘ (r • ·) '' ball (0 : E) 1 = ball c r
    rw [image_comp, image_smul, smul_unitBall hr.ne', IsometryEquiv.image_ball]
    simp [abs_of_pos hr]
