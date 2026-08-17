/-
Copyright (c) 2026 Ryan Shin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Shin
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Charts for the closed unit ball: the interior chart and the radial unit map

First installment of a series giving the closed unit ball in
`EuclideanSpace ℝ (Fin n)` a smooth manifold-with-boundary structure over
`EuclideanHalfSpace n` — the first such structure above dimension 1
(cf. `Instances/Real.lean` for the 1-dimensional `Icc` instance, whose
idioms this file follows: charts as `OpenPartialHomeomorph` into the
half-space, inverses made total by clamping, correctness proved on `target`).

This file provides:

* `DiskInteriorChart` — the chart covering the open ball, shifting by
  `2 • e₀` into the half-space interior; its inverse shifts back and
  radially clamps (`radialClamp`), which is total and agrees with the true
  inverse on the target.
* `unitOr` — the radial unit map into the sphere, made total by a junk value
  at `0`, with the rescaling identities and continuity away from the origin
  needed by the boundary charts of the sequel.

Follow-ups add the boundary charts, the `ChartedSpace` instance, and the
`IsManifold (𝓡∂ n)` instance.
-/

@[expose] public section

open Set Metric

open scoped ContDiff Manifold

noncomputable section

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Each coordinate of a Euclidean vector is bounded by its norm. -/
lemma EuclideanSpace.abs_coord_le_norm (w : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |w i| ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  have h1 : |w i| ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have h2 : (0 : ℝ) ≤ ∑ j, ‖w j‖ ^ 2 := by positivity
  nlinarith [Real.sq_sqrt h2, Real.sqrt_nonneg (∑ j, ‖w j‖ ^ 2), abs_nonneg (w i)]

/-- The center offset: twice the first standard basis vector. -/
def diskShift (n : ℕ) [NeZero n] : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single (0 : Fin n) (2 : ℝ)

/-- The radial clamp: identity on the closed unit ball, radial projection
outside. Total by `0⁻¹ = 0`. -/
def radialClamp (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1 ⊓ ‖w‖⁻¹) • w

omit [NeZero n] in
lemma radialClamp_of_le (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ ≤ 1) :
    radialClamp w = w := by
  rcases eq_or_ne w 0 with h | h
  · simp [radialClamp, h]
  · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr h
    have : (1 : ℝ) ≤ ‖w‖⁻¹ := (one_le_inv₀ hpos).mpr hw
    simp [radialClamp, inf_of_le_left this]

omit [NeZero n] in
lemma norm_radialClamp_le (w : EuclideanSpace ℝ (Fin n)) :
    ‖radialClamp w‖ ≤ 1 := by
  rcases le_or_gt ‖w‖ 1 with h | h
  · rw [radialClamp_of_le w h]; exact h
  · have hpos : 0 < ‖w‖ := lt_trans one_pos h
    have hinv : ‖w‖⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr h.le
    have h0 : (0 : ℝ) ≤ ‖w‖⁻¹ := inv_nonneg.mpr hpos.le
    rw [radialClamp, inf_of_le_right hinv, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg h0, inv_mul_cancel₀ (ne_of_gt hpos)]

/-- The interior chart of the closed unit ball: shift into the half-space. -/
def DiskInteriorChart :
    OpenPartialHomeomorph (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      (EuclideanHalfSpace n) where
  source := { z | ‖z.val‖ < 1 }
  target := { z | ‖z.val - diskShift n‖ < 1 }
  toFun z := ⟨z.val + diskShift n, by
    have hz : ‖z.val‖ ≤ 1 :=
      mem_closedBall_zero_iff.mp z.2
    have h1 : |z.val 0| ≤ 1 :=
      le_trans (EuclideanSpace.abs_coord_le_norm _ 0) hz
    have h2 : (z.val + diskShift n) 0 =
        z.val 0 + 2 := by
      simp [diskShift]
    rw [h2]
    have := abs_le.mp h1
    linarith [this.1]⟩
  invFun z := ⟨radialClamp (z.val - diskShift n),
    mem_closedBall_zero_iff.mpr (norm_radialClamp_le _)⟩
  map_source' := by
    intro z hz
    simpa [add_sub_cancel_right] using hz
  map_target' := by
    intro z hz
    simpa [radialClamp_of_le _ (le_of_lt hz)] using hz
  left_inv' := by
    intro z hz
    ext1
    simp only [add_sub_cancel_right]
    exact radialClamp_of_le _ (le_of_lt hz)
  right_inv' := by
    intro z hz
    ext1
    simp only [radialClamp_of_le _ (le_of_lt hz), sub_add_cancel]
  open_source := by
    have h : IsOpen { w : EuclideanSpace ℝ (Fin n) | ‖w‖ < 1 } := by
      simpa [ball, dist_zero_right] using
        isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)
    exact h.preimage continuous_subtype_val
  open_target := by
    have h : IsOpen { w : EuclideanSpace ℝ (Fin n) | ‖w - diskShift n‖ < 1 } := by
      simpa [ball, dist_eq_norm] using isOpen_ball (x := diskShift n) (ε := 1)
    exact h.preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Continuous.continuousOn
    exact (continuous_subtype_val.add continuous_const).subtype_mk _
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hg : Continuous (fun z :
        { z : EuclideanHalfSpace n | ‖z.val - diskShift n‖ < 1 } =>
        (⟨z.val.val - diskShift n,
          mem_closedBall_zero_iff.mpr (le_of_lt z.property)⟩ :
          closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
      ((continuous_subtype_val.comp continuous_subtype_val).sub
        continuous_const).subtype_mk _
    exact hg.congr fun z =>
      Subtype.ext (radialClamp_of_le _ (le_of_lt z.property)).symm

/-! ### Toward the boundary charts (Milestone 2a): the total radial unit map -/

/-- The radial unit vector of `x`, with junk value `p` at `x = 0`. Total, so
it can serve as a chart component; charts will exclude `0` from their
sources. -/
def unitOr (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (x : EuclideanSpace ℝ (Fin n)) : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  if h : x = 0 then p else
    ⟨‖x‖⁻¹ • x, by
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h
      simp [norm_smul, inv_mul_cancel₀ (ne_of_gt hpos)]⟩

omit [NeZero n] in
lemma unitOr_val_of_ne (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {x : EuclideanSpace ℝ (Fin n)} (h : x ≠ 0) :
    (unitOr p x).val = ‖x‖⁻¹ • x := by
  simp [unitOr, h]

omit [NeZero n] in
lemma smul_unitOr (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {x : EuclideanSpace ℝ (Fin n)} (h : x ≠ 0) :
    ‖x‖ • (unitOr p x).val = x := by
  rw [unitOr_val_of_ne p h, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

omit [NeZero n] in
lemma unitOr_smul (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {r : ℝ} (hr : 0 < r) (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    unitOr p (r • u.val) = u := by
  have hu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hune : u.val ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact one_ne_zero hu.symm
  have hne : r • u.val ≠ 0 := smul_ne_zero (ne_of_gt hr) hune
  ext1
  rw [unitOr_val_of_ne p hne, norm_smul, hu, mul_one, Real.norm_eq_abs,
    abs_of_pos hr, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]

omit [NeZero n] in
lemma continuousOn_unitOr (p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ContinuousOn (unitOr p) { x : EuclideanSpace ℝ (Fin n) | x ≠ 0 } := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hg : Continuous (fun z : { x : EuclideanSpace ℝ (Fin n) | x ≠ 0 } =>
      (⟨‖z.val‖⁻¹ • z.val, by
        have hpos : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
        simp [norm_smul, inv_mul_cancel₀ (ne_of_gt hpos)]⟩ :
        sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun z => norm_ne_zero_iff.mpr z.property)).smul continuous_subtype_val
  exact hg.congr fun z => Subtype.ext (unitOr_val_of_ne p z.property).symm
