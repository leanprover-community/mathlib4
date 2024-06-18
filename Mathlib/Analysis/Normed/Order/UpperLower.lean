/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Field.Pi
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.Normed.Order.Basic
import Mathlib.Algebra.Order.UpperLower
import Mathlib.Data.Real.Sqrt

#align_import analysis.normed.order.upper_lower from "leanprover-community/mathlib"@"992efbda6f85a5c9074375d3c7cb9764c64d8f72"

/-!
# Upper/lower/order-connected sets in normed groups

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.
-/


open Function Metric Set

variable {α ι : Type*}

section MetricSpace

variable [NormedOrderedGroup α] {s : Set α}

@[to_additive IsUpperSet.thickening]
protected theorem IsUpperSet.thickening' (hs : IsUpperSet s) (ε : ℝ) :
    IsUpperSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left
#align is_upper_set.thickening' IsUpperSet.thickening'
#align is_upper_set.thickening IsUpperSet.thickening

@[to_additive IsLowerSet.thickening]
protected theorem IsLowerSet.thickening' (hs : IsLowerSet s) (ε : ℝ) :
    IsLowerSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left
#align is_lower_set.thickening' IsLowerSet.thickening'
#align is_lower_set.thickening IsLowerSet.thickening

@[to_additive IsUpperSet.cthickening]
protected theorem IsUpperSet.cthickening' (hs : IsUpperSet s) (ε : ℝ) :
    IsUpperSet (cthickening ε s) := by
  rw [cthickening_eq_iInter_thickening'']
  exact isUpperSet_iInter₂ fun δ _ => hs.thickening' _
#align is_upper_set.cthickening' IsUpperSet.cthickening'
#align is_upper_set.cthickening IsUpperSet.cthickening

@[to_additive IsLowerSet.cthickening]
protected theorem IsLowerSet.cthickening' (hs : IsLowerSet s) (ε : ℝ) :
    IsLowerSet (cthickening ε s) := by
  rw [cthickening_eq_iInter_thickening'']
  exact isLowerSet_iInter₂ fun δ _ => hs.thickening' _
#align is_lower_set.cthickening' IsLowerSet.cthickening'
#align is_lower_set.cthickening IsLowerSet.cthickening

end MetricSpace

/-! ### `ℝⁿ` -/


section Finite

variable [Finite ι] {s : Set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

theorem IsUpperSet.mem_interior_of_forall_lt (hs : IsUpperSet s) (hx : x ∈ closure s)
    (h : ∀ i, x i < y i) : y ∈ interior s := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : ∀ i, z i < y i := by
    refine fun i => (hxy _).trans_le' (sub_le_iff_le_add'.1 <| (le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs, ← dist_eq_norm']
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine mem_interior.2 ⟨ball y δ, ?_, isOpen_ball, mem_ball_self hδ⟩
  rintro w hw
  refine hs (fun i => ?_) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((lt_sub_iff_add_lt.2 <| hyz _).trans (hw _ <| mem_univ _).1).le
#align is_upper_set.mem_interior_of_forall_lt IsUpperSet.mem_interior_of_forall_lt

theorem IsLowerSet.mem_interior_of_forall_lt (hs : IsLowerSet s) (hx : x ∈ closure s)
    (h : ∀ i, y i < x i) : y ∈ interior s := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : ∀ i, y i < z i := by
    refine fun i =>
      (lt_sub_iff_add_lt.2 <| hxy _).trans_le (sub_le_comm.1 <| (le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs, ← dist_eq_norm]
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine mem_interior.2 ⟨ball y δ, ?_, isOpen_ball, mem_ball_self hδ⟩
  rintro w hw
  refine hs (fun i => ?_) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((hw _ <| mem_univ _).2.trans <| hyz _).le
#align is_lower_set.mem_interior_of_forall_lt IsLowerSet.mem_interior_of_forall_lt

end Finite

section Fintype

variable [Fintype ι] {s : Set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

theorem IsUpperSet.exists_subset_ball (hs : IsUpperSet s) (hx : x ∈ closure s) (hδ : 0 < δ) :
    ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s := by
  refine ⟨x + const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · rw [dist_self_add_left]
    refine (add_le_add_left (pi_norm_const_le <| 3 / 4 * δ) _).trans_eq ?_
    simp only [norm_mul, norm_div, Real.norm_eq_abs]
    simp only [gt_iff_lt, zero_lt_three, abs_of_pos, zero_lt_four, abs_of_pos hδ]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => ?_
  rw [mem_closedBall, dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith
#align is_upper_set.exists_subset_ball IsUpperSet.exists_subset_ball

theorem IsLowerSet.exists_subset_ball (hs : IsLowerSet s) (hx : x ∈ closure s) (hδ : 0 < δ) :
    ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s := by
  refine ⟨x - const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · rw [dist_self_sub_left]
    refine (add_le_add_left (pi_norm_const_le <| 3 / 4 * δ) _).trans_eq ?_
    simp only [norm_mul, norm_div, Real.norm_eq_abs, gt_iff_lt, zero_lt_three, abs_of_pos,
      zero_lt_four, abs_of_pos hδ]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => ?_
  rw [mem_closedBall, dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith
#align is_lower_set.exists_subset_ball IsLowerSet.exists_subset_ball

end Fintype
