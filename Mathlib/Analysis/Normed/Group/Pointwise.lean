/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

#align_import analysis.normed.group.pointwise from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/


open Metric Set Pointwise Topology

variable {E : Type*}

section SeminormedGroup

variable [SeminormedGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

@[to_additive]
theorem Metric.Bounded.mul (hs : Bounded s) (ht : Bounded t) : Bounded (s * t) := by
  obtain ⟨Rs, hRs⟩ : ∃ R, ∀ x ∈ s, ‖x‖ ≤ R := hs.exists_norm_le'
  -- ⊢ Bounded (s * t)
  obtain ⟨Rt, hRt⟩ : ∃ R, ∀ x ∈ t, ‖x‖ ≤ R := ht.exists_norm_le'
  -- ⊢ Bounded (s * t)
  refine' bounded_iff_forall_norm_le'.2 ⟨Rs + Rt, _⟩
  -- ⊢ ∀ (x : E), x ∈ s * t → ‖x‖ ≤ Rs + Rt
  rintro z ⟨x, y, hx, hy, rfl⟩
  -- ⊢ ‖(fun x x_1 => x * x_1) x y‖ ≤ Rs + Rt
  exact norm_mul_le_of_le (hRs x hx) (hRt y hy)
  -- 🎉 no goals
#align metric.bounded.mul Metric.Bounded.mul
#align metric.bounded.add Metric.Bounded.add

@[to_additive]
theorem Metric.Bounded.inv : Bounded s → Bounded s⁻¹ := by
  simp_rw [bounded_iff_forall_norm_le', ← image_inv, ball_image_iff, norm_inv']
  -- ⊢ (∃ C, ∀ (x : E), x ∈ s → ‖x‖ ≤ C) → ∃ C, ∀ (x : E), x ∈ s → ‖x‖ ≤ C
  exact id
  -- 🎉 no goals
#align metric.bounded.inv Metric.Bounded.inv
#align metric.bounded.neg Metric.Bounded.neg

@[to_additive]
theorem Metric.Bounded.div (hs : Bounded s) (ht : Bounded t) : Bounded (s / t) :=
  (div_eq_mul_inv _ _).symm.subst <| hs.mul ht.inv
#align metric.bounded.div Metric.Bounded.div
#align metric.bounded.sub Metric.Bounded.sub

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

section EMetric

open EMetric

@[to_additive (attr := simp)]
theorem infEdist_inv_inv (x : E) (s : Set E) : infEdist x⁻¹ s⁻¹ = infEdist x s := by
  rw [← image_inv, infEdist_image isometry_inv]
  -- 🎉 no goals
#align inf_edist_inv_inv infEdist_inv_inv
#align inf_edist_neg_neg infEdist_neg_neg

@[to_additive]
theorem infEdist_inv (x : E) (s : Set E) : infEdist x⁻¹ s = infEdist x s⁻¹ := by
  rw [← infEdist_inv_inv, inv_inv]
  -- 🎉 no goals
#align inf_edist_inv infEdist_inv
#align inf_edist_neg infEdist_neg

end EMetric

variable (ε δ s t x y)

@[to_additive (attr := simp)]
theorem inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹ := by
  simp_rw [thickening, ← infEdist_inv]
  -- ⊢ {x | EMetric.infEdist x s < ENNReal.ofReal δ}⁻¹ = {x | EMetric.infEdist x⁻¹  …
  rfl
  -- 🎉 no goals
#align inv_thickening inv_thickening
#align neg_thickening neg_thickening

@[to_additive (attr := simp)]
theorem inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹ := by
  simp_rw [cthickening, ← infEdist_inv]
  -- ⊢ {x | EMetric.infEdist x s ≤ ENNReal.ofReal δ}⁻¹ = {x | EMetric.infEdist x⁻¹  …
  rfl
  -- 🎉 no goals
#align inv_cthickening inv_cthickening
#align neg_cthickening neg_cthickening

@[to_additive (attr := simp)]
theorem inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ := (IsometryEquiv.inv E).preimage_ball x δ
#align inv_ball inv_ball
#align neg_ball neg_ball

@[to_additive (attr := simp)]
theorem inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ :=
  (IsometryEquiv.inv E).preimage_closedBall x δ
#align inv_closed_ball inv_closedBall
#align neg_closed_ball neg_closedBall

@[to_additive]
theorem singleton_mul_ball : {x} * ball y δ = ball (x * y) δ := by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]
  -- 🎉 no goals
#align singleton_mul_ball singleton_mul_ball
#align singleton_add_ball singleton_add_ball

@[to_additive]
theorem singleton_div_ball : {x} / ball y δ = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]
  -- 🎉 no goals
#align singleton_div_ball singleton_div_ball
#align singleton_sub_ball singleton_sub_ball

@[to_additive]
theorem ball_mul_singleton : ball x δ * {y} = ball (x * y) δ := by
  rw [mul_comm, singleton_mul_ball, mul_comm y]
  -- 🎉 no goals
#align ball_mul_singleton ball_mul_singleton
#align ball_add_singleton ball_add_singleton

@[to_additive]
theorem ball_div_singleton : ball x δ / {y} = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]
  -- 🎉 no goals
#align ball_div_singleton ball_div_singleton
#align ball_sub_singleton ball_sub_singleton

@[to_additive]
theorem singleton_mul_ball_one : {x} * ball 1 δ = ball x δ := by simp
                                                                 -- 🎉 no goals
#align singleton_mul_ball_one singleton_mul_ball_one
#align singleton_add_ball_zero singleton_add_ball_zero

@[to_additive]
theorem singleton_div_ball_one : {x} / ball 1 δ = ball x δ := by
  rw [singleton_div_ball, div_one]
  -- 🎉 no goals
#align singleton_div_ball_one singleton_div_ball_one
#align singleton_sub_ball_zero singleton_sub_ball_zero

@[to_additive]
theorem ball_one_mul_singleton : ball 1 δ * {x} = ball x δ := by simp [ball_mul_singleton]
                                                                 -- 🎉 no goals
#align ball_one_mul_singleton ball_one_mul_singleton
#align ball_zero_add_singleton ball_zero_add_singleton

@[to_additive]
theorem ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ := by
  rw [ball_div_singleton, one_div]
  -- 🎉 no goals
#align ball_one_div_singleton ball_one_div_singleton
#align ball_zero_sub_singleton ball_zero_sub_singleton

@[to_additive]
theorem smul_ball_one : x • ball (1 : E) δ = ball x δ := by
  rw [smul_ball, smul_eq_mul, mul_one]
  -- 🎉 no goals
#align smul_ball_one smul_ball_one
#align vadd_ball_zero vadd_ball_zero

@[to_additive (attr := simp 1100)]
theorem singleton_mul_closedBall : {x} * closedBall y δ = closedBall (x * y) δ := by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_closedBall]
  -- 🎉 no goals
#align singleton_mul_closed_ball singleton_mul_closedBall
#align singleton_add_closed_ball singleton_add_closedBall

@[to_additive (attr := simp 1100)]
theorem singleton_div_closedBall : {x} / closedBall y δ = closedBall (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_closedBall, singleton_mul_closedBall]
  -- 🎉 no goals
#align singleton_div_closed_ball singleton_div_closedBall
#align singleton_sub_closed_ball singleton_sub_closedBall

@[to_additive (attr := simp 1100)]
theorem closedBall_mul_singleton : closedBall x δ * {y} = closedBall (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]
  -- 🎉 no goals
#align closed_ball_mul_singleton closedBall_mul_singleton
#align closed_ball_add_singleton closedBall_add_singleton

@[to_additive (attr := simp 1100)]
theorem closedBall_div_singleton : closedBall x δ / {y} = closedBall (x / y) δ := by
  simp [div_eq_mul_inv]
  -- 🎉 no goals
#align closed_ball_div_singleton closedBall_div_singleton
#align closed_ball_sub_singleton closedBall_sub_singleton

@[to_additive]
theorem singleton_mul_closedBall_one : {x} * closedBall 1 δ = closedBall x δ := by simp
                                                                                   -- 🎉 no goals
#align singleton_mul_closed_ball_one singleton_mul_closedBall_one
#align singleton_add_closed_ball_zero singleton_add_closedBall_zero

@[to_additive]
theorem singleton_div_closedBall_one : {x} / closedBall 1 δ = closedBall x δ := by
  rw [singleton_div_closedBall, div_one]
  -- 🎉 no goals
#align singleton_div_closed_ball_one singleton_div_closedBall_one
#align singleton_sub_closed_ball_zero singleton_sub_closedBall_zero

@[to_additive]
theorem closedBall_one_mul_singleton : closedBall 1 δ * {x} = closedBall x δ := by simp
                                                                                   -- 🎉 no goals
#align closed_ball_one_mul_singleton closedBall_one_mul_singleton
#align closed_ball_zero_add_singleton closedBall_zero_add_singleton

@[to_additive]
theorem closedBall_one_div_singleton : closedBall 1 δ / {x} = closedBall x⁻¹ δ := by simp
                                                                                     -- 🎉 no goals
#align closed_ball_one_div_singleton closedBall_one_div_singleton
#align closed_ball_zero_sub_singleton closedBall_zero_sub_singleton

@[to_additive (attr := simp 1100)]
theorem smul_closedBall_one : x • closedBall (1 : E) δ = closedBall x δ := by simp
                                                                              -- 🎉 no goals
#align smul_closed_ball_one smul_closedBall_one
#align vadd_closed_ball_zero vadd_closedBall_zero

@[to_additive]
theorem mul_ball_one : s * ball 1 δ = thickening δ s := by
  rw [thickening_eq_biUnion_ball]
  -- ⊢ s * ball 1 δ = ⋃ (x : E) (_ : x ∈ s), ball x δ
  convert iUnion₂_mul (fun x (_ : x ∈ s) => {x}) (ball (1 : E) δ)
  -- ⊢ s = ⋃ (i : E) (_ : i ∈ s), {i}
  exact s.biUnion_of_singleton.symm
  -- ⊢ ball x✝¹ δ = {x✝¹} * ball 1 δ
  ext x
  -- ⊢ x ∈ ball x✝¹ δ ↔ x ∈ {x✝¹} * ball 1 δ
  simp_rw [singleton_mul_ball, mul_one]
  -- 🎉 no goals
#align mul_ball_one mul_ball_one
#align add_ball_zero add_ball_zero

@[to_additive]
theorem div_ball_one : s / ball 1 δ = thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]
                                                           -- 🎉 no goals
#align div_ball_one div_ball_one
#align sub_ball_zero sub_ball_zero

@[to_additive]
theorem ball_mul_one : ball 1 δ * s = thickening δ s := by rw [mul_comm, mul_ball_one]
                                                           -- 🎉 no goals
#align ball_mul_one ball_mul_one
#align ball_add_zero ball_add_zero

@[to_additive]
theorem ball_div_one : ball 1 δ / s = thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]
                                                             -- 🎉 no goals
#align ball_div_one ball_div_one
#align ball_sub_zero ball_sub_zero

@[to_additive (attr := simp)]
theorem mul_ball : s * ball x δ = x • thickening δ s := by
  rw [← smul_ball_one, mul_smul_comm, mul_ball_one]
  -- 🎉 no goals
#align mul_ball mul_ball
#align add_ball add_ball

@[to_additive (attr := simp)]
theorem div_ball : s / ball x δ = x⁻¹ • thickening δ s := by simp [div_eq_mul_inv]
                                                             -- 🎉 no goals
#align div_ball div_ball
#align sub_ball sub_ball

@[to_additive (attr := simp)]
theorem ball_mul : ball x δ * s = x • thickening δ s := by rw [mul_comm, mul_ball]
                                                           -- 🎉 no goals
#align ball_mul ball_mul
#align ball_add ball_add

@[to_additive (attr := simp)]
theorem ball_div : ball x δ / s = x • thickening δ s⁻¹ := by simp [div_eq_mul_inv]
                                                             -- 🎉 no goals
#align ball_div ball_div
#align ball_sub ball_sub

variable {ε δ s t x y}

@[to_additive]
theorem IsCompact.mul_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s * closedBall (1 : E) δ = cthickening δ s := by
  rw [hs.cthickening_eq_biUnion_closedBall hδ]
  -- ⊢ s * closedBall 1 δ = ⋃ (x : E) (_ : x ∈ s), closedBall x δ
  ext x
  -- ⊢ x ∈ s * closedBall 1 δ ↔ x ∈ ⋃ (x : E) (_ : x ∈ s), closedBall x δ
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_iUnion, mem_closedBall, exists_and_left,
    mem_closedBall_one_iff, ← eq_div_iff_mul_eq'', div_one, exists_eq_right]
#align is_compact.mul_closed_ball_one IsCompact.mul_closedBall_one
#align is_compact.add_closed_ball_zero IsCompact.add_closedBall_zero

@[to_additive]
theorem IsCompact.div_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s / closedBall 1 δ = cthickening δ s := by simp [div_eq_mul_inv, hs.mul_closedBall_one hδ]
                                               -- 🎉 no goals
#align is_compact.div_closed_ball_one IsCompact.div_closedBall_one
#align is_compact.sub_closed_ball_zero IsCompact.sub_closedBall_zero

@[to_additive]
theorem IsCompact.closedBall_one_mul (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ * s = cthickening δ s := by rw [mul_comm, hs.mul_closedBall_one hδ]
                                               -- 🎉 no goals
#align is_compact.closed_ball_one_mul IsCompact.closedBall_one_mul
#align is_compact.closed_ball_zero_add IsCompact.closedBall_zero_add

@[to_additive]
theorem IsCompact.closedBall_one_div (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ / s = cthickening δ s⁻¹ := by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closedBall_one hδ]
  -- 🎉 no goals
#align is_compact.closed_ball_one_div IsCompact.closedBall_one_div
#align is_compact.closed_ball_zero_sub IsCompact.closedBall_zero_sub

@[to_additive]
theorem IsCompact.mul_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s * closedBall x δ = x • cthickening δ s := by
  rw [← smul_closedBall_one, mul_smul_comm, hs.mul_closedBall_one hδ]
  -- 🎉 no goals
#align is_compact.mul_closed_ball IsCompact.mul_closedBall
#align is_compact.add_closed_ball IsCompact.add_closedBall

@[to_additive]
theorem IsCompact.div_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s / closedBall x δ = x⁻¹ • cthickening δ s := by
  simp [div_eq_mul_inv, mul_comm, hs.mul_closedBall hδ]
  -- 🎉 no goals
#align is_compact.div_closed_ball IsCompact.div_closedBall
#align is_compact.sub_closed_ball IsCompact.sub_closedBall

@[to_additive]
theorem IsCompact.closedBall_mul (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by rw [mul_comm, hs.mul_closedBall hδ]
                                                   -- 🎉 no goals
#align is_compact.closed_ball_mul IsCompact.closedBall_mul
#align is_compact.closed_ball_add IsCompact.closedBall_add

@[to_additive]
theorem IsCompact.closedBall_div (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by
  simp [div_eq_mul_inv, hs.closedBall_mul hδ]
  -- 🎉 no goals
#align is_compact.closed_ball_div IsCompact.closedBall_div
#align is_compact.closed_ball_sub IsCompact.closedBall_sub

end SeminormedCommGroup
