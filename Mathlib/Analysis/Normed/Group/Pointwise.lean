/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/


open Metric Set Pointwise Topology

variable {E : Type*}

section SeminormedGroup

variable [SeminormedGroup E] {s t : Set E}

-- note: we can't use `LipschitzOnWith.isBounded_image2` here without adding `[IsIsometricSMul E E]`
@[to_additive]
theorem Bornology.IsBounded.mul (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s * t) := by
  obtain ⟨Rs, hRs⟩ : ∃ R, ∀ x ∈ s, ‖x‖ ≤ R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : ∃ R, ∀ x ∈ t, ‖x‖ ≤ R := ht.exists_norm_le'
  refine isBounded_iff_forall_norm_le'.2 ⟨Rs + Rt, ?_⟩
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact norm_mul_le_of_le' (hRs x hx) (hRt y hy)

@[to_additive]
theorem Bornology.IsBounded.of_mul (hst : IsBounded (s * t)) : IsBounded s ∨ IsBounded t :=
  AntilipschitzWith.isBounded_of_image2_left _ (fun x => (isometry_mul_right x).antilipschitz) hst

@[to_additive]
theorem Bornology.IsBounded.inv : IsBounded s → IsBounded s⁻¹ := by
  simp_rw [isBounded_iff_forall_norm_le', ← image_inv_eq_inv, forall_mem_image, norm_inv']
  exact id

@[to_additive]
theorem Bornology.IsBounded.div (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s / t) :=
  div_eq_mul_inv s t ▸ hs.mul ht.inv

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] {δ : ℝ} {s : Set E} {x y : E}

section EMetric

open EMetric

@[to_additive (attr := simp)]
theorem infEdist_inv_inv (x : E) (s : Set E) : infEdist x⁻¹ s⁻¹ = infEdist x s := by
  rw [← image_inv_eq_inv, infEdist_image isometry_inv]

@[to_additive]
theorem infEdist_inv (x : E) (s : Set E) : infEdist x⁻¹ s = infEdist x s⁻¹ := by
  rw [← infEdist_inv_inv, inv_inv]

@[to_additive]
theorem ediam_mul_le (x y : Set E) : EMetric.diam (x * y) ≤ EMetric.diam x + EMetric.diam y :=
  (LipschitzOnWith.ediam_image2_le (· * ·) _ _
        (fun _ _ => (isometry_mul_right _).lipschitz.lipschitzOnWith) fun _ _ =>
        (isometry_mul_left _).lipschitz.lipschitzOnWith).trans_eq <|
    by simp only [ENNReal.coe_one, one_mul]

end EMetric

variable (δ s x y)

@[to_additive (attr := simp)]
theorem inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹ := by
  simp_rw [thickening, ← infEdist_inv]
  rfl

@[to_additive (attr := simp)]
theorem inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹ := by
  simp_rw [cthickening, ← infEdist_inv]
  rfl

@[to_additive (attr := simp)]
theorem inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ := (IsometryEquiv.inv E).preimage_ball x δ

@[to_additive (attr := simp)]
theorem inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ :=
  (IsometryEquiv.inv E).preimage_closedBall x δ

@[to_additive]
theorem singleton_mul_ball : {x} * ball y δ = ball (x * y) δ := by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]

@[to_additive]
theorem singleton_div_ball : {x} / ball y δ = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]

@[to_additive]
theorem ball_mul_singleton : ball x δ * {y} = ball (x * y) δ := by
  rw [mul_comm, singleton_mul_ball, mul_comm y]

@[to_additive]
theorem ball_div_singleton : ball x δ / {y} = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]

@[to_additive]
theorem singleton_mul_ball_one : {x} * ball 1 δ = ball x δ := by simp

@[to_additive]
theorem singleton_div_ball_one : {x} / ball 1 δ = ball x δ := by
  rw [singleton_div_ball, div_one]

@[to_additive]
theorem ball_one_mul_singleton : ball 1 δ * {x} = ball x δ := by simp

@[to_additive]
theorem ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ := by
  rw [ball_div_singleton, one_div]

@[to_additive]
theorem smul_ball_one : x • ball (1 : E) δ = ball x δ := by
  rw [smul_ball, smul_eq_mul, mul_one]

@[to_additive (attr := simp 1100)]
theorem singleton_mul_closedBall : {x} * closedBall y δ = closedBall (x * y) δ := by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_closedBall]

@[to_additive (attr := simp 1100)]
theorem singleton_div_closedBall : {x} / closedBall y δ = closedBall (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_closedBall, singleton_mul_closedBall]

@[to_additive (attr := simp 1100)]
theorem closedBall_mul_singleton : closedBall x δ * {y} = closedBall (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]
theorem closedBall_div_singleton : closedBall x δ / {y} = closedBall (x / y) δ := by
  simp [div_eq_mul_inv]

@[to_additive]
theorem singleton_mul_closedBall_one : {x} * closedBall 1 δ = closedBall x δ := by simp

@[to_additive]
theorem singleton_div_closedBall_one : {x} / closedBall 1 δ = closedBall x δ := by
  rw [singleton_div_closedBall, div_one]

@[to_additive]
theorem closedBall_one_mul_singleton : closedBall 1 δ * {x} = closedBall x δ := by simp

@[to_additive]
theorem closedBall_one_div_singleton : closedBall 1 δ / {x} = closedBall x⁻¹ δ := by simp

@[to_additive (attr := simp 1100)]
theorem smul_closedBall_one : x • closedBall (1 : E) δ = closedBall x δ := by simp

@[to_additive]
theorem mul_ball_one : s * ball 1 δ = thickening δ s := by
  rw [thickening_eq_biUnion_ball]
  convert iUnion₂_mul (fun x (_ : x ∈ s) => {x}) (ball (1 : E) δ)
  · exact s.biUnion_of_singleton.symm
  ext x
  simp_rw [singleton_mul_ball, mul_one]

@[to_additive]
theorem div_ball_one : s / ball 1 δ = thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]

@[to_additive]
theorem ball_mul_one : ball 1 δ * s = thickening δ s := by rw [mul_comm, mul_ball_one]

@[to_additive]
theorem ball_div_one : ball 1 δ / s = thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]

@[to_additive (attr := simp)]
theorem mul_ball : s * ball x δ = x • thickening δ s := by
  rw [← smul_ball_one, mul_smul_comm, mul_ball_one]

@[to_additive (attr := simp)]
theorem div_ball : s / ball x δ = x⁻¹ • thickening δ s := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
theorem ball_mul : ball x δ * s = x • thickening δ s := by rw [mul_comm, mul_ball]

@[to_additive (attr := simp)]
theorem ball_div : ball x δ / s = x • thickening δ s⁻¹ := by simp [div_eq_mul_inv]

variable {δ s x y}

@[to_additive]
theorem IsCompact.mul_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s * closedBall (1 : E) δ = cthickening δ s := by
  rw [hs.cthickening_eq_biUnion_closedBall hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_iUnion, mem_closedBall,
    ← eq_div_iff_mul_eq'', div_one, exists_eq_right]

@[to_additive]
theorem IsCompact.div_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s / closedBall 1 δ = cthickening δ s := by simp [div_eq_mul_inv, hs.mul_closedBall_one hδ]

@[to_additive]
theorem IsCompact.closedBall_one_mul (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ * s = cthickening δ s := by rw [mul_comm, hs.mul_closedBall_one hδ]

@[to_additive]
theorem IsCompact.closedBall_one_div (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ / s = cthickening δ s⁻¹ := by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closedBall_one hδ]

@[to_additive]
theorem IsCompact.mul_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s * closedBall x δ = x • cthickening δ s := by
  rw [← smul_closedBall_one, mul_smul_comm, hs.mul_closedBall_one hδ]

@[to_additive]
theorem IsCompact.div_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s / closedBall x δ = x⁻¹ • cthickening δ s := by
  simp [div_eq_mul_inv, hs.mul_closedBall hδ]

@[to_additive]
theorem IsCompact.closedBall_mul (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by rw [mul_comm, hs.mul_closedBall hδ]

@[to_additive]
theorem IsCompact.closedBall_div (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by
  simp [hs.closedBall_mul hδ]

end SeminormedCommGroup
