/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies

! This file was ported from Lean 3 source module analysis.normed.group.pointwise
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/


open Metric Set

open Pointwise Topology

variable {E : Type _}

section SeminormedGroup

variable [SeminormedGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

@[to_additive]
theorem Metric.Bounded.mul (hs : Bounded s) (ht : Bounded t) : Bounded (s * t) :=
  by
  obtain ⟨Rs, hRs⟩ : ∃ R, ∀ x ∈ s, ‖x‖ ≤ R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : ∃ R, ∀ x ∈ t, ‖x‖ ≤ R := ht.exists_norm_le'
  refine' bounded_iff_forall_norm_le'.2 ⟨Rs + Rt, _⟩
  rintro z ⟨x, y, hx, hy, rfl⟩
  exact norm_mul_le_of_le (hRs x hx) (hRt y hy)
#align metric.bounded.mul Metric.Bounded.mul
#align metric.bounded.add Metric.Bounded.add

@[to_additive]
theorem Metric.Bounded.inv : Bounded s → Bounded s⁻¹ :=
  by
  simp_rw [bounded_iff_forall_norm_le', ← image_inv, ball_image_iff, norm_inv']
  exact id
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

section Emetric

open Emetric

@[to_additive]
theorem infEdist_inv (x : E) (s : Set E) : infEdist x⁻¹ s = infEdist x s⁻¹ :=
  eq_of_forall_le_iff fun r => by simp_rw [le_inf_edist, ← image_inv, ball_image_iff, edist_inv]
#align inf_edist_inv infEdist_inv
#align inf_edist_neg infEdist_neg

@[simp, to_additive]
theorem infEdist_inv_inv (x : E) (s : Set E) : infEdist x⁻¹ s⁻¹ = infEdist x s := by
  rw [infEdist_inv, inv_inv]
#align inf_edist_inv_inv infEdist_inv_inv
#align inf_edist_neg_neg infEdist_neg_neg

end Emetric

variable (ε δ s t x y)

@[simp, to_additive]
theorem inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹ :=
  by
  simp_rw [thickening, ← infEdist_inv]
  rfl
#align inv_thickening inv_thickening
#align neg_thickening neg_thickening

@[simp, to_additive]
theorem inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹ :=
  by
  simp_rw [cthickening, ← infEdist_inv]
  rfl
#align inv_cthickening inv_cthickening
#align neg_cthickening neg_cthickening

@[simp, to_additive]
theorem inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ :=
  by
  simp_rw [ball, ← dist_inv]
  rfl
#align inv_ball inv_ball
#align neg_ball neg_ball

@[simp, to_additive]
theorem inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ :=
  by
  simp_rw [closed_ball, ← dist_inv]
  rfl
#align inv_closed_ball inv_closedBall
#align neg_closed_ball neg_closedBall

@[to_additive]
theorem singleton_mul_ball : {x} * ball y δ = ball (x * y) δ := by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]
#align singleton_mul_ball singleton_mul_ball
#align singleton_add_ball singleton_add_ball

@[to_additive]
theorem singleton_div_ball : {x} / ball y δ = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]
#align singleton_div_ball singleton_div_ball
#align singleton_sub_ball singleton_sub_ball

@[to_additive]
theorem ball_mul_singleton : ball x δ * {y} = ball (x * y) δ := by
  rw [mul_comm, singleton_mul_ball, mul_comm y]
#align ball_mul_singleton ball_mul_singleton
#align ball_add_singleton ball_add_singleton

@[to_additive]
theorem ball_div_singleton : ball x δ / {y} = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]
#align ball_div_singleton ball_div_singleton
#align ball_sub_singleton ball_sub_singleton

@[to_additive]
theorem singleton_mul_ball_one : {x} * ball 1 δ = ball x δ := by simp
#align singleton_mul_ball_one singleton_mul_ball_one
#align singleton_add_ball_zero singleton_add_ball_zero

@[to_additive]
theorem singleton_div_ball_one : {x} / ball 1 δ = ball x δ := by simp [singleton_div_ball]
#align singleton_div_ball_one singleton_div_ball_one
#align singleton_sub_ball_zero singleton_sub_ball_zero

@[to_additive]
theorem ball_one_mul_singleton : ball 1 δ * {x} = ball x δ := by simp [ball_mul_singleton]
#align ball_one_mul_singleton ball_one_mul_singleton
#align ball_zero_add_singleton ball_zero_add_singleton

@[to_additive]
theorem ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ := by simp [ball_div_singleton]
#align ball_one_div_singleton ball_one_div_singleton
#align ball_zero_sub_singleton ball_zero_sub_singleton

@[to_additive]
theorem smul_ball_one : x • ball 1 δ = ball x δ :=
  by
  ext
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div]
#align smul_ball_one smul_ball_one
#align vadd_ball_zero vadd_ball_zero

@[simp, to_additive]
theorem singleton_mul_closedBall : {x} * closedBall y δ = closedBall (x * y) δ := by
  simp only [mul_comm y x, preimage_mul_closedBall, image_mul_left, singleton_mul, div_inv_eq_mul]
#align singleton_mul_closed_ball singleton_mul_closedBall
#align singleton_add_closed_ball singleton_add_closedBall

@[simp, to_additive]
theorem singleton_div_closedBall : {x} / closedBall y δ = closedBall (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_closedBall, singleton_mul_closedBall]
#align singleton_div_closed_ball singleton_div_closedBall
#align singleton_sub_closed_ball singleton_sub_closedBall

@[simp, to_additive]
theorem closedBall_mul_singleton : closedBall x δ * {y} = closedBall (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]
#align closed_ball_mul_singleton closedBall_mul_singleton
#align closed_ball_add_singleton closedBall_add_singleton

@[simp, to_additive]
theorem closedBall_div_singleton : closedBall x δ / {y} = closedBall (x / y) δ := by
  simp [div_eq_mul_inv]
#align closed_ball_div_singleton closedBall_div_singleton
#align closed_ball_sub_singleton closedBall_sub_singleton

@[to_additive]
theorem singleton_mul_closedBall_one : {x} * closedBall 1 δ = closedBall x δ := by simp
#align singleton_mul_closed_ball_one singleton_mul_closedBall_one
#align singleton_add_closed_ball_zero singleton_add_closedBall_zero

@[to_additive]
theorem singleton_div_closedBall_one : {x} / closedBall 1 δ = closedBall x δ := by simp
#align singleton_div_closed_ball_one singleton_div_closedBall_one
#align singleton_sub_closed_ball_zero singleton_sub_closedBall_zero

@[to_additive]
theorem closedBall_one_mul_singleton : closedBall 1 δ * {x} = closedBall x δ := by simp
#align closed_ball_one_mul_singleton closedBall_one_mul_singleton
#align closed_ball_zero_add_singleton closedBall_zero_add_singleton

@[to_additive]
theorem closedBall_one_div_singleton : closedBall 1 δ / {x} = closedBall x⁻¹ δ := by simp
#align closed_ball_one_div_singleton closedBall_one_div_singleton
#align closed_ball_zero_sub_singleton closedBall_zero_sub_singleton

-- This is the `to_additive` version of the below, but it will later follow as a special case of
-- `vadd_closed_ball` for `normed_add_torsor`s, so we give it higher simp priority.
-- (There is no `normed_mul_torsor`, hence the asymmetry between additive and multiplicative
-- versions.)
@[simp]
theorem vadd_closedBall_zero {E : Type _} [SeminormedAddCommGroup E] (δ : ℝ) (x : E) :
    x +ᵥ Metric.closedBall 0 δ = Metric.closedBall x δ :=
  by
  ext
  simp [mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_sub, dist_eq_norm_sub]
#align vadd_closed_ball_zero vadd_closedBall_zero

@[simp]
theorem smul_closedBall_one : x • closedBall 1 δ = closedBall x δ :=
  by
  ext
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div]
#align smul_closed_ball_one smul_closedBall_one

attribute [to_additive] smul_closedBall_one

@[to_additive]
theorem mul_ball_one : s * ball 1 δ = thickening δ s :=
  by
  rw [thickening_eq_bUnion_ball]
  convert Union₂_mul (fun x (_ : x ∈ s) => {x}) (ball (1 : E) δ)
  exact s.bUnion_of_singleton.symm
  ext (x y)
  simp_rw [singleton_mul_ball, mul_one]
#align mul_ball_one mul_ball_one
#align add_ball_zero add_ball_zero

@[to_additive]
theorem div_ball_one : s / ball 1 δ = thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]
#align div_ball_one div_ball_one
#align sub_ball_zero sub_ball_zero

@[to_additive]
theorem ball_mul_one : ball 1 δ * s = thickening δ s := by rw [mul_comm, mul_ball_one]
#align ball_mul_one ball_mul_one
#align ball_add_zero ball_add_zero

@[to_additive]
theorem ball_div_one : ball 1 δ / s = thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]
#align ball_div_one ball_div_one
#align ball_sub_zero ball_sub_zero

@[simp, to_additive]
theorem mul_ball : s * ball x δ = x • thickening δ s := by
  rw [← smul_ball_one, mul_smul_comm, mul_ball_one]
#align mul_ball mul_ball
#align add_ball add_ball

@[simp, to_additive]
theorem div_ball : s / ball x δ = x⁻¹ • thickening δ s := by simp [div_eq_mul_inv]
#align div_ball div_ball
#align sub_ball sub_ball

@[simp, to_additive]
theorem ball_mul : ball x δ * s = x • thickening δ s := by rw [mul_comm, mul_ball]
#align ball_mul ball_mul
#align ball_add ball_add

@[simp, to_additive]
theorem ball_div : ball x δ / s = x • thickening δ s⁻¹ := by simp [div_eq_mul_inv]
#align ball_div ball_div
#align ball_sub ball_sub

variable {ε δ s t x y}

@[to_additive]
theorem IsCompact.mul_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s * closedBall 1 δ = cthickening δ s :=
  by
  rw [hs.cthickening_eq_bUnion_closed_ball hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_Union, mem_closed_ball, exists_and_left,
    mem_closedBall_one_iff, ← eq_div_iff_mul_eq'', exists_eq_right]
#align is_compact.mul_closed_ball_one IsCompact.mul_closedBall_one
#align is_compact.add_closed_ball_zero IsCompact.add_closedBall_zero

@[to_additive]
theorem IsCompact.div_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s / closedBall 1 δ = cthickening δ s := by simp [div_eq_mul_inv, hs.mul_closed_ball_one hδ]
#align is_compact.div_closed_ball_one IsCompact.div_closedBall_one
#align is_compact.sub_closed_ball_zero IsCompact.sub_closedBall_zero

@[to_additive]
theorem IsCompact.closedBall_one_mul (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ * s = cthickening δ s := by rw [mul_comm, hs.mul_closed_ball_one hδ]
#align is_compact.closed_ball_one_mul IsCompact.closedBall_one_mul
#align is_compact.closed_ball_zero_add IsCompact.closedBall_zero_add

@[to_additive]
theorem IsCompact.closedBall_one_div (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ / s = cthickening δ s⁻¹ := by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closed_ball_one hδ]
#align is_compact.closed_ball_one_div IsCompact.closedBall_one_div
#align is_compact.closed_ball_zero_sub IsCompact.closedBall_zero_sub

@[to_additive]
theorem IsCompact.mul_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s * closedBall x δ = x • cthickening δ s := by
  rw [← smul_closedBall_one, mul_smul_comm, hs.mul_closed_ball_one hδ]
#align is_compact.mul_closed_ball IsCompact.mul_closedBall
#align is_compact.add_closed_ball IsCompact.add_closedBall

@[to_additive]
theorem IsCompact.div_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s / closedBall x δ = x⁻¹ • cthickening δ s := by
  simp [div_eq_mul_inv, mul_comm, hs.mul_closed_ball hδ]
#align is_compact.div_closed_ball IsCompact.div_closedBall
#align is_compact.sub_closed_ball IsCompact.sub_closedBall

@[to_additive]
theorem IsCompact.closedBall_mul (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by rw [mul_comm, hs.mul_closed_ball hδ]
#align is_compact.closed_ball_mul IsCompact.closedBall_mul
#align is_compact.closed_ball_add IsCompact.closedBall_add

@[to_additive]
theorem IsCompact.closedBall_div (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by
  simp [div_eq_mul_inv, mul_comm, hs.closed_ball_mul hδ]
#align is_compact.closed_ball_div IsCompact.closedBall_div
#align is_compact.closed_ball_sub IsCompact.closedBall_sub

end SeminormedCommGroup

