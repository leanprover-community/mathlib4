/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Michał Świętek
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.LocallyConvex.AbsConvex
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure

/-!
# Polar sets in the strong dual of a normed space

In this file we study polar sets in the strong dual `StrongDual` of a normed space.

## Main definitions

* `polar 𝕜 s` is the subset of `StrongDual 𝕜 E` consisting of those functionals `x'` for which
  `‖x' z‖ ≤ 1` for every `z ∈ s`.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

strong dual, polar
-/

@[expose] public section

noncomputable section

open Topology Bornology

namespace NormedSpace

section PolarSets

open Metric Set StrongDual

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem isClosed_polar (s : Set E) : IsClosed (StrongDual.polar 𝕜 s) := by
  dsimp only [StrongDual.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine isClosed_biInter fun z _ => ?_
  exact isClosed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.norm

@[simp]
theorem polar_closure (s : Set E) : StrongDual.polar 𝕜 (closure s) = StrongDual.polar 𝕜 s :=
  ((topDualPairing 𝕜 E).flip.polar_antitone subset_closure).antisymm <|
    (topDualPairing 𝕜 E).flip.polar_gc.l_le <|
      closure_minimal ((topDualPairing 𝕜 E).flip.polar_gc.le_u_l s) <| by
        simpa [LinearMap.flip_flip] using
          (isClosed_polar _ _).preimage (ContinuousLinearMap.apply 𝕜 𝕜 (E := E)).continuous

variable {𝕜}

/-- If `x'` is a `StrongDual 𝕜 E` element such that the norms `‖x' z‖` are bounded for `z ∈ s`, then
a small scalar multiple of `x'` is in `polar 𝕜 s`. -/
theorem smul_mem_polar {s : Set E} {x' : StrongDual 𝕜 E} {c : 𝕜} (hc : ∀ z, z ∈ s → ‖x' z‖ ≤ ‖c‖) :
    c⁻¹ • x' ∈ StrongDual.polar 𝕜 s := by
  by_cases c_zero : c = 0
  · simp only [c_zero, inv_zero, zero_smul]
    exact (topDualPairing 𝕜 E).flip.zero_mem_polar _
  have eq : ∀ z, ‖c⁻¹ • x' z‖ = ‖c⁻¹‖ * ‖x' z‖ := fun z => norm_smul c⁻¹ _
  have le : ∀ z, z ∈ s → ‖c⁻¹ • x' z‖ ≤ ‖c⁻¹‖ * ‖c‖ := by
    intro z hzs
    rw [eq z]
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : ‖c⁻¹‖ * ‖c‖ = 1 := by
    simp only [c_zero, norm_eq_zero, Ne, not_false_iff, inv_mul_cancel₀, norm_inv]
  rwa [cancel] at le

theorem polar_ball_subset_closedBall_div {c : 𝕜} (hc : 1 < ‖c‖) {r : ℝ} (hr : 0 < r) :
    StrongDual.polar 𝕜 (ball (0 : E) r) ⊆ closedBall (0 : StrongDual 𝕜 E) (‖c‖ / r) := by
  intro x' hx'
  rw [StrongDual.mem_polar_iff] at hx'
  simp only [mem_closedBall_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ‖c‖ / r := div_pos (zero_lt_one.trans hc) hr
  refine ContinuousLinearMap.opNorm_le_of_shell hr hcr.le hc fun x h₁ h₂ => ?_
  calc
    ‖x' x‖ ≤ 1 := hx' _ h₂
    _ ≤ ‖c‖ / r * ‖x‖ := (inv_le_iff_one_le_mul₀' hcr).1 (by rwa [inv_div])

variable (𝕜)

theorem closedBall_inv_subset_polar_closedBall {r : ℝ} :
    closedBall (0 : StrongDual 𝕜 E) r⁻¹ ⊆ StrongDual.polar 𝕜 (closedBall (0 : E) r) :=
  fun x' hx' x hx =>
  calc
    ‖x' x‖ ≤ ‖x'‖ * ‖x‖ := x'.le_opNorm x
    _ ≤ r⁻¹ * r :=
      (mul_le_mul (mem_closedBall_zero_iff.1 hx') (mem_closedBall_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx'))
    _ = r / r := inv_mul_eq_div _ _
    _ ≤ 1 := div_self_le_one r

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with inverse
radius. -/
theorem polar_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}
    (hr : 0 < r) :
    StrongDual.polar 𝕜 (closedBall (0 : E) r) = closedBall (0 : StrongDual 𝕜 E) r⁻¹ := by
  refine Subset.antisymm ?_ (closedBall_inv_subset_polar_closedBall 𝕜)
  intro x' h
  simp only [mem_closedBall_zero_iff]
  refine ContinuousLinearMap.opNorm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z _ => ?_
  simpa only [one_div] using LinearMap.bound_of_ball_bound' hr 1 x'.toLinearMap h z

theorem polar_ball {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}
    (hr : 0 < r) : StrongDual.polar 𝕜 (ball (0 : E) r) = closedBall (0 : StrongDual 𝕜 E) r⁻¹ := by
  apply le_antisymm
  · intro x hx
    rw [mem_closedBall_zero_iff]
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    rw [← mem_closedBall_zero_iff, ← (mul_div_cancel_left₀ a (Ne.symm (ne_of_lt hr)))]
    rw [← RCLike.norm_of_nonneg (K := 𝕜) (le_trans zero_le_one
      (le_of_lt ((inv_lt_iff_one_lt_mul₀' hr).mp ha)))]
    apply polar_ball_subset_closedBall_div _ hr hx
    rw [RCLike.norm_of_nonneg (K := 𝕜) (le_trans zero_le_one
      (le_of_lt ((inv_lt_iff_one_lt_mul₀' hr).mp ha)))]
    exact (inv_lt_iff_one_lt_mul₀' hr).mp ha
  · rw [← polar_closedBall hr]
    exact LinearMap.polar_antitone _ ball_subset_closedBall

/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms of all elements of
the polar `polar 𝕜 s` are bounded by a constant. -/
theorem isBounded_polar_of_mem_nhds_zero {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsBounded (StrongDual.polar 𝕜 s) := by
  obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ‖a‖ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : ∃ r : ℝ, 0 < r ∧ ball 0 r ⊆ s := Metric.mem_nhds_iff.1 s_nhds
  exact isBounded_closedBall.subset
    (((topDualPairing 𝕜 E).flip.polar_antitone r_ball).trans <|
      polar_ball_subset_closedBall_div ha r_pos)

theorem sInter_polar_eq_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {r : ℝ} (hr : 0 < r) :
    ⋂₀ (StrongDual.polar 𝕜 '' { F | F.Finite ∧ F ⊆ closedBall (0 : E) r⁻¹ }) = closedBall 0 r := by
  conv_rhs => rw [← inv_inv r]
  rw [← polar_closedBall (inv_pos_of_pos hr), StrongDual.polar,
    (topDualPairing 𝕜 E).flip.sInter_polar_finite_subset_eq_polar (closedBall (0 : E) r⁻¹)]

end PolarSets

end NormedSpace

namespace LinearMap

section NormedField

variable {𝕜 E F : Type*}
variable [RCLike 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

open ComplexOrder in
theorem polar_AbsConvex : AbsConvex 𝕜 (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact AbsConvex.iInter₂ fun i hi =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F →ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_RCLike_iff_convex_real.mpr (convex_closedBall 0 1)).linear_preimage _⟩

end NormedField

end LinearMap

section Deprecated

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

@[deprecated SeparatingDual.eq_zero_of_forall_dual_eq_zero (since := "2026-03-18")]
theorem NormedSpace.eq_zero_of_forall_dual_eq_zero {x : E}
    (h : ∀ f : StrongDual 𝕜 E, f x = 0) : x = 0 :=
  SeparatingDual.eq_zero_of_forall_dual_eq_zero h

@[deprecated SeparatingDual.eq_zero_iff_forall_dual_eq_zero (since := "2026-03-18")]
theorem NormedSpace.eq_zero_iff_forall_dual_eq_zero (x : E) :
    x = 0 ↔ ∀ g : StrongDual 𝕜 E, g x = 0 :=
  SeparatingDual.eq_zero_iff_forall_dual_eq_zero x

@[deprecated SeparatingDual.eq_iff_forall_dual_eq (since := "2026-03-18")]
theorem NormedSpace.eq_iff_forall_dual_eq {x y : E} :
    x = y ↔ ∀ g : StrongDual 𝕜 E, g x = g y :=
  SeparatingDual.eq_iff_forall_dual_eq

end Deprecated
