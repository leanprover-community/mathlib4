/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.Instances.AddCircle.Real  -- shake: keep (used in type annotation)

/-!
# The additive circle as a normed group

We define the normed group structure on `AddCircle p`, for `p : ℝ`. For example if `p = 1` then:
`‖(x : AddCircle 1)‖ = |x - round x|` for any `x : ℝ` (see `UnitAddCircle.norm_eq`).

## Main definitions:

* `AddCircle.norm_eq`: a characterisation of the norm on `AddCircle p`

## TODO

* The fact `InnerProductGeometry.angle (Real.cos θ) (Real.sin θ) = ‖(θ : Real.Angle)‖`

-/

public section


noncomputable section

open Metric QuotientAddGroup Set

open Int hiding mem_zmultiples_iff

open AddSubgroup

namespace AddCircle

variable (p : ℝ)

instance : NormedAddCommGroup (AddCircle p) := QuotientAddGroup.instNormedAddCommGroup _

@[simp]
theorem norm_coe_mul (x : ℝ) (t : ℝ) :
    ‖(↑(t * x) : AddCircle (t * p))‖ = |t| * ‖(x : AddCircle p)‖ := by
  obtain rfl | ht := eq_or_ne t 0
  · simp
  simp only [norm_eq_infDist, ← Real.norm_eq_abs, ← infDist_smul₀, smul_zero]
  congr 1 with m
  simp_rw [zmultiples, eq_iff_sub_mem, zsmul_eq_mul, mul_left_comm, ← smul_eq_mul, Set.range_smul]
  simp [mem_smul_set_iff_inv_smul_mem₀ ht, mul_sub, ht]

theorem norm_neg_period (x : ℝ) : ‖(x : AddCircle (-p))‖ = ‖(x : AddCircle p)‖ := by
  suffices ‖(↑(-1 * x) : AddCircle (-1 * p))‖ = ‖(x : AddCircle p)‖ by
    rw [← this, neg_one_mul]
    simp
  simp only [norm_coe_mul, abs_neg, abs_one, one_mul]

@[simp]
theorem norm_eq_of_zero {x : ℝ} : ‖(x : AddCircle (0 : ℝ))‖ = |x| := by
  suffices { y : ℝ | (y : AddCircle (0 : ℝ)) = (x : AddCircle (0 : ℝ)) } = {x} by
    simp [norm_eq_infDist, this]
  ext y
  simp [eq_iff_sub_mem, sub_eq_zero]

theorem norm_eq {x : ℝ} : ‖(x : AddCircle p)‖ = |x - round (p⁻¹ * x) * p| := by
  suffices ∀ x : ℝ, ‖(x : AddCircle (1 : ℝ))‖ = |x - round x| by
    rcases eq_or_ne p 0 with (rfl | hp)
    · simp
    have hx := norm_coe_mul p x p⁻¹
    rw [abs_inv, eq_inv_mul_iff_mul_eq₀ ((not_congr abs_eq_zero).mpr hp)] at hx
    rw [← hx, inv_mul_cancel₀ hp, this, ← abs_mul, mul_sub, mul_inv_cancel_left₀ hp, mul_comm p]
  clear! x p
  intro x
  simp only [le_antisymm_iff, le_norm_iff, Real.norm_eq_abs]
  refine ⟨le_of_forall_le fun r hr ↦ ?_, ?_⟩
  · rw [abs_sub_round_eq_min, le_inf_iff]
    rw [le_norm_iff] at hr
    constructor
    · simpa [abs_of_nonneg] using hr (fract x)
    · simpa [abs_sub_comm (fract x)] using hr (fract x - 1) (by simp)
  · simpa [zmultiples, QuotientAddGroup.eq, zsmul_eq_mul, mul_one, mem_mk, mem_range, and_imp,
      forall_exists_index, eq_neg_add_iff_add_eq, ← eq_sub_iff_add_eq, forall_comm (α := ℕ)]
      using round_le _

theorem norm_eq' (hp : 0 < p) {x : ℝ} : ‖(x : AddCircle p)‖ = p * |p⁻¹ * x - round (p⁻¹ * x)| := by
  conv_rhs =>
    congr
    rw [← abs_eq_self.mpr hp.le]
  rw [← abs_mul, mul_sub, mul_inv_cancel_left₀ hp.ne.symm, norm_eq, mul_comm p]

theorem norm_le_half_period {x : AddCircle p} (hp : p ≠ 0) : ‖x‖ ≤ |p| / 2 := by
  obtain ⟨x⟩ := x
  change ‖(x : AddCircle p)‖ ≤ |p| / 2
  rw [norm_eq, ← mul_le_mul_iff_right₀ (abs_pos.mpr (inv_ne_zero hp)), ← abs_mul, mul_sub,
    mul_left_comm, ← mul_div_assoc, ← abs_mul, inv_mul_cancel₀ hp, mul_one, abs_one]
  exact abs_sub_round (p⁻¹ * x)

@[simp]
theorem norm_half_period_eq : ‖(↑(p / 2) : AddCircle p)‖ = |p| / 2 := by
  rcases eq_or_ne p 0 with (rfl | hp); · simp
  rw [norm_eq, ← mul_div_assoc, inv_mul_cancel₀ hp, one_div, round_two_inv, Int.cast_one,
    one_mul, (by linarith : p / 2 - p = -(p / 2)), abs_neg, abs_div, abs_two]

theorem norm_coe_eq_abs_iff {x : ℝ} (hp : p ≠ 0) : ‖(x : AddCircle p)‖ = |x| ↔ |x| ≤ |p| / 2 := by
  refine ⟨fun hx => hx ▸ norm_le_half_period p hp, fun hx => ?_⟩
  suffices ∀ p : ℝ, 0 < p → |x| ≤ p / 2 → ‖(x : AddCircle p)‖ = |x| by
    rcases hp.symm.lt_or_gt with (hp | hp)
    · rw [abs_eq_self.mpr hp.le] at hx
      exact this p hp hx
    · rw [← norm_neg_period]
      rw [abs_eq_neg_self.mpr hp.le] at hx
      exact this (-p) (neg_pos.mpr hp) hx
  clear hx
  intro p hp hx
  rcases eq_or_ne x (p / (2 : ℝ)) with (rfl | hx')
  · simp [abs_div]
  suffices round (p⁻¹ * x) = 0 by simp [norm_eq, this]
  rw [round_eq_zero_iff]
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  replace hx₂ := Ne.lt_of_le hx' hx₂
  constructor
  · rwa [le_inv_mul_iff₀ hp, mul_neg, ← mul_div_assoc, mul_one]
  · rwa [inv_mul_lt_iff₀ hp, ← mul_div_assoc, mul_one]

theorem norm_nsmul_eq_mul {x : AddCircle p} {n : ℕ}
    (hx : n * ‖x‖ ≤ |p| / 2) : ‖n • x‖ = n * ‖x‖ := by
  obtain ⟨t, rfl⟩ := mk_surjective x
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [← coe_nsmul, nsmul_eq_mul, norm_eq_of_zero, abs_mul, Nat.abs_cast]
  let s := t - round (p⁻¹ * t) * p
  have hs : (s : AddCircle p) = t := by simp [s, coe_period]
  have hs' : ‖(s : AddCircle p)‖ = |s| := by rw [hs, norm_eq]
  rw [← hs, hs'] at hx ⊢
  rw [← coe_nsmul, nsmul_eq_mul, (norm_coe_eq_abs_iff p hp).mpr
    (by rwa [abs_mul, Nat.abs_cast]), abs_mul, Nat.abs_cast]

/-- If `x` lies in the ball of radius `|p| / 2 / n` and `n • x` lies in the ball of radius `s`,
then `x` lies in the ball of radius `s / n`. -/
theorem mem_ball_div {x : AddCircle p} {s : ℝ} {n : ℕ}
    (h1 : x ∈ ball 0 (|p| / 2 / n)) (h2 : n • x ∈ ball 0 s) : x ∈ ball 0 (s / n) := by
  have hn0 : n ≠ 0 := by
    contrapose h1
    simp [h1]
  rw [mem_ball_zero_iff, lt_div_iff₀' (by positivity)] at h1 ⊢
  rwa [mem_ball_zero_iff, norm_nsmul_eq_mul p h1.le] at h2

/-- The balls of radius `|p| / 2 / 2 ^ (n + 1)` around `0` form a basis of neighbourhoods of `0`. -/
theorem hasBasis_ball_div_two_pow (hp : p ≠ 0) :
    (nhds (0 : AddCircle p)).HasBasis (fun _ ↦ True) (fun n ↦ ball 0 (|p| / 2 / 2 ^ (n + 1))) :=
  nhds_basis_uniformity <| mk_uniformity_basis_of_tendsto (f := fun n ↦ |p| / 2 / 2 ^ (n + 1))
    (l := Filter.atTop) (fun _ _ ↦ by positivity) (by simp) <| tendsto_const_nhds.div_atTop <|
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (Filter.tendsto_add_atTop_nat 1)

/-- If all positive multiples of `x : AddCircle p` lie in the ball of radius `|p| / 2 / 2` around
`0`, then `x = 0`. -/
theorem eq_zero_of_forall_nsmul_mem_ball {x : AddCircle p}
    (hx : ∀ n > 0, n • x ∈ ball 0 (|p| / 2 / 2)) : x = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simpa using hx 1
  have hx1 : x ∈ ball 0 (|p| / 2 / 2) := by simpa using hx 1
  have h (n : ℕ) : x ∈ ball 0 (|p| / 2 / 2 ^ (n + 1)) := by
    induction n with
    | zero => simpa using hx1
    | succ n ih =>
        simpa [div_div, mul_assoc, ← pow_succ'] using
          mem_ball_div p (by simpa using ih) (hx (2 ^ (n + 1)) (by positivity))
  rw [← Set.mem_singleton_iff, ← ker_nhds, (hasBasis_ball_div_two_pow p hp).ker]
  exact Set.mem_iInter₂.mpr fun n _ ↦ h n

open Metric

theorem closedBall_eq_univ_of_half_period_le (hp : p ≠ 0) (x : AddCircle p) {ε : ℝ}
    (hε : |p| / 2 ≤ ε) : closedBall x ε = univ :=
  eq_univ_iff_forall.mpr fun x => by
    simpa only [mem_closedBall, dist_eq_norm] using (norm_le_half_period p hp).trans hε

@[simp]
theorem coe_real_preimage_closedBall_period_zero (x ε : ℝ) :
    (↑) ⁻¹' closedBall (x : AddCircle (0 : ℝ)) ε = closedBall x ε := by
  ext y
  simp [dist_eq_norm, ← QuotientAddGroup.mk_sub]

theorem coe_real_preimage_closedBall_eq_iUnion (x ε : ℝ) :
    (↑) ⁻¹' closedBall (x : AddCircle p) ε = ⋃ z : ℤ, closedBall (x + z • p) ε := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp [iUnion_const]
  ext y
  simp only [dist_eq_norm, mem_preimage, mem_closedBall, zsmul_eq_mul, mem_iUnion, Real.norm_eq_abs,
    ← QuotientAddGroup.mk_sub, norm_eq, ← sub_sub]
  refine ⟨fun h => ⟨round (p⁻¹ * (y - x)), h⟩, ?_⟩
  rintro ⟨n, hn⟩
  rw [← mul_le_mul_iff_right₀ (abs_pos.mpr <| inv_ne_zero hp), ← abs_mul, mul_sub, mul_comm _ p,
    inv_mul_cancel_left₀ hp] at hn ⊢
  exact (round_le (p⁻¹ * (y - x)) n).trans hn

theorem coe_real_preimage_closedBall_inter_eq {x ε : ℝ} (s : Set ℝ)
    (hs : s ⊆ closedBall x (|p| / 2)) :
    (↑) ⁻¹' closedBall (x : AddCircle p) ε ∩ s = if ε < |p| / 2 then closedBall x ε ∩ s else s := by
  rcases le_or_gt (|p| / 2) ε with hε | hε
  · rcases eq_or_ne p 0 with (rfl | hp)
    · simp only [abs_zero, zero_div] at hε
      simp only [not_lt.mpr hε, coe_real_preimage_closedBall_period_zero, abs_zero, zero_div,
        ite_false, inter_eq_right]
      exact hs.trans (closedBall_subset_closedBall <| by simp [hε])
    simp [closedBall_eq_univ_of_half_period_le p hp (↑x) hε, not_lt.mpr hε]
  · suffices ∀ z : ℤ, closedBall (x + z • p) ε ∩ s = if z = 0 then closedBall x ε ∩ s else ∅ by
      simp [-zsmul_eq_mul, coe_real_preimage_closedBall_eq_iUnion,
        iUnion_inter, iUnion_ite, this, hε]
    intro z
    simp only [Real.closedBall_eq_Icc] at hs ⊢
    rcases eq_or_ne z 0 with (rfl | hz)
    · simp
    simp only [hz, zsmul_eq_mul, ite_false, eq_empty_iff_forall_notMem]
    rintro y ⟨⟨hy₁, hy₂⟩, hy₀⟩
    obtain ⟨hy₃, hy₄⟩ := hs hy₀
    rcases lt_trichotomy 0 p with (hp | (rfl : 0 = p) | hp)
    · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz with hz' | hz'
      · have : ↑z * p ≤ -p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
      · have : p ≤ ↑z * p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
    · simp only [mul_zero, add_zero, abs_zero, zero_div] at hy₁ hy₂ hε
      linarith
    · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz with hz' | hz'
      · have : -p ≤ ↑z * p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]
      · have : ↑z * p ≤ p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]

section FiniteOrderPoints

variable {p} [hp : Fact (0 < p)]

theorem norm_div_natCast {m n : ℕ} :
    ‖(↑(↑m / ↑n * p) : AddCircle p)‖ = p * (↑(min (m % n) (n - m % n)) / n) := by
  have : p⁻¹ * (↑m / ↑n * p) = ↑m / ↑n := by rw [mul_comm _ p, inv_mul_cancel_left₀ hp.out.ne.symm]
  rw [norm_eq' p hp.out, this, abs_sub_round_div_natCast_eq]

theorem exists_norm_eq_of_isOfFinAddOrder {u : AddCircle p} (hu : IsOfFinAddOrder u) :
    ∃ k : ℕ, ‖u‖ = p * (k / addOrderOf u) := by
  let n := addOrderOf u
  change ∃ k : ℕ, ‖u‖ = p * (k / n)
  obtain ⟨m, -, -, hm⟩ := exists_gcd_eq_one_of_isOfFinAddOrder hu
  refine ⟨min (m % n) (n - m % n), ?_⟩
  rw [← hm, norm_div_natCast]

theorem le_add_order_smul_norm_of_isOfFinAddOrder {u : AddCircle p} (hu : IsOfFinAddOrder u)
    (hu' : u ≠ 0) : p ≤ addOrderOf u • ‖u‖ := by
  obtain ⟨n, hn⟩ := exists_norm_eq_of_isOfFinAddOrder hu
  replace hu : (addOrderOf u : ℝ) ≠ 0 := by
    norm_cast
    exact (addOrderOf_pos_iff.mpr hu).ne'
  conv_lhs => rw [← mul_one p]
  rw [hn, nsmul_eq_mul, ← mul_assoc, mul_comm _ p, mul_assoc, mul_div_cancel₀ _ hu,
    mul_le_mul_iff_right₀ hp.out, Nat.one_le_cast, Nat.one_le_iff_ne_zero]
  contrapose hu'
  simpa only [hu', Nat.cast_zero, zero_div, mul_zero, norm_eq_zero] using hn

end FiniteOrderPoints

end AddCircle

namespace UnitAddCircle

theorem norm_eq {x : ℝ} : ‖(x : UnitAddCircle)‖ = |x - round x| := by simp [AddCircle.norm_eq]

end UnitAddCircle
