/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Instances.AddCircle

#align_import analysis.normed.group.add_circle from "leanprover-community/mathlib"@"084f76e20c88eae536222583331abd9468b08e1c"

/-!
# The additive circle as a normed group

We define the normed group structure on `AddCircle p`, for `p : ℝ`. For example if `p = 1` then:
`‖(x : AddCircle 1)‖ = |x - round x|` for any `x : ℝ` (see `UnitAddCircle.norm_eq`).

## Main definitions:

 * `AddCircle.norm_eq`: a characterisation of the norm on `AddCircle p`

## TODO

 * The fact `InnerProductGeometry.angle (Real.cos θ) (Real.sin θ) = ‖(θ : Real.Angle)‖`

-/


noncomputable section

open Set

open Int hiding mem_zmultiples_iff

open AddSubgroup

namespace AddCircle

variable (p : ℝ)

instance : NormedAddCommGroup (AddCircle p) :=
  AddSubgroup.normedAddCommGroupQuotient _

@[simp]
theorem norm_coe_mul (x : ℝ) (t : ℝ) :
    ‖(↑(t * x) : AddCircle (t * p))‖ = |t| * ‖(x : AddCircle p)‖ := by
  have aux : ∀ {a b c : ℝ}, a ∈ zmultiples b → c * a ∈ zmultiples (c * b) := fun {a b c} h => by
    simp only [mem_zmultiples_iff] at h ⊢
    obtain ⟨n, rfl⟩ := h
    exact ⟨n, (mul_smul_comm n c b).symm⟩
  rcases eq_or_ne t 0 with (rfl | ht); · simp
  have ht' : |t| ≠ 0 := (not_congr abs_eq_zero).mpr ht
  simp only [quotient_norm_eq, Real.norm_eq_abs]
  conv_rhs => rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg (abs_nonneg t)]
  simp only [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
  congr 1
  ext z
  rw [mem_smul_set_iff_inv_smul_mem₀ ht']
  show
    (∃ y, y - t * x ∈ zmultiples (t * p) ∧ |y| = z) ↔ ∃ w, w - x ∈ zmultiples p ∧ |w| = |t|⁻¹ * z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨t⁻¹ * y, ?_, by rw [abs_mul, abs_inv]⟩
    rw [← inv_mul_cancel_left₀ ht x, ← inv_mul_cancel_left₀ ht p, ← mul_sub]
    exact aux hy
  · rintro ⟨w, hw, hw'⟩
    refine ⟨t * w, ?_, by rw [← (eq_inv_mul_iff_mul_eq₀ ht').mp hw', abs_mul]⟩
    rw [← mul_sub]
    exact aux hw
#align add_circle.norm_coe_mul AddCircle.norm_coe_mul

theorem norm_neg_period (x : ℝ) : ‖(x : AddCircle (-p))‖ = ‖(x : AddCircle p)‖ := by
  suffices ‖(↑(-1 * x) : AddCircle (-1 * p))‖ = ‖(x : AddCircle p)‖ by
    rw [← this, neg_one_mul]
    simp
  simp only [norm_coe_mul, abs_neg, abs_one, one_mul]
#align add_circle.norm_neg_period AddCircle.norm_neg_period

@[simp]
theorem norm_eq_of_zero {x : ℝ} : ‖(x : AddCircle (0 : ℝ))‖ = |x| := by
  suffices { y : ℝ | (y : AddCircle (0 : ℝ)) = (x : AddCircle (0 : ℝ)) } = {x} by
    rw [quotient_norm_eq, this, image_singleton, Real.norm_eq_abs, csInf_singleton]
  ext y
  simp [QuotientAddGroup.eq_iff_sub_mem, mem_zmultiples_iff, sub_eq_zero]
#align add_circle.norm_eq_of_zero AddCircle.norm_eq_of_zero

theorem norm_eq {x : ℝ} : ‖(x : AddCircle p)‖ = |x - round (p⁻¹ * x) * p| := by
  suffices ∀ x : ℝ, ‖(x : AddCircle (1 : ℝ))‖ = |x - round x| by
    rcases eq_or_ne p 0 with (rfl | hp)
    · simp
    have hx := norm_coe_mul p x p⁻¹
    rw [abs_inv, eq_inv_mul_iff_mul_eq₀ ((not_congr abs_eq_zero).mpr hp)] at hx
    rw [← hx, inv_mul_cancel hp, this, ← abs_mul, mul_sub, mul_inv_cancel_left₀ hp, mul_comm p]
  clear! x p
  intros x
  rw [quotient_norm_eq, abs_sub_round_eq_min]
  have h₁ : BddBelow (abs '' { m : ℝ | (m : AddCircle (1 : ℝ)) = x }) :=
    ⟨0, by simp [mem_lowerBounds]⟩
  have h₂ : (abs '' { m : ℝ | (m : AddCircle (1 : ℝ)) = x }).Nonempty := ⟨|x|, ⟨x, rfl, rfl⟩⟩
  apply le_antisymm
  · simp_rw [Real.norm_eq_abs, csInf_le_iff h₁ h₂, le_min_iff]
    intro b h
    refine
      ⟨mem_lowerBounds.1 h _ ⟨fract x, ?_, abs_fract⟩,
        mem_lowerBounds.1 h _ ⟨fract x - 1, ?_, by rw [abs_sub_comm, abs_one_sub_fract]⟩⟩
    · simp only [mem_setOf, fract, sub_eq_self, QuotientAddGroup.mk_sub,
        QuotientAddGroup.eq_zero_iff, intCast_mem_zmultiples_one]
    · simp only [mem_setOf, fract, sub_eq_self, QuotientAddGroup.mk_sub,
        QuotientAddGroup.eq_zero_iff, intCast_mem_zmultiples_one, sub_sub,
        (by norm_cast : (⌊x⌋ : ℝ) + 1 = (↑(⌊x⌋ + 1) : ℝ))]
  · simp only [QuotientAddGroup.mk'_apply, Real.norm_eq_abs, le_csInf_iff h₁ h₂]
    rintro b' ⟨b, hb, rfl⟩
    simp only [mem_setOf, QuotientAddGroup.eq_iff_sub_mem, mem_zmultiples_iff,
      smul_one_eq_cast] at hb
    obtain ⟨z, hz⟩ := hb
    rw [(by rw [hz]; abel : x = b - z), fract_sub_int, ← abs_sub_round_eq_min]
    convert round_le b 0
    simp
#align add_circle.norm_eq AddCircle.norm_eq

theorem norm_eq' (hp : 0 < p) {x : ℝ} : ‖(x : AddCircle p)‖ = p * |p⁻¹ * x - round (p⁻¹ * x)| := by
  conv_rhs =>
    congr
    rw [← abs_eq_self.mpr hp.le]
  rw [← abs_mul, mul_sub, mul_inv_cancel_left₀ hp.ne.symm, norm_eq, mul_comm p]
#align add_circle.norm_eq' AddCircle.norm_eq'

theorem norm_le_half_period {x : AddCircle p} (hp : p ≠ 0) : ‖x‖ ≤ |p| / 2 := by
  obtain ⟨x⟩ := x
  change ‖(x : AddCircle p)‖ ≤ |p| / 2
  rw [norm_eq, ← mul_le_mul_left (abs_pos.mpr (inv_ne_zero hp)), ← abs_mul, mul_sub, mul_left_comm,
    ← mul_div_assoc, ← abs_mul, inv_mul_cancel hp, mul_one, abs_one]
  exact abs_sub_round (p⁻¹ * x)
#align add_circle.norm_le_half_period AddCircle.norm_le_half_period

@[simp]
theorem norm_half_period_eq : ‖(↑(p / 2) : AddCircle p)‖ = |p| / 2 := by
  rcases eq_or_ne p 0 with (rfl | hp); · simp
  rw [norm_eq, ← mul_div_assoc, inv_mul_cancel hp, one_div, round_two_inv, Int.cast_one,
    one_mul, (by linarith : p / 2 - p = -(p / 2)), abs_neg, abs_div, abs_two]
#align add_circle.norm_half_period_eq AddCircle.norm_half_period_eq

theorem norm_coe_eq_abs_iff {x : ℝ} (hp : p ≠ 0) : ‖(x : AddCircle p)‖ = |x| ↔ |x| ≤ |p| / 2 := by
  refine ⟨fun hx => hx ▸ norm_le_half_period p hp, fun hx => ?_⟩
  suffices ∀ p : ℝ, 0 < p → |x| ≤ p / 2 → ‖(x : AddCircle p)‖ = |x| by
    -- Porting note: replaced `lt_trichotomy` which had trouble substituting `p = 0`.
    rcases hp.symm.lt_or_lt with (hp | hp)
    · rw [abs_eq_self.mpr hp.le] at hx
      exact this p hp hx
    · rw [← norm_neg_period]
      rw [abs_eq_neg_self.mpr hp.le] at hx
      exact this (-p) (neg_pos.mpr hp) hx
  clear hx
  intro p hp hx
  rcases eq_or_ne x (p / (2 : ℝ)) with (rfl | hx')
  · simp [abs_div, abs_two]
  suffices round (p⁻¹ * x) = 0 by simp [norm_eq, this]
  rw [round_eq_zero_iff]
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  replace hx₂ := Ne.lt_of_le hx' hx₂
  constructor
  · rwa [← mul_le_mul_left hp, ← mul_assoc, mul_inv_cancel hp.ne.symm, one_mul, mul_neg, ←
      mul_div_assoc, mul_one]
  · rwa [← mul_lt_mul_left hp, ← mul_assoc, mul_inv_cancel hp.ne.symm, one_mul, ← mul_div_assoc,
      mul_one]
#align add_circle.norm_coe_eq_abs_iff AddCircle.norm_coe_eq_abs_iff

open Metric

theorem closedBall_eq_univ_of_half_period_le (hp : p ≠ 0) (x : AddCircle p) {ε : ℝ}
    (hε : |p| / 2 ≤ ε) : closedBall x ε = univ :=
  eq_univ_iff_forall.mpr fun x => by
    simpa only [mem_closedBall, dist_eq_norm] using (norm_le_half_period p hp).trans hε
#align add_circle.closed_ball_eq_univ_of_half_period_le AddCircle.closedBall_eq_univ_of_half_period_le

@[simp]
theorem coe_real_preimage_closedBall_period_zero (x ε : ℝ) :
    (↑) ⁻¹' closedBall (x : AddCircle (0 : ℝ)) ε = closedBall x ε := by
  ext y
  -- Porting note: squeezed the simp
  simp only [Set.mem_preimage, dist_eq_norm, AddCircle.norm_eq_of_zero, iff_self,
    ← QuotientAddGroup.mk_sub, Metric.mem_closedBall, Real.norm_eq_abs]
#align add_circle.coe_real_preimage_closed_ball_period_zero AddCircle.coe_real_preimage_closedBall_period_zero

theorem coe_real_preimage_closedBall_eq_iUnion (x ε : ℝ) :
    (↑) ⁻¹' closedBall (x : AddCircle p) ε = ⋃ z : ℤ, closedBall (x + z • p) ε := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp [iUnion_const]
  ext y
  simp only [dist_eq_norm, mem_preimage, mem_closedBall, zsmul_eq_mul, mem_iUnion, Real.norm_eq_abs,
    ← QuotientAddGroup.mk_sub, norm_eq, ← sub_sub]
  refine ⟨fun h => ⟨round (p⁻¹ * (y - x)), h⟩, ?_⟩
  rintro ⟨n, hn⟩
  rw [← mul_le_mul_left (abs_pos.mpr <| inv_ne_zero hp), ← abs_mul, mul_sub, mul_comm _ p,
    inv_mul_cancel_left₀ hp] at hn ⊢
  exact (round_le (p⁻¹ * (y - x)) n).trans hn
#align add_circle.coe_real_preimage_closed_ball_eq_Union AddCircle.coe_real_preimage_closedBall_eq_iUnion

theorem coe_real_preimage_closedBall_inter_eq {x ε : ℝ} (s : Set ℝ)
    (hs : s ⊆ closedBall x (|p| / 2)) :
    (↑) ⁻¹' closedBall (x : AddCircle p) ε ∩ s = if ε < |p| / 2 then closedBall x ε ∩ s else s := by
  rcases le_or_lt (|p| / 2) ε with hε | hε
  · rcases eq_or_ne p 0 with (rfl | hp)
    · simp only [abs_zero, zero_div] at hε
      simp only [not_lt.mpr hε, coe_real_preimage_closedBall_period_zero, abs_zero, zero_div,
        if_false, inter_eq_right]
      exact hs.trans (closedBall_subset_closedBall <| by simp [hε])
    -- Porting note: was
    -- simp [closedBall_eq_univ_of_half_period_le p hp (↑x) hε, not_lt.mpr hε]
    simp only [not_lt.mpr hε, ite_false, inter_eq_right]
    rw [closedBall_eq_univ_of_half_period_le p hp (↑x : ℝ ⧸ zmultiples p) hε, preimage_univ]
    apply subset_univ
  · suffices ∀ z : ℤ, closedBall (x + z • p) ε ∩ s = if z = 0 then closedBall x ε ∩ s else ∅ by
      simp [-zsmul_eq_mul, ← QuotientAddGroup.mk_zero, coe_real_preimage_closedBall_eq_iUnion,
        iUnion_inter, iUnion_ite, this, hε]
    intro z
    simp only [Real.closedBall_eq_Icc, zero_sub, zero_add] at hs ⊢
    rcases eq_or_ne z 0 with (rfl | hz)
    · simp
    simp only [hz, zsmul_eq_mul, if_false, eq_empty_iff_forall_not_mem]
    rintro y ⟨⟨hy₁, hy₂⟩, hy₀⟩
    obtain ⟨hy₃, hy₄⟩ := hs hy₀
    rcases lt_trichotomy 0 p with (hp | (rfl : 0 = p) | hp)
    · cases' Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz with hz' hz'
      · have : ↑z * p ≤ -p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
      · have : p ≤ ↑z * p := by nlinarith
        linarith [abs_eq_self.mpr hp.le]
    · simp only [mul_zero, add_zero, abs_zero, zero_div] at hy₁ hy₂ hε
      linarith
    · cases' Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz with hz' hz'
      · have : -p ≤ ↑z * p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]
      · have : ↑z * p ≤ p := by nlinarith
        linarith [abs_eq_neg_self.mpr hp.le]
#align add_circle.coe_real_preimage_closed_ball_inter_eq AddCircle.coe_real_preimage_closedBall_inter_eq

section FiniteOrderPoints

variable {p} [hp : Fact (0 < p)]

theorem norm_div_natCast {m n : ℕ} :
    ‖(↑(↑m / ↑n * p) : AddCircle p)‖ = p * (↑(min (m % n) (n - m % n)) / n) := by
  have : p⁻¹ * (↑m / ↑n * p) = ↑m / ↑n := by rw [mul_comm _ p, inv_mul_cancel_left₀ hp.out.ne.symm]
  rw [norm_eq' p hp.out, this, abs_sub_round_div_natCast_eq]
#align add_circle.norm_div_nat_cast AddCircle.norm_div_natCast

@[deprecated (since := "2024-04-17")]
alias norm_div_nat_cast := norm_div_natCast

theorem exists_norm_eq_of_isOfFinAddOrder {u : AddCircle p} (hu : IsOfFinAddOrder u) :
    ∃ k : ℕ, ‖u‖ = p * (k / addOrderOf u) := by
  let n := addOrderOf u
  change ∃ k : ℕ, ‖u‖ = p * (k / n)
  obtain ⟨m, -, -, hm⟩ := exists_gcd_eq_one_of_isOfFinAddOrder hu
  refine ⟨min (m % n) (n - m % n), ?_⟩
  rw [← hm, norm_div_natCast]
#align add_circle.exists_norm_eq_of_fin_add_order AddCircle.exists_norm_eq_of_isOfFinAddOrder

theorem le_add_order_smul_norm_of_isOfFinAddOrder {u : AddCircle p} (hu : IsOfFinAddOrder u)
    (hu' : u ≠ 0) : p ≤ addOrderOf u • ‖u‖ := by
  obtain ⟨n, hn⟩ := exists_norm_eq_of_isOfFinAddOrder hu
  replace hu : (addOrderOf u : ℝ) ≠ 0 := by
    norm_cast
    exact (addOrderOf_pos_iff.mpr hu).ne'
  conv_lhs => rw [← mul_one p]
  rw [hn, nsmul_eq_mul, ← mul_assoc, mul_comm _ p, mul_assoc, mul_div_cancel₀ _ hu,
    mul_le_mul_left hp.out, Nat.one_le_cast, Nat.one_le_iff_ne_zero]
  contrapose! hu'
  simpa only [hu', Nat.cast_zero, zero_div, mul_zero, norm_eq_zero] using hn
#align add_circle.le_add_order_smul_norm_of_is_of_fin_add_order AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder

end FiniteOrderPoints

end AddCircle

namespace UnitAddCircle

theorem norm_eq {x : ℝ} : ‖(x : UnitAddCircle)‖ = |x - round x| := by simp [AddCircle.norm_eq]
#align unit_add_circle.norm_eq UnitAddCircle.norm_eq

end UnitAddCircle
