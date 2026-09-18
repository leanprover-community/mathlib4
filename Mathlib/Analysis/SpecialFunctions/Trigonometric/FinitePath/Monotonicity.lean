/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.FinitePath.BernsteinCertificate
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.FinitePath.Limit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.FinitePath.Positivity

/-!
# Monotonicity of finite path coherence

The coherence is strictly increasing from size four and stays strictly below its limit.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Real.FinitePath

private lemma sin_taylor_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x :=
  Real.sin_ge_sub_cube hx

private lemma cos_taylor_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv : ∀ t : ℝ, deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have hs := sin_taylor_lower ht.le
    nlinarith
  have h := hmono (by simp) hx hx
  simp only [f, Real.cos_zero] at h
  nlinarith

private lemma sin_taylor_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv : ∀ t : ℝ, deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have hc := cos_taylor_upper ht.le
    nlinarith
  have h := hmono (by simp) hx hx
  simp only [f, Real.sin_zero] at h
  nlinarith

private lemma cos_taylor_lower {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t =>
    Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720
  have hderiv : ∀ t : ℝ,
      deriv f t = -Real.sin t + t - t ^ 3 / 6 + t ^ 5 / 120 := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have hs := sin_taylor_upper ht.le
    nlinarith
  have h := hmono (by simp) hx hx
  simp only [f, Real.cos_zero] at h
  nlinarith

/-- Continuous angular form of the squared finite path coherence. -/
private noncomputable def coherenceSqAngle (x : ℝ) : ℝ :=
  ((Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 + 8 * x / Real.pi) / 3) *
      Real.tan x ^ 2 - 2 + 4 * x / Real.pi

private lemma coherenceSq_eq_coherenceSqAngle (d : ℕ) (hd : 4 ≤ d) :
    coherenceSq d = coherenceSqAngle (angle d) := by
  have hN : size d ≠ 0 := by unfold size; positivity
  have htpos : 0 < angle d := by unfold angle size; positivity
  have htlt : angle d < Real.pi / 2 := by
    unfold angle size
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (d:ℝ) + 1) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [show (4 : ℝ) ≤ d by exact_mod_cast hd, Real.pi_pos]
  have hcos : Real.cos (angle d) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, htlt⟩).ne'
  have htne : angle d ≠ 0 := htpos.ne'
  have hpiθ : Real.pi = angle d * size d := by
    unfold angle; field_simp
  have hpyth : Real.sin (angle d) ^ 2 = 1 - Real.cos (angle d) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (angle d)
    linarith
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [coherenceSq, coherenceSqAngle, Real.tan_eq_sin_div_cos, hpiθ]
  unfold size
  field_simp [hcos, htne, hd1]
  rw [hpyth]
  ring

private lemma hasDerivAt_coherenceSqAngle {x : ℝ}
    (hx : x ≠ 0) (hcos : Real.cos x ≠ 0) :
    HasDerivAt coherenceSqAngle
      (((-2 * Real.pi ^ 2 / x ^ 3 + 2 * Real.pi / x ^ 2 + 8 / Real.pi) *
          Real.sin x ^ 2 * Real.cos x +
        2 * (Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 +
          8 * x / Real.pi) * Real.sin x +
        12 / Real.pi * Real.cos x ^ 3) /
        (3 * Real.cos x ^ 3)) x := by
  unfold coherenceSqAngle
  have htan : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x := Real.hasDerivAt_tan hcos
  have da := (hasDerivAt_const x (Real.pi ^ 2)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  have db := (hasDerivAt_const x (2 * Real.pi)).div (hasDerivAt_id x) hx
  have dab := da.sub db
  have dabc := dab.sub (hasDerivAt_const x (4 : ℝ))
  have dd := ((hasDerivAt_const x (8 : ℝ)).mul (hasDerivAt_id x)).div_const Real.pi
  have dQ := dabc.add dd
  have dQdiv3 := dQ.div_const 3
  have dtansq := htan.pow 2
  have dmul := dQdiv3.mul dtansq
  have dsub2 := dmul.sub (hasDerivAt_const x (2 : ℝ))
  have de := ((hasDerivAt_const x (4 : ℝ)).mul (hasDerivAt_id x)).div_const Real.pi
  have dfinal := dsub2.add de
  refine dfinal.congr_deriv ?_
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.div_apply]
  field_simp [hx, Real.pi_ne_zero]
  have hsin : Real.sin x = Real.tan x * Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  rw [hsin]
  ring

set_option maxHeartbeats 1000000 in
-- The polynomial normalization in this proof exceeds the default heartbeat budget.
private lemma deriv_coherenceSqAngle_neg {x : ℝ}
    (hx0 : 0 < x) (hx5 : x ≤ Real.pi / 5) :
    deriv coherenceSqAngle x < 0 := by
  have hxhalf : x < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hxone : x ≤ 1 := by
    have hpilt : Real.pi < (4 : ℝ) := Real.pi_lt_four
    nlinarith
  have hcospos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hxhalf⟩
  have hspos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by nlinarith [Real.pi_pos])
  let y : ℝ := x / Real.pi
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy5 : y ≤ 1 / 5 := by
    dsimp [y]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpi22 : Real.pi ≤ (22 / 7 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hpoly := coherence_derivative_remainder_neg hy0 hy5 hpi3 hpi22
  let sl : ℝ := x - x ^ 3 / 6
  let su : ℝ := x - x ^ 3 / 6 + x ^ 5 / 120
  let cl : ℝ := 1 - x ^ 2 / 2
  let cu : ℝ := 1 - x ^ 2 / 2 + x ^ 4 / 24
  let q : ℝ := Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 +
    8 * x / Real.pi
  let qp : ℝ := -2 * Real.pi ^ 2 / x ^ 3 + 2 * Real.pi / x ^ 2 +
    8 / Real.pi
  have hsl : sl ≤ Real.sin x := by
    simpa [sl] using sin_taylor_lower hx0.le
  have hsu : Real.sin x ≤ su := by
    simpa [su] using sin_taylor_upper hx0.le
  have hcl : cl ≤ Real.cos x := by
    simpa [cl] using Real.one_sub_sq_div_two_le_cos (x := x)
  have hcu : Real.cos x ≤ cu := by
    simpa [cu] using cos_taylor_upper hx0.le
  have hsl0 : 0 < sl := by
    dsimp [sl]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hxpow : x ^ 3 = x * x ^ 2 := by ring
    rw [hxpow]
    nlinarith
  have hcl0 : 0 < cl := by
    dsimp [cl]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    nlinarith
  have hcu0 : 0 < cu := lt_of_lt_of_le hcospos hcu
  have hqpos : 0 < q := by
    have hypos : 0 < y := by dsimp [y]; positivity
    have hy_sq : y ^ 2 ≤ (1 / 5 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hy0 hy5 2
    have hbase : 0 < 1 - 2 * y - 4 * y ^ 2 + 8 * y ^ 3 := by
      have hy3 : 0 ≤ y ^ 3 := by positivity
      nlinarith
    dsimp [q, y] at hbase ⊢
    field_simp [hx0.ne', Real.pi_ne_zero] at hbase ⊢
    nlinarith [sq_nonneg x, sq_nonneg Real.pi]
  have hqpneg : qp < 0 := by
    have hypos : 0 < y := by dsimp [y]; positivity
    have hy3 : y ^ 3 ≤ (1 / 5 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hy0 hy5 3
    have hbase : -2 + 2 * y + 8 * y ^ 3 < 0 := by nlinarith
    dsimp [qp, y] at hbase ⊢
    field_simp [hx0.ne', Real.pi_ne_zero] at hbase ⊢
    nlinarith [sq_nonneg x, sq_nonneg Real.pi]
  have hsq : sl ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ hsl0.le hsl 2
  have hprod : sl ^ 2 * cl ≤ Real.sin x ^ 2 * Real.cos x := by
    exact mul_le_mul hsq hcl hcl0.le (sq_nonneg _)
  have hcube : Real.cos x ^ 3 ≤ cu ^ 3 :=
    pow_le_pow_left₀ hcospos.le hcu 3
  have hupper :
      qp * (Real.sin x ^ 2 * Real.cos x) + 2 * q * Real.sin x +
          12 / Real.pi * Real.cos x ^ 3 ≤
        qp * (sl ^ 2 * cl) + 2 * q * su +
          12 / Real.pi * cu ^ 3 := by
    have h1 := mul_le_mul_of_nonpos_left hprod hqpneg.le
    have h2 := mul_le_mul_of_nonneg_left hsu (by positivity : 0 ≤ 2 * q)
    have h3 := mul_le_mul_of_nonneg_left hcube
      (by positivity : 0 ≤ 12 / Real.pi)
    linarith
  have hrem : qp * (sl ^ 2 * cl) + 2 * q * su +
      12 / Real.pi * cu ^ 3 < 0 := by
    have heq :
        Real.pi * (qp * (sl ^ 2 * cl) + 2 * q * su +
          12 / Real.pi * cu ^ 3) =
        (5 * Real.pi ^ 12 * y ^ 12 - 180 * Real.pi ^ 10 * y ^ 10 +
          1880 * Real.pi ^ 8 * y ^ 8 - 160 * Real.pi ^ 8 * y ^ 6 +
          160 * Real.pi ^ 8 * y ^ 5 - 7552 * Real.pi ^ 6 * y ^ 6 -
          384 * Real.pi ^ 6 * y ^ 5 + 2048 * Real.pi ^ 6 * y ^ 4 -
          2144 * Real.pi ^ 6 * y ^ 3 + 6720 * Real.pi ^ 4 * y ^ 4 +
          7680 * Real.pi ^ 4 * y ^ 3 - 5760 * Real.pi ^ 4 * y ^ 2 +
          7680 * Real.pi ^ 4 * y + 34560 * Real.pi ^ 2 * y ^ 2 -
          46080 * Real.pi ^ 2 * y - 11520 * Real.pi ^ 2 + 69120) / 5760 := by
      dsimp [qp, q, sl, su, cl, cu, y]
      field_simp [hx0.ne', Real.pi_ne_zero]
      ring
    rw [← heq] at hpoly
    nlinarith [hpoly, Real.pi_pos]
  have hnum := hupper.trans_lt hrem
  rw [(hasDerivAt_coherenceSqAngle hx0.ne' hcospos.ne').deriv]
  dsimp [qp, q] at hnum ⊢
  apply div_neg_of_neg_of_pos _ (by positivity)
  nlinarith [hnum]

private lemma coherenceSqAngle_strictAntiOn :
    StrictAntiOn coherenceSqAngle (Set.Ioc 0 (Real.pi / 5)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (Real.pi / 5))
  · intro x hx
    obtain ⟨hx0, hx5⟩ := hx
    have hxhalf : x < Real.pi / 2 := by nlinarith [Real.pi_pos, hx5]
    have hcospos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxhalf⟩
    exact (hasDerivAt_coherenceSqAngle hx0.ne' hcospos.ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact deriv_coherenceSqAngle_neg hx.1 hx.2.le

theorem coherenceSq_strictMonoOn :
    StrictMonoOn coherenceSq {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  rw [coherenceSq_eq_coherenceSqAngle a ha,
    coherenceSq_eq_coherenceSqAngle b hb]
  have hta0 : 0 < angle a := by unfold angle size; positivity
  have htb0 : 0 < angle b := by unfold angle size; positivity
  have hta5 : angle a ≤ Real.pi / 5 := by
    unfold angle size
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)]
    have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [Real.pi_pos]
  have htb5 : angle b ≤ Real.pi / 5 := by
    unfold angle size
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)]
    have hbR : (4 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [Real.pi_pos]
  have htheta : angle b < angle a := by
    unfold angle size
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    nlinarith [Real.pi_pos]
  exact coherenceSqAngle_strictAntiOn ⟨htb0, htb5⟩ ⟨hta0, hta5⟩ htheta

theorem coherence_strictMonoOn :
    StrictMonoOn coherence {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  unfold coherence
  exact Real.sqrt_lt_sqrt (zero_le_one.trans (one_lt_coherenceSq a ha).le)
    (coherenceSq_strictMonoOn ha hb hab)

theorem gap_strictMonoOn :
    StrictMonoOn gap {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  simpa [gap] using coherence_strictMonoOn ha hb hab

theorem coherence_four_le (d : ℕ) (hd : 4 ≤ d) : coherence 4 ≤ coherence d := by
  rcases eq_or_lt_of_le hd with h | h
  · simp [h]
  · have hmem4 : (4 : ℕ) ∈ {d : ℕ | 4 ≤ d} := le_refl 4
    have hmemd : d ∈ {d : ℕ | 4 ≤ d} := hd
    exact (coherence_strictMonoOn hmem4 hmemd h).le

theorem gap_four_le (d : ℕ) (hd : 4 ≤ d) :
    gap 4 ≤ gap d := by
  simpa [gap] using coherence_four_le d hd

theorem gap_sq_four_le (d : ℕ) (hd : 4 ≤ d) :
    gap 4 ^ 2 ≤ gap d ^ 2 := by
  have h4 : 0 < gap 4 := by
    simpa [gap] using one_lt_coherence 4 (by omega)
  have hd0 : 0 < gap d := by
    simpa [gap] using one_lt_coherence d hd
  nlinarith [gap_four_le d hd]

private theorem coherence_tail_strictMono :
    StrictMono (fun n : ℕ => coherence (n + 4)) := by
  intro a b hab
  have hmemA : a + 4 ∈ {d : ℕ | 4 ≤ d} := Nat.le_add_left 4 a
  have hmemB : b + 4 ∈ {d : ℕ | 4 ≤ d} := Nat.le_add_left 4 b
  have hlt : a + 4 < b + 4 := by omega
  exact coherence_strictMonoOn hmemA hmemB hlt

private theorem coherence_tail_tendsto :
    Tendsto (fun n : ℕ => coherence (n + 4)) atTop (𝓝 coherenceLimit) := by
  exact (Filter.tendsto_add_atTop_iff_nat 4).2 coherence_tendsto_aux

theorem coherence_lt_limit (d : ℕ) (hd : 4 ≤ d) : coherence d < coherenceLimit := by
  let n := d - 4
  have hdn : n + 4 = d := by dsimp [n]; omega
  have hstep : coherence (n + 4) < coherence ((n + 1) + 4) :=
    coherence_tail_strictMono (Nat.lt_succ_self n)
  have hlimit : coherence ((n + 1) + 4) ≤ coherenceLimit :=
    coherence_tail_strictMono.monotone.ge_of_tendsto coherence_tail_tendsto (n + 1)
  rw [← hdn]
  exact hstep.trans_le hlimit

theorem gap_lt_limit (d : ℕ) (hd : 4 ≤ d) :
    gap d < gapLimit := by
  simpa [gap, gapLimit] using coherence_lt_limit d hd

end Real.FinitePath
