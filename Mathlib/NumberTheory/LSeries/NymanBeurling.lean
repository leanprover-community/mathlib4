/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Nyman–Beurling and Báez-Duarte $L^2(0, 1)$ Approximations for the Riemann Hypothesis

This file formalizes Titchmarsh's (1986, Eq. 2.1.5) Mellin transform identity for the reciprocal
fractional part `{1 / x}` across the right half-plane `0 < Re(s)`, `s ≠ 1`, together with the
spatial `L²(0, 1)` Cauchy–Schwarz lower bounds and forward theorems of Nyman (1950),
Beurling (1955), and Báez-Duarte (2003): if `1` lies in the `L²(0, 1)` closure of constrained or
unconstrained finite linear combinations of `x ↦ {1 / (k * x)}`, then `RiemannHypothesis` holds.
-/

@[expose] public section

open MeasureTheory Set Filter

/-- The reciprocal fractional-part function `x ↦ {1 / x}`. -/
noncomputable def recipFract (x : ℝ) : ℝ :=
  Int.fract (1 / x)

/-- The `k`-th dilated reciprocal fractional-part function `x ↦ {1 / (k * x)}`. -/
noncomputable def recipFractScaled (k : ℕ) (x : ℝ) : ℝ :=
  Int.fract (1 / ((k : ℝ) * x))

/-- The `n`-th harmonic sub-interval summand appearing in the continuation of
`∫ x in Ioc 0 1, {1 / x} * x ^ (s - 1)` for `0 < Re(s)`, `s ≠ 1`. -/
noncomputable def harmonicUnitSummand (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
    ((n : ℂ) / s) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))

private lemma recipFractScaled_eq_of_gt_one {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 1 < x) :
    recipFractScaled k x = 1 / ((k : ℝ) * x) := by
  unfold recipFractScaled
  have hk_ge : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkx : 1 < (k : ℝ) * x := by nlinarith
  rw [Int.fract_eq_self]
  exact ⟨by positivity, (div_lt_one (by linarith)).mpr hkx⟩

private lemma norm_recipFractScaled_le_one (k : ℕ) (x : ℝ) :
    ‖(recipFractScaled k x : ℂ)‖ ≤ 1 := by
  unfold recipFractScaled
  rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

private lemma norm_recipFract_le_one (x : ℝ) : ‖(recipFract x : ℂ)‖ ≤ 1 := by
  simpa [recipFract, recipFractScaled] using norm_recipFractScaled_le_one 1 x

private lemma measurable_recipFractScaled (k : ℕ) : Measurable (recipFractScaled k) :=
  measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))

private lemma measurable_recipFract : Measurable recipFract :=
  measurable_fract.comp (measurable_const.div measurable_id)

lemma integrableOn_Ioc_cpow (s : ℂ) (hs_pos : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
  refine hrpow.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne')).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    simp

private lemma integrableOn_Ioc_recipFract_cpow (s : ℂ) (hs_pos : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
  refine hrpow.mono' ?_ ?_
  · refine measurable_recipFract.complex_ofReal.aestronglyMeasurable.restrict.mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne')).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
    exact (mul_le_mul_of_nonneg_right (norm_recipFract_le_one x)
      (Real.rpow_nonneg hx.1.le _)).trans (one_mul _).le

private lemma integrableOn_Ioi_recipFract_cpow (s : ℂ) (hs_lt_one : s.re < 1) :
    IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi (1 : ℝ)) := by
  have ha_lt : (s - 2).re < -1 := by
    simp only [Complex.sub_re, Complex.re_ofNat]
    linarith
  refine (integrableOn_Ioi_cpow_of_lt ha_lt zero_lt_one).congr_fun (fun x hx => ?_)
    measurableSet_Ioi
  have hx_pos : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hrf : recipFract x = 1 / x := by
    simpa [recipFract, recipFractScaled] using recipFractScaled_eq_of_gt_one le_rfl hx
  rw [hrf]
  push_cast
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hx_ne]
  congr 1
  ring

private lemma integrableOn_Ioi_recipFractScaled_cpow (k : ℕ) (hk : 1 ≤ k) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1) :
    IntegrableOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow_ne : (k : ℂ) ^ (s - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk_ne)
  have hunion : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hint_unscaled :
      IntegrableOn (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
    rw [hunion]
    exact (integrableOn_Ioc_recipFract_cpow s hs_pos).union
      (integrableOn_Ioi_recipFract_cpow s hs_lt_one)
  rw [← integrable_indicator_iff measurableSet_Ioi] at hint_unscaled ⊢
  have hscale : Integrable (fun x : ℝ => ((k : ℂ) ^ (s - 1))⁻¹ *
      ((Ioi (0 : ℝ)).indicator (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1))
        ((k : ℝ) * x))) :=
    (hint_unscaled.comp_mul_left' hk_pos.ne').const_mul ((k : ℂ) ^ (s - 1))⁻¹
  refine hscale.congr (ae_of_all _ fun x => ?_)
  dsimp only
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · have hkx : (k : ℝ) * x ∈ Ioi (0 : ℝ) := mul_pos hk_pos hx
    rw [indicator_of_mem hx, indicator_of_mem hkx]
    have hcp : (((k : ℝ) * x : ℝ) : ℂ) ^ (s - 1) = (k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg hk_pos.le (mem_Ioi.mp hx).le (s - 1)
    rw [hcp]
    change ((k : ℂ) ^ (s - 1))⁻¹ *
        ((recipFract ((k : ℝ) * x) : ℂ) * ((k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1))) =
      (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)
    unfold recipFractScaled recipFract
    field_simp [hpow_ne]
  · have hkx : (k : ℝ) * x ∉ Ioi (0 : ℝ) := fun hm => hx ((mul_pos_iff_of_pos_left hk_pos).mp hm)
    rw [indicator_of_notMem hx, indicator_of_notMem hkx, mul_zero]

private lemma mellin_recipFract_split (s : ℂ) (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1) :
    ∫ x in Ioi (0 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) +
      (∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
  rw [(Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (integrableOn_Ioc_recipFract_cpow s hs_pos) (integrableOn_Ioi_recipFract_cpow s hs_lt_one)

private lemma integral_Ioi_cpow_of_lt_one {a : ℂ} (ha : a.re < -1) :
    ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ a = -(1 / (a + 1)) := by
  have ha1_ne : a + 1 ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hd : ∀ x ∈ Ici (1 : ℝ),
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (a + 1) / (a + 1)) ((x : ℂ) ^ a) x := fun x hx => by
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    convert (hasDerivAt_ofReal_cpow_const hx_pos.ne' ha1_ne).div_const (a + 1) using 1
    simp [ha1_ne, mul_div_cancel_left₀]
  have ht : Tendsto (fun t : ℝ => (t : ℂ) ^ (a + 1) / (a + 1)) atTop (nhds (0 / (a + 1))) := by
    apply Tendsto.div_const
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hre : (a + 1).re < 0 := by simp only [Complex.add_re, Complex.one_re]; linarith
    have hnorm : (fun t : ℝ => ‖(t : ℂ) ^ (a + 1)‖) =ᶠ[atTop] fun t : ℝ => t ^ (a + 1).re := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht_pos
      exact Complex.norm_cpow_eq_rpow_re_of_pos ht_pos (a + 1)
    rw [tendsto_congr' hnorm]
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1).re)
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (integrableOn_Ioi_cpow_of_lt ha zero_lt_one) ht
  simpa [zero_div, Complex.ofReal_one, Complex.one_cpow, neg_div] using hres

private lemma mellin_recipFract_tail (s : ℂ) (hs_lt_one : s.re < 1) :
    ∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) = -(1 / (s - 1)) := by
  have hcongr : ∫ x in Ioi (1 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx_pos : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hrf : recipFract x = 1 / x := by
      simpa [recipFract, recipFractScaled] using recipFractScaled_eq_of_gt_one le_rfl hx
    rw [hrf]
    push_cast
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
    rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hx_ne]
    congr 1
    ring
  rw [hcongr]
  have ha_lt : (s - 2).re < -1 := by simp only [Complex.sub_re, Complex.re_ofNat]; linarith
  have htail := integral_Ioi_cpow_of_lt_one ha_lt
  have hs21 : s - 2 + 1 = s - 1 := by ring
  rwa [hs21] at htail

private lemma floor_one_div_eq_of_mem_Ioo {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) : ⌊1 / x⌋ = (n : ℤ) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hx_pos : 0 < x := lt_trans (one_div_pos.mpr hn1_pos) hx.1
  rw [Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · have h1 : (n : ℝ) = 1 / (1 / (n : ℝ)) := by rw [one_div_one_div]
    rw [Int.cast_natCast, h1]
    exact one_div_le_one_div_of_le hx_pos hx.2.le
  · have h2 : (n : ℝ) + 1 = 1 / (1 / ((n : ℝ) + 1)) := by rw [one_div_one_div]
    rw [Int.cast_natCast, h2]
    exact one_div_lt_one_div_of_lt (one_div_pos.mpr hn1_pos) hx.1

private lemma abel_harmonic_telescope (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) =
      (∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) - (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1),
      Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
    push_cast
    ring

private lemma sum_harmonic_floor_integral_eq (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) =
      (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) -
        (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) := by
  have hterm : (∑ n ∈ Finset.Ico 1 (M + 1),
      (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s))) =
      (1 / s) * ∑ n ∈ Finset.Ico 1 (M + 1),
        (n : ℂ) * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hterm, abel_harmonic_telescope]

private lemma inv_cpow_nat (m : ℕ) (w : ℂ) : ((1 / (m : ℝ) : ℝ) : ℂ) ^ w = (m : ℂ) ^ (-w) := by
  push_cast
  have harg : (m : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg m)]
    exact Real.pi_ne_zero.symm
  rw [one_div, Complex.inv_cpow_eq_ite, ite_eq_right_iff.mpr (fun h => absurd h harg),
    Complex.cpow_neg]

private lemma integral_Ioc_harmonic_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (x : ℂ) ^ (s - 1) =
      ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) / s := by
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith)
  rw [← intervalIntegral.integral_of_le hle,
    integral_cpow (Or.inl (by simp [Complex.sub_re]; linarith))]
  have hs1 : s - 1 + 1 = s := by ring
  rw [hs1, inv_cpow_nat n s, show ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ^ s = ((n + 1 : ℕ) : ℂ) ^ (-s)
    from by simpa [Nat.cast_add, Nat.cast_one] using inv_cpow_nat (n + 1) s]

private lemma floor_cpow_ae_const (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)))),
      ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) = (n : ℂ) * (x : ℂ) ^ (s - 1) := by
  have hdiff : ∀ᵐ x ∂volume, x ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) →
      x ∈ Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) := by
    have hne : ∀ᵐ x ∂volume, x ≠ (1 / (n : ℝ)) := ae_iff.mpr (by simp [measure_singleton])
    filter_upwards [hne] with x hne hx
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hdiff] with x hx_imp hx_ioc
  rw [floor_one_div_eq_of_mem_Ioo hn (hx_imp hx_ioc)]
  simp

private lemma integral_Ioc_harmonic_floor_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs_pos : 0 < s.re) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
  rw [integral_congr_ae (floor_cpow_ae_const n hn s), integral_const_mul,
    integral_Ioc_harmonic_cpow n hn s hs_pos]
  ring

private lemma integrableOn_Ioc_harmonic_floor_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcont : ContinuousOn (fun x : ℝ => (n : ℂ) * (x : ℂ) ^ (s - 1))
      (Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    refine ContinuousOn.mul continuousOn_const fun x hx => ?_
    have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx_pos.ne')).continuousWithinAt
  exact (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr
    ((floor_cpow_ae_const n hn s).mono fun _ h => h.symm)

private lemma truncated_floor_partition_aux (M : ℕ) (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (1 / ((M : ℝ) + 1)) 1) ∧
    ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) =
      ∑ n ∈ Finset.Ico 1 (M + 1),
        ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) := by
  induction M with
  | zero =>
    have hIoc : Ioc (1 / (((0 : ℕ) : ℝ) + 1)) 1 = ∅ := by norm_num
    rw [hIoc]
    simp
  | succ M ih =>
    rcases ih with ⟨ih_int, ih_eq⟩
    have ha : 1 / (((M + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    have hb : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
    have hunion : Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) 1 =
        Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1)) ∪ Ioc (1 / ((M : ℝ) + 1)) 1 :=
      (Ioc_union_Ioc_eq_Ioc ha hb).symm
    have hdisj : Disjoint (Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1)))
        (Ioc (1 / ((M : ℝ) + 1)) 1) := by
      rw [disjoint_left]
      intro x hx1 hx2
      linarith [hx1.2, hx2.1]
    have hleft_int : IntegrableOn (fun x : ℝ => ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1))
        (Ioc (1 / (((M + 1 : ℕ) : ℝ) + 1)) (1 / ((M : ℝ) + 1))) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        integrableOn_Ioc_harmonic_floor_cpow (M + 1) (by omega) s
    refine ⟨by rw [hunion]; exact hleft_int.union ih_int, ?_⟩
    rw [hunion, setIntegral_union hdisj measurableSet_Ioc hleft_int ih_int, ih_eq,
      Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), add_comm]
    congr 1
    simp [Nat.cast_add, Nat.cast_one]

private lemma integrableOn_Ioc_truncated_inv_mul_cpow (a : ℝ) (ha : 0 < a) (b : ℝ) (_hab : a ≤ b)
    (s : ℂ) :
    IntegrableOn (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) (Ioc a b) := by
  have hcont : ContinuousOn (fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) (Icc a b) := by
    refine ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le ha hx.1).ne')) ?_
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (lt_of_lt_of_le ha hx.1).ne')).continuousWithinAt
  exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private lemma integral_Ioc_inv_mul_cpow (a : ℝ) (ha : 0 < a) (b : ℝ) (hab : a ≤ b)
    (s : ℂ) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc a b, ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      ((b : ℂ) ^ (s - 1) - (a : ℂ) ^ (s - 1)) / (s - 1) := by
  have hcongr : ∫ x in Ioc a b, ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      ∫ x in Ioc a b, (x : ℂ) ^ (s - 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ha hx.1.le).ne'
    push_cast
    rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hx_ne]
    congr 1
    ring
  have hs2_ne : s - 2 ≠ -1 := fun h => hs_ne_one (by linear_combination h)
  have h0_not_mem : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab, mem_Icc]
    intro h0
    linarith [h0.1]
  rw [hcongr, ← intervalIntegral.integral_of_le hab, integral_cpow (Or.inr ⟨hs2_ne, h0_not_mem⟩)]
  have hs21 : s - 2 + 1 = s - 1 := by ring
  rw [hs21]

private noncomputable def truncatedTitchmarshRHS (s : ℂ) (M : ℕ) : ℂ :=
  (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
    (1 / s) * ((∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s)) -
      (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s))

private lemma integral_Ioc_truncated_recipFract_cpow (M : ℕ) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      truncatedTitchmarshRHS s M := by
  have ha : 0 < 1 / ((M : ℝ) + 1) := by positivity
  have hab : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
  have hdecomp : (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) =
      fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) -
        ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) := by
    ext x
    unfold recipFract Int.fract
    push_cast
    ring
  rw [hdecomp, integral_sub (integrableOn_Ioc_truncated_inv_mul_cpow _ ha 1 hab s)
      (truncated_floor_partition_aux M s).1,
    integral_Ioc_inv_mul_cpow _ ha 1 hab s hs_ne_one, (truncated_floor_partition_aux M s).2]
  have hsum :
      (∑ n ∈ Finset.Ico 1 (M + 1),
        ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
          ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1)) =
        ∑ n ∈ Finset.Ico 1 (M + 1),
          (n : ℂ) / s * ((n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)) :=
    Finset.sum_congr rfl fun n hn =>
      integral_Ioc_harmonic_floor_cpow n (Finset.mem_Ico.mp hn).1 s hs_pos
  rw [hsum, sum_harmonic_floor_integral_eq, Complex.ofReal_one, Complex.one_cpow]
  have hinv : (((1 / ((M : ℝ) + 1) : ℝ) : ℂ)) ^ (s - 1) = ((M + 1 : ℕ) : ℂ) ^ (1 - s) := by
    have heq : (1 / ((M : ℝ) + 1) : ℝ) = 1 / ((M + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [heq, inv_cpow_nat (M + 1) (s - 1)]
    congr 1
    ring
  rw [hinv]
  rfl

private lemma tendsto_truncatedTitchmarshRHS_eq_unit (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    Tendsto (truncatedTitchmarshRHS s) atTop
      (nhds (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))) := by
  have heq : truncatedTitchmarshRHS s = fun M : ℕ =>
      ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) := by
    ext M
    exact (integral_Ioc_truncated_recipFract_cpow M s hs_pos hs_ne_one).symm
  rw [heq]
  have hsub : (fun M : ℕ => ∫ x in Ioc (1 / ((M : ℝ) + 1)) 1,
      (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) = fun M : ℕ =>
      (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) -
      (∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
    ext M
    have h0 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    have h1 : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
    have hint := integrableOn_Ioc_recipFract_cpow s hs_pos
    have hsplit : ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
        (∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) +
        (∫ x in Ioc (1 / ((M : ℝ) + 1)) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) := by
      rw [(Ioc_union_Ioc_eq_Ioc h0 h1).symm]
      exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hint.mono_set (Ioc_subset_Ioc_right h1)) (hint.mono_set (Ioc_subset_Ioc_left h0))
    linear_combination -hsplit
  have hnorm_le : ∀ M : ℕ,
      ‖∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ((M : ℝ) + 1) ^ (-s.re) / s.re := fun M => by
    have h0 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    have h1 : 1 / ((M : ℝ) + 1) ≤ (1 : ℝ) := div_le_one_of_le₀ (by linarith) (by positivity)
    have hint_fn := (integrableOn_Ioc_recipFract_cpow s hs_pos).mono_set (Ioc_subset_Ioc_right h1)
    have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (s.re - 1))
        (Ioc (0 : ℝ) (1 / ((M : ℝ) + 1))) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h0]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1)
    have hle_int : ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)),
        ‖(recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), x ^ (s.re - 1) := by
      refine setIntegral_mono_on hint_fn.norm hint_rpow measurableSet_Ioc fun x hx => ?_
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_right (norm_recipFract_le_one x)
        (Real.rpow_nonneg hx.1.le _)).trans (one_mul _).le
    have hval : ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), x ^ (s.re - 1) =
        ((M : ℝ) + 1) ^ (-s.re) / s.re := by
      rw [← intervalIntegral.integral_of_le h0,
        integral_rpow (Or.inl (by linarith : (-1 : ℝ) < s.re - 1))]
      have hs1 : s.re - 1 + 1 = s.re := by ring
      rw [hs1, Real.zero_rpow hs_pos.ne', sub_zero, one_div,
        Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
    exact (norm_integral_le_integral_norm _).trans (hle_int.trans hval.le)
  have ht_zero : Tendsto (fun M : ℕ =>
      ∫ x in Ioc (0 : ℝ) (1 / ((M : ℝ) + 1)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1))
      atTop (nhds 0) := by
    have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have ht : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (-s.re) / s.re) atTop (nhds (0 / s.re)) :=
      ((tendsto_rpow_neg_atTop hs_pos).comp hm).div_const s.re
    rw [zero_div] at ht
    exact squeeze_zero_norm hnorm_le ht
  rw [hsub]
  simpa using tendsto_const_nhds.sub ht_zero

private lemma sum_harmonicUnitSummand_eq_truncatedTitchmarshRHS (s : ℂ)
    (_hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), harmonicUnitSummand s n = truncatedTitchmarshRHS s M := by
  have htelesc : ∑ n ∈ Finset.Ico 1 (M + 1),
      ((n : ℂ) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) =
      (1 - ((M + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
      have hcast : ((M + 1 : ℕ) : ℂ) + 1 = ((M + 1 + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [← hcast]
      field_simp [sub_ne_zero.mpr hs_ne_one]
      ring
  unfold harmonicUnitSummand
  rw [Finset.sum_sub_distrib, htelesc, sum_harmonic_floor_integral_eq s M]
  rfl

private lemma mellin_recipFract_unit_interval_of_one_lt_re (s : ℂ) (hs_gt_one : 1 < s.re) :
    ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s := by
  have hs_pos : 0 < s.re := by linarith
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs_gt_one; simp at hs_gt_one; linarith
  have hs_ne_one : s ≠ 1 := fun h => by rw [h] at hs_gt_one; simp at hs_gt_one
  have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hpow0 : Tendsto (fun t : ℝ => t ^ (1 - s.re)) atTop (nhds 0) := by
    simpa [neg_sub] using tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)
  have hpow : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (1 - s.re)) atTop (nhds 0) := hpow0.comp hm
  have h_succ : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℂ) ^ (1 - s)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine hpow.congr fun M => ?_
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hcast : ((M + 1 : ℕ) : ℂ) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re, Complex.one_re]
  have h_mul : Tendsto (fun M : ℕ => (M : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s)) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun M => ?_) hpow
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hcast : ((M + 1 : ℕ) : ℂ) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.norm_natCast,
      Complex.neg_re]
    calc (M : ℝ) * ((M : ℝ) + 1) ^ (-s.re)
        ≤ ((M : ℝ) + 1) * ((M : ℝ) + 1) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hpos.le _)
      _ = ((M : ℝ) + 1) ^ (1 : ℝ) * ((M : ℝ) + 1) ^ (-s.re) := by rw [Real.rpow_one]
      _ = ((M : ℝ) + 1) ^ (1 - s.re) := by rw [← Real.rpow_add hpos, sub_eq_add_neg]
  have h_zeta : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s))
      atTop (nhds (riemannZeta s)) := by
    have hsum := Complex.summable_one_div_nat_cpow.mpr hs_gt_one
    have hhas : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ s) (riemannZeta s) := by
      rw [zeta_eq_tsum_one_div_nat_cpow hs_gt_one]
      exact hsum.hasSum
    have ht : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), 1 / (n : ℂ) ^ s)
        atTop (nhds (riemannZeta s)) := hhas.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have heq : (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), 1 / (n : ℂ) ^ s) =
        fun M : ℕ => ∑ n ∈ Finset.Ico 1 (M + 1), (n : ℂ) ^ (-s) := by
      ext M
      induction M with
      | zero => simp [Complex.zero_cpow hs_ne]
      | succ M ih =>
        rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih,
          one_div, Complex.cpow_neg]
    rwa [heq] at ht
  have h1 := ((tendsto_const_nhds (x := (1 : ℂ))).sub h_succ).div_const (s - 1)
  have h2 := (tendsto_const_nhds (x := 1 / s)).mul (h_zeta.sub h_mul)
  have h12 : Tendsto (truncatedTitchmarshRHS s) atTop (nhds (1 / (s - 1) - riemannZeta s / s)) := by
    convert h1.sub h2 using 1
    · ext M; unfold truncatedTitchmarshRHS; push_cast; ring
    · simp [sub_zero, one_mul, div_eq_mul_inv, mul_comm]
  exact tendsto_nhds_unique (tendsto_truncatedTitchmarshRHS_eq_unit s hs_pos hs_ne_one) h12

private lemma integral_Ioc_harmonic_recipFract_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      harmonicUnitSummand s n := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith)
  have hdecomp : (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) =
      fun x : ℝ => ((1 / x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) -
        ((⌊1 / x⌋ : ℤ) : ℂ) * (x : ℂ) ^ (s - 1) := by
    ext x
    unfold recipFract Int.fract
    push_cast
    ring
  rw [hdecomp, integral_sub (integrableOn_Ioc_truncated_inv_mul_cpow _ (one_div_pos.mpr hn1_pos)
      (1 / (n : ℝ)) hle s) (integrableOn_Ioc_harmonic_floor_cpow n hn s),
    integral_Ioc_inv_mul_cpow _ (one_div_pos.mpr hn1_pos) (1 / (n : ℝ)) hle s hs_ne_one,
    integral_Ioc_harmonic_floor_cpow n hn s hs_pos]
  rw [inv_cpow_nat n (s - 1),
    show ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ^ (s - 1) = ((n + 1 : ℕ) : ℂ) ^ (1 - s) from by
      simpa [Nat.cast_add, Nat.cast_one, neg_sub] using inv_cpow_nat (n + 1) (s - 1)]
  simp only [neg_sub]
  rfl

private lemma norm_harmonicUnitSummand_le_of_le_re (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs_ge : δ ≤ s.re) (hs_ne_one : s ≠ 1) :
    ‖harmonicUnitSummand s n‖ ≤ ((n : ℝ) ^ (-δ) - ((n + 1 : ℕ) : ℝ) ^ (-δ)) / δ := by
  have hs_pos : 0 < s.re := lt_of_lt_of_le hδ hs_ge
  rw [← integral_Ioc_harmonic_recipFract_cpow n hn s hs_pos hs_ne_one]
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith)
  have hsub : Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) ⊆ Ioc (0 : ℝ) 1 :=
    Ioc_subset_Ioc (by positivity) (div_le_one_of_le₀ (by exact_mod_cast hn) (by positivity))
  have hint_fn := (integrableOn_Ioc_recipFract_cpow s hs_pos).mono_set hsub
  have hint_rpow : IntegrableOn (fun x : ℝ => x ^ (δ - 1))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    have hcont : ContinuousOn (fun x : ℝ => x ^ (δ - 1))
        (Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := fun x hx =>
      (Real.continuousAt_rpow_const _ _
        (Or.inl (lt_of_lt_of_le (one_div_pos.mpr hn1_pos) hx.1).ne')).continuousWithinAt
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hle_int : ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
      ‖(recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
      ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), x ^ (δ - 1) := by
    refine setIntegral_mono_on hint_fn.norm hint_rpow measurableSet_Ioc fun x hx => ?_
    have hx_mem := hsub hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx_mem.1, Complex.sub_re, Complex.one_re]
    calc ‖(recipFract x : ℂ)‖ * x ^ (s.re - 1)
        ≤ 1 * x ^ (s.re - 1) :=
          mul_le_mul_of_nonneg_right (norm_recipFract_le_one x) (Real.rpow_nonneg hx_mem.1.le _)
      _ = x ^ (s.re - 1) := one_mul _
      _ ≤ x ^ (δ - 1) := Real.rpow_le_rpow_of_exponent_ge hx_mem.1 hx_mem.2 (by linarith)
  have hval : ∫ x in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), x ^ (δ - 1) =
      ((n : ℝ) ^ (-δ) - ((n + 1 : ℕ) : ℝ) ^ (-δ)) / δ := by
    rw [← intervalIntegral.integral_of_le hle,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < δ - 1))]
    have hδ1 : δ - 1 + 1 = δ := by ring
    have inv_rpow : ∀ m : ℕ, (1 / (m : ℝ)) ^ δ = (m : ℝ) ^ (-δ) := fun m => by
      rw [one_div, Real.inv_rpow (Nat.cast_nonneg m), Real.rpow_neg (Nat.cast_nonneg m)]
    rw [hδ1, inv_rpow n, show (1 / ((n : ℝ) + 1)) ^ δ = ((n + 1 : ℕ) : ℝ) ^ (-δ) from by
      simpa [Nat.cast_add, Nat.cast_one] using inv_rpow (n + 1)]
  exact (norm_integral_le_integral_norm _).trans (hle_int.trans hval.le)

private lemma summable_rpow_diff_div (δ : ℝ) (hδ : 0 < δ) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ)) / δ) := by
  let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (-δ) / δ
  have hg_nn : ∀ n : ℕ, 0 ≤ g n - g (n + 1) := fun n => by
    have hle : (((n + 1 + 1 : ℕ) : ℝ) ^ (-δ)) ≤ ((n + 1 : ℕ) : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast Nat.le_succ (n + 1)) (by linarith)
    simpa [g, sub_div, Nat.cast_add, Nat.cast_one] using div_nonneg (sub_nonneg.mpr hle) hδ.le
  have hg_tz : Tendsto g atTop (nhds 0) := by
    have hm : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hpow : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ (-δ)) atTop (nhds 0) := by
      convert (tendsto_rpow_neg_atTop hδ).comp hm using 1
      ext M
      simp [Nat.cast_add, Nat.cast_one]
    simpa [g, zero_div] using hpow.div_const δ
  have hg_t : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, (g n - g (n + 1))) atTop
      (nhds (g 0)) := by
    simp_rw [Finset.sum_range_sub' g]
    simpa [sub_zero] using tendsto_const_nhds.sub hg_tz
  simpa [g, sub_div, Nat.cast_add, Nat.cast_one] using
    ((hasSum_iff_tendsto_nat_of_nonneg hg_nn (g 0)).mpr hg_t).summable

private lemma summable_harmonicUnitSummand (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    Summable (fun n : ℕ => harmonicUnitSummand s (n + 1)) := by
  refine (summable_rpow_diff_div s.re hs_pos).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_harmonicUnitSummand_le_of_le_re (n + 1) (by omega)
      s.re hs_pos s le_rfl hs_ne_one) |>.of_norm

private lemma tsum_harmonicUnitSummand_eq_unit_integral (s : ℂ)
    (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    (∑' n : ℕ, harmonicUnitSummand s (n + 1)) =
      ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs_pos; simp at hs_pos
  have ht1 := (summable_harmonicUnitSummand s hs_pos hs_ne_one).hasSum.tendsto_sum_nat
  have heq : (fun M : ℕ => ∑ n ∈ Finset.range M, harmonicUnitSummand s (n + 1)) =
      truncatedTitchmarshRHS s := by
    ext M
    rw [← sum_harmonicUnitSummand_eq_truncatedTitchmarshRHS s hs_ne hs_ne_one M]
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1), ih]
  rw [heq] at ht1
  exact tendsto_nhds_unique ht1 (tendsto_truncatedTitchmarshRHS_eq_unit s hs_pos hs_ne_one)

private lemma analyticOnNhd_tsum_harmonicUnitSummand :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑' n : ℕ, harmonicUnitSummand s (n + 1))
      {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  have hS_open : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hS_open
  let δ : ℝ := s.re / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [hs.1]
  let Uδ : Set ℂ := {w : ℂ | δ < w.re ∧ w ≠ 1}
  have hUδ_open : IsOpen Uδ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have h_diff_term : ∀ n : ℕ,
      DifferentiableOn ℂ (fun w : ℂ => harmonicUnitSummand w (n + 1)) Uδ := by
    intro n w hw
    have hw_ne_zero : w ≠ 0 := fun h0 => by
      rw [h0] at hw
      simp only [Uδ, Set.mem_ofPred_eq, Complex.zero_re] at hw
      linarith [hw.1, hδ]
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn2 : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ (1 - z)) w :=
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hn1)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 + 1 : ℕ) : ℂ) ^ (1 - z)) w :=
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hn2)
    have h3 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ (-z)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl hn1)
    have h4 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 + 1 : ℕ) : ℂ) ^ (-z)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl hn2)
    have h_all : DifferentiableAt ℂ (fun z : ℂ => harmonicUnitSummand z (n + 1)) w := by
      unfold harmonicUnitSummand
      exact ((h1.sub h2).div (differentiableAt_id.sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hw.2)).sub
          (((differentiableAt_const _).div differentiableAt_id hw_ne_zero).mul (h3.sub h4))
    exact h_all.differentiableWithinAt
  have h_diff_Uδ := Complex.differentiableOn_tsum_of_summable_norm (summable_rpow_diff_div δ hδ)
    h_diff_term hUδ_open fun n w hw =>
      norm_harmonicUnitSummand_le_of_le_re (n + 1) (by omega) δ hδ w hw.1.le hw.2
  exact (h_diff_Uδ.differentiableAt
    (hUδ_open.mem_nhds ⟨by dsimp [δ]; linarith [hs.1], hs.2⟩)).differentiableWithinAt

private lemma convex_linear_gt (f : ℂ →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {s : ℂ | r < f s} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
  by_cases ha0 : 0 < a
  · calc r = a * r + b * r := by rw [← add_mul, hab, one_mul]
      _ < a * f x + b * f y := add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx ha0) (mul_le_mul_of_nonneg_left hy.le hb)
  · have ha0' : a = 0 := le_antisymm (not_lt.mp ha0) ha
    have hb1 : b = 1 := by linarith
    rw [ha0', hb1]
    linarith

private lemma convex_linear_lt (f : ℂ →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {s : ℂ | f s < r} := by
  simpa [neg_lt_neg_iff] using convex_linear_gt (-f) (-r)

/-- Critical-strip series continuation of the Riemann zeta function: for `0 < s.re` and `s ≠ 1`,
`riemannZeta s = s / (s - 1) - s * ∑' n : ℕ, harmonicUnitSummand s (n + 1)`. -/
theorem riemannZeta_eq_tsum_harmonicUnitSummand (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * ∑' n : ℕ, harmonicUnitSummand s (n + 1) := by
  let S : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  let F : ℂ → ℂ := fun z =>
    riemannZeta z - z * (1 / (z - 1) - ∑' n : ℕ, harmonicUnitSummand z (n + 1))
  have hS_open : IsOpen S := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hF_ana : AnalyticOnNhd ℂ F S := by
    have h_zeta : AnalyticOnNhd ℂ riemannZeta S :=
      DifferentiableOn.analyticOnNhd
        (fun z hz => (differentiableAt_riemannZeta hz.2).differentiableWithinAt) hS_open
    have h_pole : AnalyticOnNhd ℂ (fun z : ℂ => (1 : ℂ) / (z - 1)) S :=
      DifferentiableOn.analyticOnNhd (fun z hz => ((differentiableAt_const (1 : ℂ)).div
        (differentiableAt_id.sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hz.2)).differentiableWithinAt) hS_open
    exact h_zeta.sub (analyticOnNhd_id.mul (h_pole.sub analyticOnNhd_tsum_harmonicUnitSummand))
  have hF_gt_one : ∀ z : ℂ, 1 < z.re → F z = 0 := fun z hz => by
    have hz_ne : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz; linarith
    have hz1 : z ≠ 1 := fun h1 => by rw [h1] at hz; simp at hz
    have htsum : (∑' n : ℕ, harmonicUnitSummand z (n + 1)) = 1 / (z - 1) - riemannZeta z / z := by
      rw [tsum_harmonicUnitSummand_eq_unit_integral z (by linarith) hz1,
        mellin_recipFract_unit_interval_of_one_lt_re z hz]
    dsimp [F]
    rw [htsum]
    field_simp [hz_ne]
    ring
  let U_top : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im}
  let U_bot : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0}
  let U_left : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}
  have hre0 : Convex ℝ {z : ℂ | 0 < z.re} := convex_linear_gt Complex.reLm 0
  have hright_open : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have htop_open : IsOpen U_top :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hU_top_sub : U_top ⊆ S := fun z ⟨hz_re, hz_im⟩ =>
    ⟨hz_re, fun h1 => by subst h1; simp at hz_im⟩
  have hU_bot_sub : U_bot ⊆ S := fun z ⟨hz_re, hz_im⟩ =>
    ⟨hz_re, fun h1 => by subst h1; simp at hz_im⟩
  have hU_left_sub : U_left ⊆ S := fun z ⟨hz_re, hz_lt⟩ =>
    ⟨hz_re, fun h1 => by subst h1; simp at hz_lt⟩
  have hzero_top : Set.EqOn F 0 U_top := by
    refine (hF_ana.mono hU_top_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (hre0.inter (convex_linear_gt Complex.imLm 0)).isPreconnected
      (z₀ := (2 : ℂ) + Complex.I) (by simp [U_top]) ?_
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 1 < z.re}, hright_open.mem_nhds (by simp), fun z hz => hF_gt_one z hz⟩
  have hzero_bot : Set.EqOn F 0 U_bot := by
    refine (hF_ana.mono hU_bot_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (hre0.inter (convex_linear_lt Complex.imLm 0)).isPreconnected
      (z₀ := (2 : ℂ) - Complex.I) (by simp [U_bot]) ?_
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 1 < z.re}, hright_open.mem_nhds (by simp), fun z hz => hF_gt_one z hz⟩
  have hzero_left : Set.EqOn F 0 U_left := by
    refine (hF_ana.mono hU_left_sub).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (hre0.inter (convex_linear_lt Complex.reLm 1)).isPreconnected
      (z₀ := (1 / 2 : ℂ) + Complex.I) (by simp [U_left]; norm_num) ?_
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨U_top, htop_open.mem_nhds (by simp [U_top]), fun z hz => hzero_top hz⟩
  have hFs : F s = 0 := by
    rcases lt_trichotomy s.re 1 with hlt | heq | hgt
    · exact hzero_left ⟨hs_pos, hlt⟩
    · have him : s.im ≠ 0 := fun h0 => hs_ne_one (Complex.ext heq h0)
      rcases lt_or_gt_of_ne him with hneg | hpos
      · exact hzero_bot ⟨hs_pos, hneg⟩
      · exact hzero_top ⟨hs_pos, hpos⟩
    · exact hF_gt_one s hgt
  have h_eq := sub_eq_zero.mp hFs
  rw [h_eq]
  ring

/-- Titchmarsh (1986, Eq. 2.1.5): for `0 < s.re` and `s ≠ 1`,
`∫ x in Ioc 0 1, ({1 / x} : ℂ) * x ^ (s - 1) = 1 / (s - 1) - riemannZeta s / s`. -/
theorem mellin_recipFract_unit_interval (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    ∫ x in Set.Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / (s - 1) - riemannZeta s / s := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs_pos; simp at hs_pos
  rw [← tsum_harmonicUnitSummand_eq_unit_integral s hs_pos hs_ne_one,
    riemannZeta_eq_tsum_harmonicUnitSummand s hs_pos hs_ne_one]
  field_simp [hs_ne]
  ring

/-- Schwarz conjugation symmetry of `riemannZeta` for `0 < s.re` and `s ≠ 1`:
`riemannZeta (conj s) = conj (riemannZeta s)`. -/
theorem riemannZeta_conj_of_pos_re (s : ℂ) (hs_pos : 0 < s.re) (hs_ne_one : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  have hcs_pos : 0 < (starRingEnd ℂ s).re := by simpa using hs_pos
  have hcs_ne_one : starRingEnd ℂ s ≠ 1 :=
    fun h1 => hs_ne_one (by simpa using congr_arg (starRingEnd ℂ) h1)
  have h_conj : ∀ (n : ℕ) (hn : 1 ≤ n),
      harmonicUnitSummand (starRingEnd ℂ s) n = starRingEnd ℂ (harmonicUnitSummand s n) := by
    intro n hn
    have cpow_nat_conj : ∀ (m : ℕ) (hm : 1 ≤ m) (w : ℂ),
        starRingEnd ℂ ((m : ℂ) ^ w) = (m : ℂ) ^ (starRingEnd ℂ w) := fun m hm w => by
      have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Complex.cpow_def_of_ne_zero hm_ne, Complex.cpow_def_of_ne_zero hm_ne,
        ← Complex.exp_conj, map_mul, ← Complex.ofReal_natCast,
        ← Complex.ofReal_log (Nat.cast_pos.mpr hm).le, Complex.conj_ofReal]
    symm
    unfold harmonicUnitSummand
    simp only [map_sub, map_div₀, map_mul, map_one, map_natCast]
    rw [cpow_nat_conj n hn (1 - s), cpow_nat_conj (n + 1) (by omega) (1 - s),
      cpow_nat_conj n hn (-s), cpow_nat_conj (n + 1) (by omega) (-s)]
    simp only [map_sub, map_one, map_neg]
  rw [riemannZeta_eq_tsum_harmonicUnitSummand s hs_pos hs_ne_one,
    riemannZeta_eq_tsum_harmonicUnitSummand (starRingEnd ℂ s) hcs_pos hcs_ne_one]
  simp only [map_sub, map_div₀, map_mul, map_one]
  congr 2
  rw [Complex.conj_tsum]
  exact tsum_congr fun n => h_conj (n + 1) (by omega)

/-- Any zero `s₀` of `riemannZeta` in the open critical strip `0 < s₀.re ∧ s₀.re < 1`
is non-real (`s₀.im ≠ 0`). -/
theorem im_ne_zero_of_inCriticalStrip_zeta_zero (s₀ : ℂ) (hs : 0 < s₀.re ∧ s₀.re < 1)
    (hz : riemannZeta s₀ = 0) : s₀.im ≠ 0 := by
  intro him
  have hs_real : s₀ = (s₀.re : ℂ) := Complex.ext rfl him
  have hs_ne_one : s₀ ≠ 1 := fun h1 => by rw [h1] at hs; simp at hs
  have hunit := mellin_recipFract_unit_interval s₀ hs.1 hs_ne_one
  rw [hz, zero_div, sub_zero] at hunit
  have hint_pos : 0 ≤ ∫ x in Ioc (0 : ℝ) 1, recipFract x * x ^ (s₀.re - 1) :=
    setIntegral_nonneg measurableSet_Ioc fun x hx =>
      mul_nonneg (Int.fract_nonneg _) (Real.rpow_nonneg hx.1.le _)
  have hint_eq : (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s₀ - 1)).re =
      ∫ x in Ioc (0 : ℝ) 1, recipFract x * x ^ (s₀.re - 1) := by
    have hint_int := integrableOn_Ioc_recipFract_cpow s₀ hs.1
    conv_lhs => rw [← Complex.reCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_int]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [Complex.reCLM_apply, hs_real, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_cpow hx.1.le, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  have hre_val : (1 / (s₀ - 1)).re = 1 / (s₀.re - 1) := by rw [hs_real]; norm_cast
  have hre_eq := congr_arg Complex.re hunit
  rw [hint_eq, hre_val] at hre_eq
  have hneg : 1 / (s₀.re - 1) < 0 := div_neg_of_pos_of_neg one_pos (by linarith [hs.2])
  linarith

lemma integral_Ioc_recipFractScaled_cpow (k : ℕ) (hk : 1 ≤ k) (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1) :
    ∫ x in Ioc (0 : ℝ) 1, (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / ((k : ℂ) * (s - 1)) - riemannZeta s / (s * (k : ℂ) ^ s) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs_ne_one : s ≠ 1 := fun h1 => by rw [h1] at hs; simp at hs
  have hpow_ne : (k : ℂ) ^ (s - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk_ne)
  have hIoi0 : ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      -(riemannZeta s / (s * (k : ℂ) ^ s)) := by
    have hscale := integral_comp_mul_left_Ioi
      (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1)) 0 hk_pos
    rw [mul_zero] at hscale
    have hcongr : ∫ x in Ioi (0 : ℝ),
        (recipFract ((k : ℝ) * x) : ℂ) * (((k : ℝ) * x : ℝ) : ℂ) ^ (s - 1) =
        (k : ℂ) ^ (s - 1) * ∫ x in Ioi (0 : ℝ),
          (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hcp : (((k : ℝ) * x : ℝ) : ℂ) ^ (s - 1) = (k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
        push_cast
        exact Complex.mul_cpow_ofReal_nonneg hk_pos.le (mem_Ioi.mp hx).le (s - 1)
      rw [hcp]
      change (recipFract ((k : ℝ) * x) : ℂ) * ((k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1)) =
        (k : ℂ) ^ (s - 1) * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
      unfold recipFractScaled recipFract
      ring
    have hmellin : ∫ x in Ioi (0 : ℝ), (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
        -(riemannZeta s / s) := by
      rw [mellin_recipFract_split s hs.1 hs.2, mellin_recipFract_unit_interval s hs.1 hs_ne_one,
        mellin_recipFract_tail s hs.2]
      ring
    rw [hcongr, hmellin] at hscale
    have hpow_s : (k : ℂ) ^ s = (k : ℂ) * (k : ℂ) ^ (s - 1) := by
      conv_lhs => rw [show s = 1 + (s - 1) from by ring, Complex.cpow_add _ _ hk_ne,
        Complex.cpow_one]
    have hsmul : ((k : ℝ)⁻¹ : ℝ) • -(riemannZeta s / s) = (k : ℂ)⁻¹ * -(riemannZeta s / s) := by
      rw [Complex.real_smul, Complex.ofReal_inv]
      rfl
    rw [hsmul] at hscale
    calc ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)
        = ((k : ℂ) ^ (s - 1))⁻¹ * ((k : ℂ) ^ (s - 1) *
            ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
      _ = ((k : ℂ) ^ (s - 1))⁻¹ * ((k : ℂ)⁻¹ * -(riemannZeta s / s)) := by rw [hscale]
      _ = -(riemannZeta s / (s * (k : ℂ) ^ s)) := by rw [hpow_s]; field_simp [hk_ne, hpow_ne]
  have hint_Ioi0 := integrableOn_Ioi_recipFractScaled_cpow k hk s hs.1 hs.2
  have h_union : ∫ x in Ioi (0 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      (∫ x in Ioc (0 : ℝ) 1, (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) +
      (∫ x in Ioi (1 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) := by
    rw [(Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint_Ioi0.mono_set fun _ hx => hx.1) (hint_Ioi0.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  have h_Ioi1 : ∫ x in Ioi (1 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      -(1 / ((k : ℂ) * (s - 1))) := by
    have h_ae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
        (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) = (1 / (k : ℂ)) * (x : ℂ) ^ (s - 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [recipFractScaled_eq_of_gt_one hk hx]
      have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one hx).ne'
      have hexp : (x : ℂ) ^ (s - 2) = (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (-1 : ℂ) := by
        rw [← Complex.cpow_add _ _ hx_ne]
        congr 1
        ring
      rw [hexp, Complex.cpow_neg_one]
      push_cast
      ring
    rw [integral_congr_ae h_ae, integral_const_mul]
    have hre : (s - 2).re < -1 := by simp [Complex.sub_re]; linarith [hs.2]
    have h := integral_Ioi_cpow_of_lt_one hre
    rw [show s - 2 + 1 = s - 1 from by ring] at h
    rw [h]
    field_simp [hk_ne, sub_ne_zero.mpr hs_ne_one]
  rw [hIoi0, h_Ioi1] at h_union
  linear_combination -h_union

private lemma sq_sub_norm_lower_bound (R g : ℝ → ℂ) (lam α : ℂ) (G_norm : ℝ)
    (h_Gpos : 0 < G_norm) (hR_int : IntegrableOn (fun x => ‖R x‖ ^ 2) (Ioc (0 : ℝ) 1))
    (hg_int : IntegrableOn (fun x => ‖g x‖ ^ 2) (Ioc (0 : ℝ) 1))
    (hRg_int : IntegrableOn (fun x => R x * starRingEnd ℂ (g x)) (Ioc (0 : ℝ) 1))
    (h_inner : ∫ x in Ioc (0 : ℝ) 1, R x * starRingEnd ℂ (g x) = α)
    (h_gnorm : ∫ x in Ioc (0 : ℝ) 1, ‖g x‖ ^ 2 = G_norm)
    (h_lam : lam = α / (G_norm : ℂ)) :
    Complex.normSq α / G_norm ≤ ∫ x in Ioo (0 : ℝ) 1, ‖R x‖ ^ 2 := by
  have hint_cross : IntegrableOn
      (fun x : ℝ => 2 * (R x * starRingEnd ℂ (lam * g x)).re) (Ioc (0 : ℝ) 1) := by
    have heq : (fun x : ℝ => 2 * (R x * starRingEnd ℂ (lam * g x)).re) =
        fun x : ℝ => 2 * (starRingEnd ℂ lam * (R x * starRingEnd ℂ (g x))).re := by
      ext x; rw [map_mul]; congr 2; ring
    rw [heq]
    exact (hRg_int.const_mul (starRingEnd ℂ lam)).re.const_mul 2
  have h_sq_nonneg : 0 ≤ ∫ x in Ioc (0 : ℝ) 1, ‖R x - lam * g x‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  have h_expand : (fun x : ℝ => ‖R x - lam * g x‖ ^ 2) =
      fun x : ℝ => (‖R x‖ ^ 2 - 2 * (R x * starRingEnd ℂ (lam * g x)).re) +
        ‖lam‖ ^ 2 * ‖g x‖ ^ 2 := by
    ext a
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hint_sub : IntegrableOn
      (fun x : ℝ => ‖R x‖ ^ 2 - 2 * (R x * starRingEnd ℂ (lam * g x)).re) (Ioc (0 : ℝ) 1) :=
    hR_int.sub hint_cross
  have hint_lamg : IntegrableOn (fun x : ℝ => ‖lam‖ ^ 2 * ‖g x‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    hg_int.const_mul (‖lam‖ ^ 2)
  rw [h_expand, integral_add hint_sub hint_lamg, integral_sub hR_int hint_cross] at h_sq_nonneg
  have h_cross_val : ∫ x in Ioc (0 : ℝ) 1, 2 * (R x * starRingEnd ℂ (lam * g x)).re =
      2 * (Complex.normSq α / G_norm) := by
    have heq : (fun x : ℝ => 2 * (R x * starRingEnd ℂ (lam * g x)).re) =
        fun x : ℝ => 2 * (starRingEnd ℂ lam * (R x * starRingEnd ℂ (g x))).re := by
      ext x; rw [map_mul]; congr 2; ring
    rw [heq, integral_const_mul]
    simp_rw [← Complex.reCLM_apply]
    rw [ContinuousLinearMap.integral_comp_comm Complex.reCLM (hRg_int.const_mul _),
      integral_const_mul, h_inner, Complex.reCLM_apply, h_lam, map_div₀, Complex.conj_ofReal,
      div_mul_eq_mul_div, mul_comm (starRingEnd ℂ α) α, Complex.mul_conj, ← Complex.ofReal_div,
      Complex.ofReal_re]
  have h_lam_val : ∫ x in Ioc (0 : ℝ) 1, ‖lam‖ ^ 2 * ‖g x‖ ^ 2 =
      Complex.normSq α / G_norm := by
    rw [integral_const_mul, h_gnorm, h_lam, norm_div, Complex.norm_real, div_pow,
      ← Complex.normSq_eq_norm_sq, Real.norm_of_nonneg h_Gpos.le]
    field_simp [h_Gpos.ne']
  rw [h_cross_val, h_lam_val] at h_sq_nonneg
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
  linarith

private lemma residual_measurable_and_norm_le (N : ℕ) (c : ℕ → ℂ) :
    Measurable (fun x : ℝ => 1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)) ∧
    ∀ x : ℝ, ‖1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)‖ ≤
      1 + ∑ k ∈ Finset.Icc 1 N, ‖c k‖ := by
  refine ⟨measurable_const.sub (Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (measurable_recipFractScaled k).complex_ofReal), fun x => ?_⟩
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  refine add_le_add le_rfl
    ((norm_sum_le (Finset.Icc 1 N) _).trans (Finset.sum_le_sum fun k _ => ?_))
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_recipFractScaled_le_one k x) (norm_nonneg _)).trans
    (mul_one _).le

private lemma integrableOn_Ioc_residual_sq (N : ℕ) (c : ℕ → ℂ) :
    IntegrableOn (fun x : ℝ =>
      ‖1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  have ⟨hmeas, hbd⟩ := residual_measurable_and_norm_le N c
  refine (integrableOn_const (C := (1 + ∑ k ∈ Finset.Icc 1 N, ‖c k‖) ^ 2)
    (hs := measure_Ioc_lt_top.ne)).mono' (hmeas.norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbd x) 2

lemma integrableOn_Ioc_recipFractScaled_cpow (k : ℕ) (hk : 1 ≤ k) (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1) :
    IntegrableOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) :=
  (integrableOn_Ioi_recipFractScaled_cpow k hk s hs.1 hs.2).mono_set fun _ hx => hx.1

/-- Spatial `L²(0, 1)` Cauchy–Schwarz lower bound for constrained Nyman–Beurling combinations:
if `∑ k ∈ Finset.Icc 1 N, c k / k = 0` and `s₀` is a zero of `riemannZeta` with
`1 / 2 < s₀.re < 1`, then `(2 * s₀.re - 1) / normSq s₀ ≤ ∫ x in Ioo 0 1, ‖R_N(x)‖ ^ 2`. -/
theorem nymanBeurling_spatial_cauchy_floor (N : ℕ) (c : ℕ → ℂ)
    (hc : ∑ k ∈ Finset.Icc 1 N, c k / (k : ℂ) = 0)
    (s₀ : ℂ) (hs : 0 < s₀.re ∧ s₀.re < 1) (hre : 1 / 2 < s₀.re) (hz : riemannZeta s₀ = 0) :
    (2 * s₀.re - 1) / Complex.normSq s₀ ≤
      ∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)‖ ^ 2 := by
  let R : ℝ → ℂ := fun x => 1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (starRingEnd ℂ s₀ - 1)
  have hs_ne : s₀ ≠ 0 := fun h0 => by rw [h0] at hs; norm_num at hs
  have h2re : 0 < 2 * s₀.re - 1 := by linarith
  have h_inner : ∫ x in Ioc (0 : ℝ) 1, R x * starRingEnd ℂ (g x) = 1 / s₀ := by
    have h_ae : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        R x * starRingEnd ℂ (g x) = R x * (x : ℂ) ^ (s₀ - 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
      dsimp [g]
      rw [Complex.cpow_def_of_ne_zero hx_ne, Complex.cpow_def_of_ne_zero hx_ne,
        ← Complex.exp_conj, map_mul, map_sub, map_one, RingHomCompTriple.comp_apply,
        RingHom.id_apply, ← Complex.ofReal_log hx.1.le, Complex.conj_ofReal]
    have h_term : ∀ k ∈ Finset.Icc 1 N, IntegrableOn
        (fun x : ℝ => c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s₀ - 1))) (Ioc (0 : ℝ) 1) :=
      fun k hk =>
        (integrableOn_Ioc_recipFractScaled_cpow k (Finset.mem_Icc.mp hk).1 s₀ hs).const_mul _
    have h_sum_eq : (fun x : ℝ => R x * (x : ℂ) ^ (s₀ - 1)) = fun x : ℝ => (x : ℂ) ^ (s₀ - 1) -
        ∑ k ∈ Finset.Icc 1 N, c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s₀ - 1)) := by
      ext x
      dsimp [R]
      rw [sub_mul, one_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    have h_sum_int : IntegrableOn (fun x : ℝ => ∑ k ∈ Finset.Icc 1 N,
        c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s₀ - 1))) (Ioc (0 : ℝ) 1) := by
      classical
      exact integrable_finsetSum _ fun k hk => h_term k hk
    rw [integral_congr_ae h_ae, h_sum_eq, integral_sub (integrableOn_Ioc_cpow s₀ hs.1) h_sum_int,
      integral_finsetSum _ fun k hk => h_term k hk]
    have h_one : ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s₀ - 1) = 1 / s₀ := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_cpow (Or.inl (by simp [Complex.sub_re]; linarith [hs.1]))]
      have hs1 : s₀ - 1 + 1 = s₀ := by ring
      rw [hs1, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hs_ne,
        sub_zero]
    have h_sub_ne : s₀ - 1 ≠ 0 := sub_ne_zero.mpr fun h1 => by rw [h1] at hs; norm_num at hs
    have h_rho : ∑ k ∈ Finset.Icc 1 N, ∫ x in Ioc (0 : ℝ) 1,
        c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s₀ - 1)) = 0 := by
      calc ∑ k ∈ Finset.Icc 1 N, ∫ x in Ioc (0 : ℝ) 1,
            c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s₀ - 1))
          = ∑ k ∈ Finset.Icc 1 N, (c k / (k : ℂ)) / (s₀ - 1) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
            have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            rw [integral_const_mul,
              integral_Ioc_recipFractScaled_cpow k hk_pos s₀ hs, hz, zero_div, sub_zero]
            field_simp [hk_ne, h_sub_ne]
        _ = (∑ k ∈ Finset.Icc 1 N, c k / (k : ℂ)) / (s₀ - 1) := (Finset.sum_div _ _ _).symm
        _ = 0 := by rw [hc, zero_div]
    rw [h_one, h_rho, sub_zero]
  have h_gnorm : ∫ x in Ioc (0 : ℝ) 1, ‖g x‖ ^ 2 = 1 / (2 * s₀.re - 1) := by
    have h_ae : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), ‖g x‖ ^ 2 = x ^ (2 * s₀.re - 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      dsimp [g]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.conj_re,
        Complex.one_re, ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
      congr 1
      ring
    rw [integral_congr_ae h_ae, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * s₀.re - 2))]
    rw [show 2 * s₀.re - 2 + 1 = 2 * s₀.re - 1 from by ring, Real.one_rpow,
      Real.zero_rpow h2re.ne', sub_zero]
  have hg_cont : ContinuousOn g (Ioc (0 : ℝ) 1) := fun x hx =>
    (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
      (Or.inl (by simp [hx.1]))).continuousWithinAt
  have hint_g2 : IntegrableOn (fun x : ℝ => ‖g x‖ ^ 2) (Ioc (0 : ℝ) 1) := by
    have hrpow : IntegrableOn (fun x : ℝ => x ^ (2 * s₀.re - 2)) (Ioc (0 : ℝ) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 2 * s₀.re - 2)
    refine hrpow.mono' ((hg_cont.norm.pow 2).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    dsimp [g]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.conj_re,
      Complex.one_re, ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    exact le_of_eq (by congr 1; ring)
  have hint_Rg : IntegrableOn (fun x : ℝ => R x * starRingEnd ℂ (g x)) (Ioc (0 : ℝ) 1) := by
    have ⟨hmeas, hbd⟩ := residual_measurable_and_norm_le N c
    have hi : IntegrableOn (fun x : ℝ => (1 + ∑ k ∈ Finset.Icc 1 N, ‖c k‖) * x ^ (s₀.re - 1))
        (Ioc (0 : ℝ) 1) := by
      have h0 : IntegrableOn (fun x : ℝ => x ^ (s₀.re - 1)) (Ioc (0 : ℝ) 1) := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact intervalIntegral.intervalIntegrable_rpow' (by linarith [hs.1] : (-1 : ℝ) < s₀.re - 1)
      exact h0.const_mul _
    refine hi.mono' (hmeas.aestronglyMeasurable.restrict.mul
      ((Complex.continuous_conj.comp_continuousOn hg_cont).aestronglyMeasurable
        measurableSet_Ioc)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [norm_mul, Complex.norm_conj]
    dsimp [g]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.conj_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (hbd x) (Real.rpow_nonneg hx.1.le _)
  have h_lb := sq_sub_norm_lower_bound R g (((2 * s₀.re - 1 : ℝ) : ℂ) / s₀) (1 / s₀)
    (1 / (2 * s₀.re - 1)) (one_div_pos.mpr h2re) (integrableOn_Ioc_residual_sq N c)
    hint_g2 hint_Rg h_inner h_gnorm
    (by rw [Complex.ofReal_div, Complex.ofReal_one, div_div_eq_mul_div, div_one]; ring)
  have h_lhs : Complex.normSq (1 / s₀) / (1 / (2 * s₀.re - 1)) =
      (2 * s₀.re - 1) / Complex.normSq s₀ := by
    rw [one_div, map_inv₀, one_div, div_inv_eq_mul, mul_comm, ← div_eq_mul_inv]
  rw [h_lhs] at h_lb
  exact h_lb

/-- Unconstrained spatial `L²(0, 1)` Cauchy–Schwarz lower bound (Báez-Duarte, 2003):
for any off-line critical-strip zero `s₀` with `1 / 2 < s₀.re < 1`, there exists `δ > 0`
such that `δ ≤ ∫ x in Ioo 0 1, ‖1 - ∑ k ∈ Finset.Icc 1 N, c k * {1 / (k * x)}‖ ^ 2`
for all `N` and unconstrained coefficients `c : ℕ → ℂ`. -/
theorem baezDuarte_unconstrained_spatial_floor (s₀ : ℂ) (hs : 0 < s₀.re ∧ s₀.re < 1)
    (hre : 1 / 2 < s₀.re) (hz : riemannZeta s₀ = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (c : ℕ → ℂ),
      δ ≤ ∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)‖ ^ 2 := by
  have hs_ne : s₀ ≠ 0 := fun h0 => by rw [h0] at hs; norm_num at hs
  have hs_ne_one : s₀ ≠ 1 := fun h1 => by rw [h1] at hs; norm_num at hs
  have hcs : 0 < (starRingEnd ℂ s₀).re ∧ (starRingEnd ℂ s₀).re < 1 := by simpa using hs
  have hz_conj : riemannZeta (starRingEnd ℂ s₀) = 0 := by
    rw [riemannZeta_conj_of_pos_re s₀ hs.1 hs_ne_one, hz, map_zero]
  have him : s₀.im ≠ 0 := im_ne_zero_of_inCriticalStrip_zeta_zero s₀ hs hz
  let h : ℝ → ℂ := fun x =>
    (starRingEnd ℂ s₀ - 1) * (x : ℂ) ^ (starRingEnd ℂ s₀ - 1) - (s₀ - 1) * (x : ℂ) ^ (s₀ - 1)
  let α₀ : ℂ := 1 / starRingEnd ℂ s₀ - 1 / s₀
  have hcs_ne : starRingEnd ℂ s₀ ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hs_ne
  have hα₀_ne : α₀ ≠ 0 := by
    intro h0
    have h_eq : s₀ = starRingEnd ℂ s₀ := by
      have h1 : 1 / starRingEnd ℂ s₀ = 1 / s₀ := sub_eq_zero.mp h0
      field_simp [hs_ne, hcs_ne] at h1
      exact h1
    have him_eq := congr_arg Complex.im h_eq
    simp at him_eq
    exact him (by linarith)
  have h_conj_ae : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), starRingEnd ℂ (h x) =
      (s₀ - 1) * (x : ℂ) ^ (s₀ - 1) -
        (starRingEnd ℂ s₀ - 1) * (x : ℂ) ^ (starRingEnd ℂ s₀ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
    have hcpow_conj : ∀ w : ℂ, starRingEnd ℂ ((x : ℂ) ^ w) = (x : ℂ) ^ (starRingEnd ℂ w) :=
      fun w => by
        rw [Complex.cpow_def_of_ne_zero hx_ne, Complex.cpow_def_of_ne_zero hx_ne,
          ← Complex.exp_conj, map_mul, ← Complex.ofReal_log hx.1.le, Complex.conj_ofReal]
    dsimp [h]
    simp only [map_sub, map_mul, map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [hcpow_conj (starRingEnd ℂ s₀ - 1), hcpow_conj (s₀ - 1)]
    simp only [map_sub, map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]
  have hint_h_conj : IntegrableOn (fun x : ℝ => starRingEnd ℂ (h x)) (Ioc (0 : ℝ) 1) :=
    (((integrableOn_Ioc_cpow s₀ hs.1).const_mul (s₀ - 1)).sub
      ((integrableOn_Ioc_cpow (starRingEnd ℂ s₀) hcs.1).const_mul
        (starRingEnd ℂ s₀ - 1))).congr (h_conj_ae.mono fun _ hx => hx.symm)
  have h_one_inner : ∫ x in Ioc (0 : ℝ) 1, starRingEnd ℂ (h x) = α₀ := by
    have hint_val : ∀ w : ℂ, 0 < w.re → ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (w - 1) = 1 / w :=
      fun w hw => by
        have hw_ne : w ≠ 0 := fun h0 => by rw [h0] at hw; simp at hw
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          integral_cpow (Or.inl (by simp [Complex.sub_re]; linarith))]
        rw [show w - 1 + 1 = w from by ring, Complex.ofReal_one, Complex.one_cpow,
          Complex.ofReal_zero, Complex.zero_cpow hw_ne, sub_zero]
    rw [integral_congr_ae h_conj_ae,
      integral_sub ((integrableOn_Ioc_cpow s₀ hs.1).const_mul _)
        ((integrableOn_Ioc_cpow (starRingEnd ℂ s₀) hcs.1).const_mul _),
      integral_const_mul, integral_const_mul, hint_val s₀ hs.1, hint_val _ hcs.1]
    dsimp [α₀]
    field_simp [hs_ne, hcs_ne]
    ring
  have h_cont_h : ContinuousOn h (Ioc (0 : ℝ) 1) := ContinuousOn.sub
    (continuousOn_const.mul fun x hx => (Complex.continuous_ofReal.continuousAt.cpow
      continuousAt_const (Or.inl (by simp [hx.1]))).continuousWithinAt)
    (continuousOn_const.mul fun x hx => (Complex.continuous_ofReal.continuousAt.cpow
      continuousAt_const (Or.inl (by simp [hx.1]))).continuousWithinAt)
  have hint_h2 : IntegrableOn (fun x : ℝ => ‖h x‖ ^ 2) (Ioc (0 : ℝ) 1) := by
    let C : ℝ := ‖starRingEnd ℂ s₀ - 1‖ + ‖s₀ - 1‖
    have h_rpow : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (2 * s₀.re - 2)) (Ioc (0 : ℝ) 1) := by
      have hi : IntegrableOn (fun x : ℝ => x ^ (2 * s₀.re - 2)) (Ioc (0 : ℝ) 1) := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 2 * s₀.re - 2)
      exact hi.const_mul (C ^ 2)
    refine h_rpow.mono' ((h_cont_h.norm.pow 2).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h_le : ‖h x‖ ≤ C * x ^ (s₀.re - 1) := by
      dsimp [h, C]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
        Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      simp only [Complex.sub_re, Complex.conj_re, Complex.one_re]
      exact le_of_eq (by ring)
    calc ‖h x‖ ^ 2 ≤ (C * x ^ (s₀.re - 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h_le 2
      _ = C ^ 2 * (x ^ (s₀.re - 1)) ^ 2 := by ring
      _ = C ^ 2 * x ^ (2 * s₀.re - 2) := by
        congr 1; rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]; congr 1; ring
  let H₀ : ℝ := ∫ x in Ioc (0 : ℝ) 1, ‖h x‖ ^ 2
  have hH₀_pos : 0 < H₀ := by
    refine lt_of_le_of_ne (setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _) ?_
    intro h0
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun _ => sq_nonneg _) hint_h2).mp h0.symm
    have hα0 : α₀ = 0 := by
      rw [← h_one_inner]
      refine integral_eq_zero_of_ae (hae0.mono fun x hx => ?_)
      dsimp only [Pi.zero_apply] at hx ⊢
      rw [norm_eq_zero.mp (sq_eq_zero_iff.mp hx), map_zero]
    exact hα₀_ne hα0
  refine ⟨Complex.normSq α₀ / H₀, div_pos (Complex.normSq_pos.mpr hα₀_ne) hH₀_pos, fun N c => ?_⟩
  let R : ℝ → ℂ := fun x => 1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)
  have h_rho_orth : ∀ k : ℕ, 1 ≤ k →
      ∫ x in Ioc (0 : ℝ) 1, (recipFractScaled k x : ℂ) * starRingEnd ℂ (h x) = 0 := fun k hk => by
    have h_ae : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        (recipFractScaled k x : ℂ) * starRingEnd ℂ (h x) =
          (s₀ - 1) * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s₀ - 1)) -
          (starRingEnd ℂ s₀ - 1) * ((recipFractScaled k x : ℂ) *
            (x : ℂ) ^ (starRingEnd ℂ s₀ - 1)) := by
      filter_upwards [h_conj_ae] with x hx
      rw [hx]
      ring
    have hz_term : ∀ w : ℂ, 0 < w.re ∧ w.re < 1 → riemannZeta w = 0 →
        (w - 1) * ∫ x in Ioc (0 : ℝ) 1, (recipFractScaled k x : ℂ) * (x : ℂ) ^ (w - 1) =
          1 / (k : ℂ) := fun w hw hzw => by
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr fun h1 => by rw [h1] at hw; norm_num at hw
      rw [integral_Ioc_recipFractScaled_cpow k hk w hw, hzw, zero_div, sub_zero]
      field_simp [Nat.cast_ne_zero.mpr (by omega : k ≠ 0), hw1]
    rw [integral_congr_ae h_ae,
      integral_sub ((integrableOn_Ioc_recipFractScaled_cpow k hk s₀ hs).const_mul _)
        ((integrableOn_Ioc_recipFractScaled_cpow k hk _ hcs).const_mul _),
      integral_const_mul, integral_const_mul, hz_term s₀ hs hz, hz_term _ hcs hz_conj, sub_self]
  have ⟨hR_meas, hR_bd⟩ := residual_measurable_and_norm_le N c
  let M : ℝ := 1 + ∑ k ∈ Finset.Icc 1 N, ‖c k‖
  have hint_Rh : IntegrableOn (fun x : ℝ => R x * starRingEnd ℂ (h x)) (Ioc (0 : ℝ) 1) := by
    refine (hint_h_conj.norm.const_mul M).mono'
      (hR_meas.aestronglyMeasurable.restrict.mul
        ((Complex.continuous_conj.comp_continuousOn h_cont_h).aestronglyMeasurable
          measurableSet_Ioc)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hR_bd x) (norm_nonneg _)
  have hint_term : ∀ k : ℕ, IntegrableOn
      (fun x : ℝ => c k * ((recipFractScaled k x : ℂ) * starRingEnd ℂ (h x))) (Ioc (0 : ℝ) 1) := by
    intro k
    refine (hint_h_conj.norm.const_mul ‖c k‖).mono'
      (((measurable_recipFractScaled k).complex_ofReal.aestronglyMeasurable.restrict.mul
        ((Complex.continuous_conj.comp_continuousOn h_cont_h).aestronglyMeasurable
          measurableSet_Ioc)).const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x _
    rw [norm_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (norm_recipFractScaled_le_one k x)
      (norm_nonneg _)) (norm_nonneg _)).trans (by simp [one_mul])
  have h_R_inner : ∫ x in Ioc (0 : ℝ) 1, R x * starRingEnd ℂ (h x) = α₀ := by
    have h_eq : (fun x : ℝ => R x * starRingEnd ℂ (h x)) = fun x : ℝ => starRingEnd ℂ (h x) -
        ∑ k ∈ Finset.Icc 1 N, c k * ((recipFractScaled k x : ℂ) * starRingEnd ℂ (h x)) := by
      ext x
      dsimp [R]
      rw [sub_mul, one_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    have hint_sum : IntegrableOn (fun x : ℝ => ∑ k ∈ Finset.Icc 1 N,
        c k * ((recipFractScaled k x : ℂ) * starRingEnd ℂ (h x))) (Ioc (0 : ℝ) 1) := by
      classical
      exact integrable_finsetSum _ fun k _ => hint_term k
    rw [h_eq, integral_sub hint_h_conj hint_sum, h_one_inner,
      integral_finsetSum _ fun k _ => hint_term k]
    have hsum0 : ∑ k ∈ Finset.Icc 1 N, ∫ x in Ioc (0 : ℝ) 1,
        c k * ((recipFractScaled k x : ℂ) * starRingEnd ℂ (h x)) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [integral_const_mul, h_rho_orth k (Finset.mem_Icc.mp hk).1, mul_zero]
    rw [hsum0, sub_zero]
  exact sq_sub_norm_lower_bound R h (α₀ / (H₀ : ℂ)) α₀ H₀ hH₀_pos
    (integrableOn_Ioc_residual_sq N c) hint_h2 hint_Rh h_R_inner rfl rfl

lemma riemannZeta_zero_strip_symm {s : ℂ} (hz : riemannZeta s = 0)
    (h_not_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h_not_one : s ≠ 1) :
    (0 < s.re ∧ s.re < 1) ∧ (riemannZeta (1 - s) = 0 ∧ 0 < (1 - s).re ∧ (1 - s).re < 1) := by
  have hs_lt_one : s.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hge) hz
  have hs_not_neg_nat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    subst hn
    rcases n with _ | n
    · simp [riemannZeta_zero] at hz
    · rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
      · refine h_not_triv ⟨m - 1, ?_⟩
        have h1 : n + 1 = 2 * ((m - 1) + 1) := by omega
        push_cast [h1]
        ring
      · let w : ℂ := ((2 * m + 2 : ℕ) : ℂ)
        have hw_not_neg : ∀ j : ℕ, w ≠ -(j : ℂ) := fun j h_eq => by
          have := congr_arg Complex.re h_eq
          simp [w] at this
          linarith
        have hw_ne_one : w ≠ 1 := fun h_eq => by
          have := congr_arg Complex.re h_eq
          simp [w] at this
          linarith
        have h_fe := riemannZeta_one_sub hw_not_neg hw_ne_one
        rw [show 1 - w = -(↑(n + 1) : ℂ) from by dsimp [w]; push_cast [hm]; ring, hz] at h_fe
        have h_cpow_ne : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
          (Or.inl (by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero))
        have h_cos_ne : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
          intro hcos
          rw [Complex.cos_eq_zero_iff] at hcos
          rcases hcos with ⟨k, hk⟩
          have hw2 : (Real.pi : ℂ) * w / 2 =
              ((((m + 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) := by dsimp [w]; push_cast; ring
          have hk2 : (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 =
              ((((2 * k + 1 : ℤ) / 2 : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; ring
          rw [hw2, hk2] at hk
          have hdiv : ((m + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℤ) / 2 : ℝ) :=
            mul_right_cancel₀ Real.pi_ne_zero (Complex.ofReal_injective hk)
          have hint : (2 * ((m : ℤ) + 1)) = 2 * k + 1 := by exact_mod_cast (by linarith :
            (2 : ℝ) * ((m + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ))
          omega
        have h_zeta_ne : riemannZeta w ≠ 0 :=
          riemannZeta_ne_zero_of_one_le_re (by dsimp [w]; norm_cast; omega)
        exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h_cpow_ne)
          (Complex.Gamma_ne_zero hw_not_neg)) h_cos_ne) h_zeta_ne) h_fe.symm
  have hz_refl : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_one_sub hs_not_neg_nat h_not_one, hz, mul_zero]
  have hs_pos : 0 < s.re := by
    by_contra hle
    exact riemannZeta_ne_zero_of_one_le_re
      (by rw [Complex.sub_re, Complex.one_re]; linarith [le_of_not_gt hle]) hz_refl
  exact ⟨⟨hs_pos, hs_lt_one⟩, hz_refl,
    by rw [Complex.sub_re, Complex.one_re]; linarith,
    by rw [Complex.sub_re, Complex.one_re]; linarith⟩

/-- **Nyman (1950) / Beurling (1955) Forward Theorem:** If `1` lies in the `L²(0, 1)` closure
of constrained dilations `∑ k ∈ Finset.Icc 1 N, c k * {1 / (k * x)}` (`∑ c k / k = 0`),
then `RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_nymanBeurling_approx
    (h_nb : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℂ),
      (∑ k ∈ Finset.Icc 1 N, c k / (k : ℂ) = 0) ∧
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)‖ ^ 2) < ε) :
    RiemannHypothesis := by
  intro s₀ hz h_not_triv h_not_one
  rcases riemannZeta_zero_strip_symm hz h_not_triv h_not_one with ⟨hs, hz_refl, hs_refl⟩
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with hlt | hgt
  · have hre_refl : 1 / 2 < (1 - s₀).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hs1_ne : 1 - s₀ ≠ 0 := fun h0 => by rw [h0] at hs_refl; simp at hs_refl
    have hδ : 0 < (2 * (1 - s₀).re - 1) / Complex.normSq (1 - s₀) :=
      div_pos (by linarith) (Complex.normSq_pos.mpr hs1_ne)
    rcases h_nb _ hδ with ⟨N, c, hc, hlt_eps⟩
    linarith [nymanBeurling_spatial_cauchy_floor N c hc (1 - s₀) hs_refl hre_refl hz_refl]
  · have hs_ne : s₀ ≠ 0 := fun h0 => by rw [h0] at hs; simp at hs
    have hδ : 0 < (2 * s₀.re - 1) / Complex.normSq s₀ :=
      div_pos (by linarith) (Complex.normSq_pos.mpr hs_ne)
    rcases h_nb _ hδ with ⟨N, c, hc, hlt_eps⟩
    linarith [nymanBeurling_spatial_cauchy_floor N c hc s₀ hs hgt hz]

/-- **Báez-Duarte (2003) Unconstrained Forward Theorem:** If `1` lies in the `L²(0, 1)` closure
of unconstrained dilations `∑ k ∈ Finset.Icc 1 N, c k * {1 / (k * x)}`, then
`RiemannHypothesis` holds. -/
theorem RiemannHypothesis.of_baezDuarte_approx
    (h_bd : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℂ),
      (∫ x in Set.Ioo (0 : ℝ) 1,
        ‖1 - ∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)‖ ^ 2) < ε) :
    RiemannHypothesis := by
  intro s₀ hz h_not_triv h_not_one
  rcases riemannZeta_zero_strip_symm hz h_not_triv h_not_one with ⟨hs, hz_refl, hs_refl⟩
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with hlt | hgt
  · have hre_refl : 1 / 2 < (1 - s₀).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    rcases baezDuarte_unconstrained_spatial_floor (1 - s₀) hs_refl hre_refl hz_refl with
      ⟨δ, hδ, hfloor⟩
    rcases h_bd δ hδ with ⟨N, c, hlt_eps⟩
    linarith [hfloor N c]
  · rcases baezDuarte_unconstrained_spatial_floor s₀ hs hgt hz with ⟨δ, hδ, hfloor⟩
    rcases h_bd δ hδ with ⟨N, c, hlt_eps⟩
    linarith [hfloor N c]

/-- Subtracting the `k = 2` sawtooth dilation `{1 / (2 * x)}` from `{1 / x}` multiplies the
Mellin transform by the `p = 2` Euler factor `(1 - 2 ^ (-s))`, removing all even harmonics
and leaving the `1 / (2 * (s - 1))` pole from the odd-integer Dirichlet series. -/
theorem mellin_eulerTwoPair_unit_interval {s : ℂ} (hs_lo : 0 < s.re) (hs_hi : s.re < 1) :
    (∫ x : ℝ in Set.Ioo 0 1,
      ((recipFractScaled 1 x : ℂ) - (recipFractScaled 2 x : ℂ)) * (x : ℂ) ^ (s - 1)) =
    1 / (2 * (s - 1)) - (riemannZeta s / s) * (1 - (2 : ℂ) ^ (-s)) := by
  have hs : 0 < s.re ∧ s.re < 1 := ⟨hs_lo, hs_hi⟩
  have h1 := integrableOn_Ioc_recipFractScaled_cpow 1 (by norm_num) s hs
  have h2 := integrableOn_Ioc_recipFractScaled_cpow 2 (by norm_num) s hs
  have hIoo : (∫ x : ℝ in Set.Ioo 0 1,
      ((recipFractScaled 1 x : ℂ) - (recipFractScaled 2 x : ℂ)) * (x : ℂ) ^ (s - 1)) =
      ∫ x : ℝ in Ioc 0 1,
        ((recipFractScaled 1 x : ℂ) * (x : ℂ) ^ (s - 1) -
          (recipFractScaled 2 x : ℂ) * (x : ℂ) ^ (s - 1)) := by
    rw [MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    ring
  rw [hIoo, MeasureTheory.integral_sub h1 h2,
    integral_Ioc_recipFractScaled_cpow 1 (by norm_num) s hs,
    integral_Ioc_recipFractScaled_cpow 2 (by norm_num) s hs]
  have hs0 : s ≠ 0 := fun h0 => by rw [h0] at hs_lo; simp at hs_lo
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h1 => by rw [h1] at hs_hi; simp at hs_hi)
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have h2s_ne : (2 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h2_ne)
  simp only [Nat.cast_one, Nat.cast_ofNat, Complex.one_cpow]
  rw [Complex.cpow_neg (2 : ℂ) s]
  field_simp
  ring

/-- The minimal Nyman dipole `{1 / x} - 2 * {1 / (2 * x)}` satisfies the Nyman pole-cancellation
constraint `1 / 1 - 2 / 2 = 0` and has Mellin transform `-(riemannZeta s / s) * (1 - 2 ^ (1 - s))`,
where the factor `1 - 2 ^ (1 - s)` vanishes at `s = 1` to neutralize the pole of `riemannZeta`. -/
theorem mellin_nymanDipole_unit_interval {s : ℂ} (hs_lo : 0 < s.re) (hs_hi : s.re < 1) :
    (∫ x : ℝ in Set.Ioo 0 1,
      ((recipFractScaled 1 x : ℂ) - 2 * (recipFractScaled 2 x : ℂ)) * (x : ℂ) ^ (s - 1)) =
    -(riemannZeta s / s) * (1 - (2 : ℂ) ^ (1 - s)) := by
  have hs : 0 < s.re ∧ s.re < 1 := ⟨hs_lo, hs_hi⟩
  have h1 := integrableOn_Ioc_recipFractScaled_cpow 1 (by norm_num) s hs
  have h2 := (integrableOn_Ioc_recipFractScaled_cpow 2 (by norm_num) s hs).const_mul (2 : ℂ)
  have hIoo : (∫ x : ℝ in Set.Ioo 0 1,
      ((recipFractScaled 1 x : ℂ) - 2 * (recipFractScaled 2 x : ℂ)) * (x : ℂ) ^ (s - 1)) =
      ∫ x : ℝ in Ioc 0 1,
        ((recipFractScaled 1 x : ℂ) * (x : ℂ) ^ (s - 1) -
          (2 : ℂ) * ((recipFractScaled 2 x : ℂ) * (x : ℂ) ^ (s - 1))) := by
    rw [MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    ring
  rw [hIoo, MeasureTheory.integral_sub h1 h2, MeasureTheory.integral_const_mul,
    integral_Ioc_recipFractScaled_cpow 1 (by norm_num) s hs,
    integral_Ioc_recipFractScaled_cpow 2 (by norm_num) s hs]
  have hs0 : s ≠ 0 := fun h0 => by rw [h0] at hs_lo; simp at hs_lo
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h1 => by rw [h1] at hs_hi; simp at hs_hi)
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have h2s_ne : (2 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h2_ne)
  simp only [Nat.cast_one, Nat.cast_ofNat, Complex.one_cpow]
  rw [Complex.cpow_sub _ _ h2_ne, Complex.cpow_one]
  field_simp
  ring

/-- At scale `N = 2`, no non-zero pair `(c₁, c₂)` can simultaneously annihilate the
even spatial jump (`c₁ + c₂ = 0`) and the `s = 1` pole residue (`c₁ + c₂ / 2 = 0`). -/
theorem two_var_jump_and_pole_eq_zero {c₁ c₂ : ℂ}
    (h_jump : c₁ + c₂ = 0) (h_pole : c₁ + c₂ / 2 = 0) :
    c₁ = 0 ∧ c₂ = 0 := by
  constructor
  · linear_combination -h_jump + 2 * h_pole
  · linear_combination 2 * h_jump - 2 * h_pole

/-- Recruiting `k = 3` with `(c₁, c₂, c₃) = (1, -1, -3/2)` preserves even-jump cancellation
(`c₁ + c₂ = 0`) while transferring the residual `1 / (2 * (s - 1))` pole of `{1/x} - {1/(2x)}`
onto `{1/(3x)}`, yielding a pole-free Mellin transform
`-(riemannZeta s / s) * (1 - 2^(-s) - (3/2) * 3^(-s))` whose Dirichlet factor vanishes
at `s = 1`. -/
theorem mellin_nymanTripole_unit_interval {s : ℂ} (hs_lo : 0 < s.re) (hs_hi : s.re < 1) :
    (∫ x : ℝ in Set.Ioo 0 1,
      ((recipFractScaled 1 x : ℂ) - (recipFractScaled 2 x : ℂ) -
        (3 / 2 : ℂ) * (recipFractScaled 3 x : ℂ)) * (x : ℂ) ^ (s - 1)) =
    -(riemannZeta s / s) * (1 - (2 : ℂ) ^ (-s) - (3 / 2 : ℂ) * (3 : ℂ) ^ (-s)) := by
  have hs : 0 < s.re ∧ s.re < 1 := ⟨hs_lo, hs_hi⟩
  have h1 := integrableOn_Ioc_recipFractScaled_cpow 1 (by norm_num) s hs
  have h2 := integrableOn_Ioc_recipFractScaled_cpow 2 (by norm_num) s hs
  have h3 := (integrableOn_Ioc_recipFractScaled_cpow 3 (by norm_num) s hs).const_mul (3 / 2 : ℂ)
  have h12 : IntegrableOn (fun x : ℝ =>
      (recipFractScaled 1 x : ℂ) * (x : ℂ) ^ (s - 1) -
        (recipFractScaled 2 x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioc 0 1) := h1.sub h2
  have hIoo : (∫ x : ℝ in Set.Ioo 0 1,
      ((recipFractScaled 1 x : ℂ) - (recipFractScaled 2 x : ℂ) -
        (3 / 2 : ℂ) * (recipFractScaled 3 x : ℂ)) * (x : ℂ) ^ (s - 1)) =
      ∫ x : ℝ in Ioc 0 1,
        (((recipFractScaled 1 x : ℂ) * (x : ℂ) ^ (s - 1) -
          (recipFractScaled 2 x : ℂ) * (x : ℂ) ^ (s - 1)) -
          (3 / 2 : ℂ) * ((recipFractScaled 3 x : ℂ) * (x : ℂ) ^ (s - 1))) := by
    rw [MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    ring
  rw [hIoo, MeasureTheory.integral_sub h12 h3, MeasureTheory.integral_sub h1 h2,
    MeasureTheory.integral_const_mul,
    integral_Ioc_recipFractScaled_cpow 1 (by norm_num) s hs,
    integral_Ioc_recipFractScaled_cpow 2 (by norm_num) s hs,
    integral_Ioc_recipFractScaled_cpow 3 (by norm_num) s hs]
  have hs0 : s ≠ 0 := fun h0 => by rw [h0] at hs_lo; simp at hs_lo
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h1 => by rw [h1] at hs_hi; simp at hs_hi)
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have h3_ne : (3 : ℂ) ≠ 0 := by norm_num
  have h2s_ne : (2 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h2_ne)
  have h3s_ne : (3 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h3_ne)
  simp only [Nat.cast_one, Nat.cast_ofNat, Complex.one_cpow]
  rw [Complex.cpow_neg (2 : ℂ) s, Complex.cpow_neg (3 : ℂ) s]
  field_simp
  ring
