/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferetiationThm
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Fundamental Theorem of Calculus and Integration by Parts for Absolutely Continuous Functions

This file proves that:
* If `f` is absolutely continuous on `uIcc a b`, then `f` is a.e. differentiable on `uIcc a b`,
`f'` is interval integrable on `a..b`, and that *Fundamental Theorem of Calculus* holds for `f'` on
`a..b`, i.e. `∫ (x : ℝ) in a..b, deriv f x = f b - f a`.
* *Integration by Parts* holds for absolutely continuous functions.

## Implementation notes

We need to prove that `f'` is interval integrable on `a..b` for any monotone function `f`. The
proof uses Fatou's lemma. From this we get `f'` is interval integrable on `a..b` for BV functions
and finally for absolutely continuous functions.

## Tags
absolutely continuous, fundamental theorem of calculus, integration by parts
-/

open MeasureTheory Set Filter Function

open scoped Topology ENNReal Interval NNReal

/-- If `f z` tends to `y` as `z` tends to `x`, then `f (x + (n : ℝ)⁻¹)` tends to `y` as `n` tends
to infinity. -/
theorem Filter.Tendsto.inverse_atTop {f : ℝ → ℝ} {x y : ℝ}
    (h : Filter.Tendsto f (𝓝[≠] x) (𝓝 y)) :
    Filter.Tendsto (fun n : ℕ ↦ f (x + (n : ℝ)⁻¹)) Filter.atTop (𝓝 y) := by
  apply Filter.Tendsto.comp h
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · nth_rw 2 [show x = x + 0 by simp]
    apply tendsto_const_nhds.add
    exact tendsto_inverse_atTop_nhds_zero_nat
  · have : ∀ᶠ (n : ℕ) in atTop, n ≠ 0 := by
      simp only [Filter.Eventually, mem_atTop_sets, mem_setOf_eq]
      use 1; intro n hn; omega
    filter_upwards [this] with n hn
    simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, inv_eq_zero]
    norm_cast

/-- If `f` is monotone on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem MonotoneOn.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ} (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  wlog hab : a ≤ b
  · have S : uIcc a b = uIcc b a := by exact uIcc_comm a b
    exact @this f b a (S ▸ hf) (by linarith) |>.symm
  simp_rw [uIcc, show min a b = a by simp [hab], show max a b = b by simp [hab] ] at hf
  let g (x : ℝ) : ℝ := if x <= a then f a else if x < b then f x else f b
  have hg : Monotone g := by
    intro x y hxy
    dsimp only [g]
    split_ifs <;> try linarith
    all_goals apply hf
    all_goals try rw [mem_Icc]
    all_goals try constructor
    all_goals try linarith
  have hgc (c : ℝ) : Monotone (fun x ↦ g (x + c)) := by
    intro x y hxy; beta_reduce; apply hg; linarith
  have h1 : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  have hg1 := hg.ae_differentiableAt
  have hg2 : ∀ᵐ (x : ℝ), HasDerivAt g (deriv g x) x ∧ 0 ≤ deriv g x := by
    filter_upwards [hg1, h1, h2] with x hx1 hx2 hx3
    exact ⟨hx1.hasDerivAt, hg.deriv_nonneg⟩
  have hfg : ∀ x ∈ Ioo a b, deriv f x = deriv g x := by
    intro x hx
    apply Filter.EventuallyEq.deriv_eq
    have : Ioo a b ∈ 𝓝 x := by
      rw [Metric.mem_nhds_iff]
      obtain ⟨ε, hε1, hε2⟩ := Metric.isOpen_iff.mp isOpen_Ioo x hx
      use ε, hε1
    filter_upwards [this] with y hy
    rw [mem_Ioo] at hy
    simp [g, hy]
  have hg3 (a0 b0 : ℝ) := hg.intervalIntegrable (μ := volume) (a := a0) (b := b0)
  have hg4 (z a0 b0 : ℝ) : IntervalIntegrable (fun x ↦ g (x + z)) volume a0 b0 := by
      convert hg3 (a0 + z) (b0 + z) |>.comp_add_right z <;> abel
  have hg5 (x : ℝ) (hx : b ≤ x) : g x = g b := by
    simp only [lt_self_iff_false, ↓reduceIte, g]
    split_ifs <;> (congr; try linarith)
  let G (c x : ℝ) := slope g x (x + c)
  have G_nonneg (c x : ℝ) (hc : 0 ≤ c) : 0 ≤ G c x := by
    have : g x ≤ g (x + c) := by apply hg; linarith
    have : 0 ≤ g (x + c) - g x := by linarith
    simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul, ge_iff_le, G]
    exact mul_nonneg (inv_nonneg.mpr hc) this
  have G_integrable (c : ℝ) : LocallyIntegrable (G c) volume := by
    simp only [G, slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
    exact (hgc c).locallyIntegrable.sub (hg.locallyIntegrable) |>.smul (c := c⁻¹)
  have G_measurable (n : ℕ) : AEMeasurable (G (n : ℝ)⁻¹) volume := by
    exact G_integrable (n : ℝ)⁻¹ |>.aestronglyMeasurable |>.aemeasurable
  have G_measurable_ab (n : ℕ) : AEMeasurable ((Ioc a b).indicator (G (n : ℝ)⁻¹)) volume := by
    apply (G_measurable n).indicator; simp
  have G_lim : ∀ᵐ (x : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ G (n : ℝ)⁻¹ x) Filter.atTop
      (nhds (deriv g x)) := by
    filter_upwards [hg2] with x ⟨hx1, hx2⟩
    rw [hasDerivAt_iff_tendsto_slope] at hx1
    dsimp [G]
    exact hx1.inverse_atTop
  have G_liminf' : ∀ᵐ (x : ℝ),
      Filter.liminf (fun (n : ℕ) ↦ ‖G (n : ℝ)⁻¹ x‖ₑ) Filter.atTop =
        ‖deriv g x‖ₑ:= by
    filter_upwards [G_lim] with x hx
    exact hx.enorm.liminf_eq
  have G_liminf'_ab : ∀ᵐ (x : ℝ),
      Filter.liminf (fun (n : ℕ) ↦ ‖(Ioc a b).indicator (G (n : ℝ)⁻¹) x‖ₑ) Filter.atTop =
      ‖((Ioc a b).indicator (deriv g)) x‖ₑ := by
    filter_upwards [G_liminf'] with x hx
    by_cases hx1 : x ∈ Ioc a b <;> simp only [hx1, Set.indicator, ↓reduceIte]
    · exact hx
    · simp
  have G_fatou := MeasureTheory.lintegral_liminf_le' (fun n ↦ ((G_measurable_ab n).enorm))
  have G_bound (n : ℕ) (hn : n ≥ 1) :
      n * (∫ (x : ℝ) in a..b, g (x + (n : ℝ)⁻¹) - g x) ≤ g b - g a := by
    calc
    _ = n * ((∫ (x : ℝ) in a..b, g (x + (↑n)⁻¹)) - ∫ (x : ℝ) in a..b, g x) := by
      rw [intervalIntegral.integral_sub]
      · exact hg4 _ _ _
      · exact hg3 _ _
    _ = n * ((∫ (x : ℝ) in (a + (↑n)⁻¹)..(b + (↑n)⁻¹), g x) - ∫ (x : ℝ) in a..b, g x) := by simp
    _ = n * ((∫ (x : ℝ) in b..(b + (↑n)⁻¹), g x) - ∫ (x : ℝ) in a..(a + (↑n)⁻¹), g x) := by
      rw [intervalIntegral.integral_interval_sub_interval_comm'] <;> exact hg3 _ _
    _ = n * ((∫ (x : ℝ) in b..(b + (↑n)⁻¹), g b) - ∫ (x : ℝ) in a..(a + (↑n)⁻¹), g x) := by
      congr 2
      apply intervalIntegral.integral_congr
      simp only [EqOn, le_add_iff_nonneg_right, inv_nonneg, Nat.cast_nonneg, uIcc_of_le, mem_Icc,
        and_imp]
      intro x hx1 _
      exact hg5 x hx1
    _ = n * ((↑n)⁻¹ * g b - ∫ (x : ℝ) in a..(a + (↑n)⁻¹), g x) := by simp
    _ ≤ n * ((↑n)⁻¹ * g b - ∫ (x : ℝ) in a..(a + (↑n)⁻¹), g a) := by
      gcongr
      apply intervalIntegral.integral_mono_on <;> try simp
      · exact hg3 _ _
      · intros; apply hg; assumption
    _ = n * ((↑n)⁻¹ * g b - (↑n)⁻¹ * g a) := by simp
    _ = g b - g a := by
      ring_nf
      rw [show (n : ℝ) * (n : ℝ)⁻¹ = 1 by refine mul_inv_cancel₀ ?_; norm_cast; omega]
      ring
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  constructor
  · suffices AEStronglyMeasurable (deriv g) (volume.restrict (Ioc a b)) by
      apply this.congr
      have h3 : ∀ᵐ x ∂(volume.restrict (Ioc a b)), x ∈ Ioc a b := by
        apply MeasureTheory.ae_restrict_mem; simp
      have h4 : ∀ᵐ x ∂(volume.restrict (Ioc a b)), x ≠ b := by
        rw [MeasureTheory.ae_restrict_iff']
        · filter_upwards [h2] with x hx1 hx2; exact hx1
        · simp
      filter_upwards [h3, h4] with x hx1 hx2
      symm; apply hfg
      rw [← Ioc_diff_right, mem_diff]
      simp [hx1, hx2]
    suffices AEStronglyMeasurable (deriv g) from this.restrict
    apply aestronglyMeasurable_of_tendsto_ae (lim := G_lim)
    intro n; exact (G_integrable (n : ℝ)⁻¹).aestronglyMeasurable
  · unfold HasFiniteIntegral
    calc ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ
    _ = ∫⁻ x, (Ioc a b).indicator (fun t ↦ ‖deriv f t‖ₑ) x := by simp
    _ = ∫⁻ x, (Ioc a b).indicator (fun t ↦ ‖deriv g t‖ₑ) x := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [h2] with x hxb
      by_cases hx : x ∈ Ioc a b <;> simp only [indicator, hx, ↓reduceIte]
      congr 1
      apply hfg
      rw [← Ioc_diff_right, mem_diff]
      simp [hx, hxb]
    _ = ∫⁻ x, ‖(Ioc a b).indicator (deriv g) x‖ₑ := by
      apply MeasureTheory.lintegral_congr
      intro x
      dsimp only [Set.indicator]
      by_cases hx : x ∈ Ioc a b <;> simp [hx]
    _ ≤ liminf (fun (n : ℕ) ↦ ∫⁻ (a_1 : ℝ), ‖(Ioc a b).indicator (G (n : ℝ)⁻¹) a_1‖ₑ) atTop :=
        by
      convert G_fatou using 1
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [G_liminf'_ab] with x hx
      rw [hx]
    _ = liminf (fun (n : ℕ) ↦ ENNReal.ofReal (∫ (a_1 : ℝ), (Ioc a b).indicator (G (n : ℝ)⁻¹) a_1))
        atTop := by
      apply Filter.liminf_congr
      filter_upwards with n
      rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm]
      · congr with y
        apply abs_eq_self.mpr
        dsimp only [Set.indicator]
        by_cases hy : y ∈ Ioc a b
        · simp only [hy, ↓reduceIte]
          apply G_nonneg; simp
        · simp only [hy, ↓reduceIte]; simp
      · have := (G_integrable (n : ℝ)⁻¹).integrableOn_isCompact (k := Icc a b)
            (hk := isCompact_Icc)
        have := this.indicator (t := Ioc a b) (ht := by simp)
        have := this.integrable_indicator (hs := by simp)
        convert this using 1
        ext x
        by_cases hx : x ∈ Ioc a b <;> simp only [indicator, hx, ↓reduceIte]
        · simp [Ioc_subset_Icc_self hx]
        · simp
    _ = liminf (fun (n : ℕ) ↦ ENNReal.ofReal (∫ a_1 in a..b, (G (n : ℝ)⁻¹) a_1)) atTop :=
        by
      apply Filter.liminf_congr
      filter_upwards with n
      congr 1
      rw [intervalIntegral.integral_of_le hab, integral_indicator]
      simp
    _ ≤ ENNReal.ofReal (g b - g a) :=
        by
      apply Filter.liminf_le_of_frequently_le'
      refine Filter.Eventually.frequently ?_
      simp only [Filter.Eventually, mem_atTop_sets, mem_setOf_eq]
      use 1
      intro n hn
      apply ENNReal.ofReal_le_ofReal
      simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul, inv_inv,
        intervalIntegral.integral_const_mul, G]
      exact G_bound n hn
    _ < ∞ := by
      exact ENNReal.ofReal_lt_top

/-- If `f` is absolute continuous on `uIcc a b`, then `f` is a.e. differentiable on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_differentiableWithinAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ Set.uIcc a b → DifferentiableWithinAt ℝ f (Set.uIcc a b) x := by
  exact hf.boundedVariationOn.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem

/-- If `f` differentiable at `x ∈ uIoo a b` within `uIcc a b`, then `f'` exists at `x`. -/
theorem DifferentiableWithinAt.hasDerivAt_interval {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DifferentiableWithinAt ℝ f (Set.uIcc a b) x) (hx : x ∈ Set.uIoo a b) :
    HasDerivAt f (deriv f x) x := by
  have : uIcc a b ∈ 𝓝 x := by
    rw [Metric.mem_nhds_iff]
    obtain ⟨ε, hε1, hε2⟩ := Metric.isOpen_iff.mp isOpen_Ioo x hx
    use ε, hε1
    trans uIoo a b; assumption; exact Ioo_subset_Icc_self
  have hx1 := hf.hasDerivWithinAt.hasDerivAt this
  rwa [hx1.deriv]

/-- If `f` is absolute continuous on `uIcc a b`, then `f` exists a.e. on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_hasDerivAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ Set.uIcc a b → HasDerivAt f (deriv f x) x := by
  have h1 : ∀ᵐ x, x ≠ min a b := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [hf.ae_differentiableWithinAt, h1, h2] with x hx1 hx2 hx3 hx4
  have : x ∈ uIoo a b := by
    rw [uIoo, ← Icc_diff_both, mem_diff, ← uIcc]; simp [hx2, hx3, hx4]
  exact (hx1 hx4).hasDerivAt_interval this

/-- If `f` has locally bounded variation on `uIcc a b`, then `f'` is interval integrable on
`a..b`. -/
theorem LocallyBoundedVariationOn.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ}
  (hf : LocallyBoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.exists_monotoneOn_sub_monotoneOn
  have h1 : ∀ᵐ x, x ≠ min a b := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  have hp1 := hp.deriv_intervalIntegrable
  have hq1 := hq.deriv_intervalIntegrable
  have hp2 := hp.ae_differentiableWithinAt_of_mem
  have hq2 := hq.ae_differentiableWithinAt_of_mem
  apply (hp1.sub hq1).congr
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff']
  · filter_upwards [hp2, hq2, h1, h2] with x hx1 hx2 hx3 hx4 hx5
    have hx6 : x ∈ uIcc a b := by rw [uIcc]; rw [uIoc] at hx5; exact Ioc_subset_Icc_self hx5
    have hx7 : x ∈ uIoo a b := by
      rw [uIoo, ← Icc_diff_both, mem_diff, ← uIcc]; simp [hx3, hx4, hx6]
    replace hx1 := (hx1 hx6).hasDerivAt_interval hx7
    replace hx2 := (hx2 hx6).hasDerivAt_interval hx7
    rw [(hx1.sub hx2).deriv]
  · simp [uIoc]

/-- If `f` is absolute continuous on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem AbsolutelyContinuousOnInterval.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ}
  (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b := by
  exact hf.boundedVariationOn.locallyBoundedVariationOn.deriv_intervalIntegrable

/-- If `f` is interval integrable on `a..b` and `c ∈ uIcc a b`, then `fun x ↦ ∫ v in c..x, f v` is
absolute continuous on `uIcc a b`. -/
theorem IntervalIntegrable.integral_absolutelyContinuousOnInterval {f : ℝ → ℝ} {a b : ℝ}
    (h : IntervalIntegrable f volume a b) (c : ℝ) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  wlog hab : a ≤ b
  · have S : uIcc a b = uIcc b a := by exact uIcc_comm a b
    exact @this f b a h.symm c (S ▸ hc) (by linarith) |>.symm
  have subinterval_integrable {x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : a ≤ y ∧ y ≤ b) :
      IntervalIntegrable f volume x y := by
    apply IntervalIntegrable.mono_set' (a := a) (b := b)
    · assumption
    · dsimp [uIoc]
      simp only [hab, inf_of_le_left, sup_of_le_right]
      gcongr <;> simp [hx, hy]
  have hf := h.1.hasFiniteIntegral
  unfold HasFiniteIntegral at hf
  replace hf := ne_of_lt hf
  unfold AbsolutelyContinuousOnInterval
  rw [uIcc] at hc
  simp_rw [show min a b = a by simp [hab], show max a b = b by simp [hab] ] at hc ⊢
  rw [mem_Icc] at hc
  intro ε hε
  have hε' := ne_of_gt ((ENNReal.ofReal_pos).mpr hε)
  obtain ⟨δ', hδ'1, hδ'2⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf hε'
  let δ'' := min 1 δ'
  have hδ''1 : δ'' ≠ 0 := by positivity
  have hδ''2 : δ'' ≠ ∞ := by simp [δ'']
  use δ''.toReal
  have hδ : δ''.toReal > 0 := by apply ENNReal.toReal_pos <;> assumption
  constructor
  · exact hδ
  · intro n I hI1 hI2 hI3
    let s := ⋃ i ∈ Finset.range n, Set.Ioc (I i).1 (I i).2
    have hs : s ⊆ Set.Ioc a b := by
      dsimp only [s]
      intro x hx
      simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨i, hi1, hi2⟩ := hx
      suffices Ioc (I i).1 (I i).2 ⊆ Ioc a b by exact this hi2
      gcongr <;> linarith [hI1 i hi1]
    have : volume.restrict (Ioc a b) s < δ' := by
      dsimp only [s]
      rw [MeasureTheory.measure_biUnion_finset]
      · have (i : ℕ) (hi : i ∈ Finset.range n) :
            volume.restrict (Ioc a b) (Ioc (I i).1 (I i).2) =
            ENNReal.ofReal (dist (I i).1 (I i).2) := by
          have := hI1 i hi
          have : (I i).1 - (I i).2 ≤ 0 := by simp [this]
          have : Ioc (I i).1 (I i).2 ⊆ Ioc a b := by gcongr <;> tauto
          have : Ioc (I i).1 (I i).2 ∩ Ioc a b = Ioc (I i).1 (I i).2 := by simp [this]
          simp [measurableSet_Ioc, Measure.restrict_apply, this]
          congr
          rw [Real.dist_eq, abs_eq_neg_self.mpr]
          · ring
          · assumption
        calc
        _ = ∑ i ∈ Finset.range n, ENNReal.ofReal ((dist (I i).1 (I i).2)) := by
              apply Finset.sum_congr rfl
              exact this
        _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (dist (I i).1 (I i).2)) := by
              rw [ENNReal.ofReal_sum_of_nonneg]
              simp
        _ < ENNReal.ofReal δ''.toReal := by rw [ENNReal.ofReal_lt_ofReal_iff] <;> assumption
        _ = δ'' := by simp [hδ''2]
        _ ≤ δ' := by simp [δ'']
      · exact hI2
      · simp
    specialize hδ'2 s this
    simp only [Real.dist_eq]
    calc
    _ = ∑ i ∈ Finset.range n, |(∫ (v : ℝ) in (I i).1..(I i).2, f v)| := by
          apply Finset.sum_congr rfl
          intro i hi
          trans |(∫ (v : ℝ) in (I i).2..(I i).1, f v)|
          · congr 1
            rw [← intervalIntegral.integral_add_adjacent_intervals (b := (I i).2)]
            · abel
            all_goals apply subinterval_integrable <;> (constructor <;> linarith [hI1 i hi])
          · rw [intervalIntegral.integral_symm]
            simp
    _ ≤ ∑ i ∈ Finset.range n, (∫ (v : ℝ) in (I i).1..(I i).2, |f v|) := by
          gcongr with i hi
          exact intervalIntegral.abs_integral_le_integral_abs (hI1 i hi).right.left
    _ = ∑ i ∈ Finset.range n, (∫ (v : ℝ) in Ioc (I i).1 (I i).2, |f v|) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact intervalIntegral.integral_of_le (hI1 i hi).right.left
    _ = ∫ (v : ℝ) in s, |f v| := by
          dsimp [s]
          symm
          apply MeasureTheory.integral_finset_biUnion
          · simp
          · exact hI2
          · intro i hi
            have : Ioc (I i).1 (I i).2 ⊆ Ioc a b := by gcongr <;> linarith [hI1 i hi]
            replace h := IntegrableOn.mono_set h.1 this
            dsimp only [IntegrableOn] at h ⊢
            fun_prop
    _ = ∫ (v : ℝ) in s, ‖f v‖ := by congr
    _ = (∫⁻ (v : ℝ) in s, ‖f v‖ₑ).toReal := by
          apply MeasureTheory.integral_norm_eq_lintegral_enorm
          exact AEStronglyMeasurable.mono_set hs h.1.left
    _ = (∫⁻ (x : ℝ) in s, ‖f x‖ₑ ∂volume.restrict (Ioc a b)).toReal := by
          congr 2
          rw [MeasureTheory.Measure.restrict_restrict₀]
          · congr 1; simp [hs]
          · apply MeasurableSet.nullMeasurableSet
            dsimp only [s]
            measurability
    _ < ε := by
          convert ENNReal.toReal_strict_mono _ hδ'2
          · symm; exact ENNReal.toReal_ofReal (by linarith)
          · simp

/-- If `f` has derivative 0 a.e. on `[d, b]`, then there is a coultable Vitali cover of `[d, b]`
a.e., consisting of closed intervals, where each has small variations wrt `f`. -/
lemma ae_deriv_zero_ctb_cover {f : ℝ → ℝ} {d b η : ℝ}
    (hf : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f 0 x) (hη : 0 < η) :
    let t := {(x, h) : ℝ × ℝ | d < x ∧ 0 < h ∧ x + h < b ∧ |f (x + h) - f x| < h * η};
    let B : ℝ × ℝ → Set ℝ := fun (x, h) ↦ Set.Icc x (x + h);
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧ volume (Ioo d b \ ⋃ a ∈ u, B a) = 0 := by
  intro t B
  replace hf : ∀ᵐ x, x ∈ Ioo d b → HasDerivAt f 0 x := by
    filter_upwards [hf] with x hx1 hx2
    exact hx1 (Ioo_subset_Icc_self hx2)
  let s := {x : ℝ | x ∈ Ioo d b ∧ HasDerivAt f 0 x}
  have hs0: NullMeasurableSet s := by
    have : s = Ioo d b \ {x : ℝ | x ∈ Ioo d b ∧ ¬HasDerivAt f 0 x} := by
      simp only [s]; ext x; constructor
        <;> simp only [mem_setOf_eq, mem_diff, mem_Ioo, not_and, not_not, and_imp]
        <;> tauto
    have : NullMeasurableSet (Ioo d b) := by measurability
    have : NullMeasurableSet {x : ℝ | x ∈ Ioo d b ∧ ¬HasDerivAt f 0 x} := by
      rw [ae_iff] at hf
      push_neg at hf
      exact NullMeasurableSet.of_null hf
    measurability
  have : ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧ volume (s \ ⋃ a ∈ u, B a) = 0 := by
    apply Vitali.exists_disjoint_covering_ae volume s t 6 (Prod.snd) (Prod.fst) B
    · simp only [Icc, Metric.closedBall, Real.dist_eq, abs_le', tsub_le_iff_right, neg_sub,
      setOf_subset_setOf, and_imp, Prod.forall, B]
      intros; constructor <;> linarith
    · intro A hA
      simp only [Real.volume_closedBall, ENNReal.coe_ofNat, Real.volume_Icc, add_sub_cancel_left, B]
      rw [show 6 = ENNReal.ofReal 6 by norm_num, ← ENNReal.ofReal_mul] <;> try norm_num
      rw [ENNReal.ofReal_le_ofReal_iff]
      · linarith
      · simp only [mem_setOf_eq, t] at hA; linarith
    · simp +contextual [B, t]
    · simp [B, isClosed_Icc]
    · intro x hx ε hε
      simp only [mem_Ioo, mem_setOf_eq, s] at hx
      obtain ⟨δ, hδ1, hδ2⟩ := (Metric.tendsto_nhds_nhds).mp (hasDerivAt_iff_tendsto.mp hx.2) η hη
      set δ' := min (min (δ / 2) ε) ((b - x) / 2)
      use (x, δ')
      have h1 : δ' > 0 := by simp [δ', hε, hδ1, hx.left.right]
      have h2 : δ' ≥ 0 := by exact le_of_lt h1
      have h3 : |δ'| < δ := by rw [abs_eq_self.mpr h2]; simp [δ', hδ1]
      simp only [mem_setOf_eq, h1, true_and, and_true, t]
      simp only [Real.dist_eq, Real.norm_eq_abs, smul_eq_mul, mul_zero, sub_zero, dist_zero_right,
        norm_mul, norm_inv, abs_abs] at hδ2
      specialize hδ2 (show |x + δ' - x| < δ by simp [h3])
      simp only [add_sub_cancel_left] at hδ2
      rw [abs_eq_self.mpr h2, ← mul_lt_mul_left h1] at hδ2
      repeat' constructor
      · exact hx.left.left
      · have : δ' ≤ (b - x) / 2 := by simp [δ']
        linarith
      · convert hδ2 using 1; field_simp
      · simp [δ']
  obtain ⟨u, hu⟩ := this
  use u
  simp only [hu, true_and]
  have hv : Ioo d b \ ⋃ a ∈ u, B a ⊆ (Ioo d b \ s) ∪ (s \ ⋃ a ∈ u, B a) := by tauto_set
  suffices volume ((Ioo d b \ s) ∪ (s \ ⋃ a ∈ u, B a)) = 0 by exact Measure.mono_null hv this
  simp only [measure_union_null_iff]; constructor
  · convert ae_iff.mp hf using 2
    ext x
    simp only [mem_Ioo, mem_diff, mem_setOf_eq, s]
    tauto
  · tauto

/-- If `f` has derivative 0 a.e. on `[d, b]`, then there is a finite Vitali cover of `[d, b]`
except for measure at most `δ`, consisting of closed intervals, where each has small variations
wrt `f`. -/
lemma ae_deriv_zero_fin_cover {f : ℝ → ℝ} {d b η δ : ℝ}
    (hf : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f 0 x)
    (hη : 0 < η) (hδ : 0 < δ) :
    let t := {(x, h) : ℝ × ℝ | d < x ∧ 0 < h ∧ x + h < b ∧ |f (x + h) - f x| < h * η};
    let B : ℝ × ℝ → Set ℝ := fun (x, h) ↦ Set.Icc x (x + h);
    ∃ n : ℕ, ∃ v : ℕ → ℝ × ℝ,
      Set.image v (Finset.range n) ⊆ t ∧
      Set.PairwiseDisjoint (Finset.range n) (fun i ↦ B (v i)) ∧
      volume (Ioo d b \ ⋃ i ∈ Finset.range n, B (v i)) < ENNReal.ofReal δ := by
  intro t B
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := ae_deriv_zero_ctb_cover hf hη
  obtain ⟨e, he⟩ := Set.countable_iff_exists_injOn.mp hu2
  have : Ioo d b \ ⋃ a ∈ u, B a = ⋂ (i : ℕ), (Ioo d b \ ⋃ a ∈ {x ∈ u | e x < i}, B a) := by
    ext x; simp only [mem_diff, mem_iUnion, exists_prop, not_exists, not_and,
      mem_setOf_eq, mem_iInter, and_imp]
    constructor
    · intro ⟨h1, h2⟩ i
      constructor <;> simp +contextual [h1, h2]
    · intro h
      constructor
      · exact (h 0).left
      · intro x hx; exact (h (e x + 1)).right x hx (by omega)
  rw [this] at hu4
  rw [MeasureTheory.measure_iInter_eq_iInf_measure_iInter_le] at hu4
  · clear this
    replace hu4 := hu4.symm ▸
      (show @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0 < ENNReal.ofReal δ by simp [hδ])
    rw [iInf_lt_iff] at hu4
    obtain ⟨n, hn⟩ := hu4
    classical
    let enum := (Finset.equivFin {j ∈ Finset.range n | ∃ x ∈ u, e x = j}).symm
    set n' := Finset.card ({j ∈ Finset.range n | ∃ x ∈ u, e x = j})
    have hvi (i : ℕ) (hi : i < n') : ∃ x ∈ u, e x = enum ⟨i, hi⟩ := by
      have := (enum ⟨i, hi⟩).property
      simp only [Finset.mem_filter, Finset.mem_range] at this
      tauto
    let v (i : ℕ) : ℝ × ℝ :=
      if hi : i < n' then Classical.choose (hvi i hi) else (0, 0)
    have v_prop (i : ℕ) (hi : i < n') : v i ∈ u ∧ e (v i) = enum ⟨i, hi⟩ := by
      simp only [hi, ↓reduceDIte, v]
      exact Classical.choose_spec (hvi i hi)
    use n', v
    constructor
    · intro z hz
      simp only [Finset.coe_range, mem_image, mem_Iio] at hz
      obtain ⟨i, hi1, hi2⟩ := hz
      exact hi2 ▸ hu1 (v_prop i hi1).left
    · constructor
      · intro i hi j hj hij
        have hi1 := v_prop i (Finset.mem_range.mp hi)
        have hj1 := v_prop j (Finset.mem_range.mp hj)
        apply hu3 hi1.left hj1.left
        intro hC
        have := Fin.mk.inj_iff.mp <| Equiv.injective enum <| Subtype.eq <|
          hj1.right ▸ hC ▸ hi1.right
        tauto
      · convert hn
        ext x
        simp only [Finset.mem_range, mem_diff, mem_iUnion, exists_prop, not_exists, not_and,
          mem_setOf_eq, mem_iInter, and_imp]
        constructor
        · intro ⟨hx1, hx2⟩ j hj
          constructor; · assumption
          intro y hy1 hy2
          have hy : e y ∈ {j ∈ Finset.range n | ∃ x ∈ u, e x = j} := by
            simp only [Finset.mem_filter, Finset.mem_range]
            constructor; omega; use y
          let i := enum.symm ⟨e y, hy⟩
          have hi : i < n' := by exact i.isLt
          have : y = v i := by
            have : e y = enum i := by simp [i]
            exact he hy1 (v_prop i hi).left (this ▸ (v_prop i hi).right.symm)
          exact this.symm ▸ hx2 i hi
        · intro hx
          constructor
          · exact hx 0 (by omega) |>.left
          · intro i hi
            have := v_prop i hi
            apply hx n (by omega) |>.right (v i)
            · tauto
            · rw [this.right]
              set j := enum ⟨i, hi⟩
              have := j.property
              simp only [Finset.mem_filter, Finset.mem_range] at this
              exact this.left
  · intro i
    dsimp only [B]
    apply NullMeasurableSet.diff; · measurability
    apply NullMeasurableSet.biUnion
    · exact hu2.mono (by simp)
    · measurability
  · use 0
    have : volume (Ioo d b) ≠ ∞ := by simp
    intro hC
    apply measure_mono_top (s₂ := Ioo d b) at hC
    · tauto
    · simp

/-- If `f` has derivative 0 a.e. on `[d, b]`, then there is a finite Vitali cover of `[d, b]`
except for measure at most `δ`, consisting of closed intervals, where each has small variations
wrt `f`. Additionally, The finite cover is already ordered. -/
lemma ae_deriv_zero_fin_ordered_cover {f : ℝ → ℝ} {d b η δ : ℝ}
    (hf : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f 0 x)
    (hη : 0 < η) (hδ1 : 0 < δ) :
    ∃ n : ℕ, ∃ v : ℕ → ℝ × ℝ,
      (∀ i ∈ Finset.range n, d < (v i).1 ∧ 0 < (v i).2 ∧ (v i).1 + (v i).2 < b ∧
        |f ((v i).1 + (v i).2) - f (v i).1| < (v i).2 * η) ∧
      (∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i < j → (v i).1 + (v i).2 < (v j).1) ∧
      (b - d) - (∑ i ∈ Finset.range n, (v i).2) < δ := by
  obtain ⟨n, v, hv1, hv2, hv3⟩ := ae_deriv_zero_fin_cover hf hη hδ1
  replace hv1 : ∀ i ∈ Finset.range n, d < (v i).1 ∧ 0 < (v i).2 ∧ (v i).1 + (v i).2 < b ∧
      |f ((v i).1 + (v i).2) - f (v i).1| < (v i).2 * η := by
    intro i hi
    have : v i ∈ {(x, h) : ℝ × ℝ | d < x ∧ h > 0 ∧ x + h < b ∧ |f (x + h) - f x| < h * η} := by
      apply @hv1 (v i)
      simp only [Finset.coe_range, mem_image, mem_Iio]
      use i; exact ⟨List.mem_range.mp hi, rfl⟩
    simpa using this
  let r_list := @Finset.sort (Finset.range n) (fun (i j) ↦ (v i).1 ≤ (v j).1) _
    { trans := by intros; linarith }
    { antisymm := by
        intro i j h1 h2
        have hij: (v i).1 = (v j).1 := by linarith
        have := hv2 i.property j.property
        contrapose this
        push_neg
        constructor
        · exact Subtype.coe_ne_coe.mpr this
        · simp only [Disjoint, le_eq_subset, bot_eq_empty, subset_empty_iff, not_forall]
          use {(v i).1}
          simp only [singleton_ne_empty, not_false_eq_true, singleton_subset_iff, exists_prop,
            and_true]
          constructor <;> simp only [mem_Icc, le_refl, le_add_iff_nonneg_right, true_and]
          · linarith [hv1 i.val i.property]
          · simp only [hij, le_refl, le_add_iff_nonneg_right, true_and]
            linarith [hv1 j.val j.property] }
    { total := by intros; exact LinearOrder.le_total _ _ }
    Finset.univ
  have r_list_len : r_list.length = n := by simp [r_list]
  let r (i : ℕ) : ℕ :=
    if hi : i ∈ Finset.range n then r_list.get ⟨i, r_list_len.symm ▸ Finset.mem_range.mp hi⟩
    else i
  have r_mem {i : ℕ} (hi : i ∈ Finset.range n) : r i ∈ Finset.range n := by
    simp [r, Finset.mem_range.mp hi]
  have r_mono {i j : ℕ} (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range n) (hij : i ≤ j) :
      (v (r i)).1 ≤ (v (r j)).1 := by
    have : List.Sorted (fun (i j : Finset.range n) ↦ (v i).1 ≤ (v j).1) r_list := by simp [r_list]
    simp only [hi, hj, r, ↓reduceDIte]
    apply @List.Sorted.rel_get_of_le _ _ {refl := by simp +contextual} _ this
    simpa
  have r_inj {i j : ℕ} (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range n) (hij : i ≠ j) :
      r i ≠ r j := by
    have nodup : r_list.Nodup := by simp [r_list]
    have := List.Nodup.getElem_inj_iff (h := nodup)
      (hi := r_list_len.symm ▸ (List.mem_range.mp hi))
      (hj := r_list_len.symm ▸ (List.mem_range.mp hj))
    simp only [hi, hj, r, ↓reduceDIte]
    intro hC
    have := this.mp (Subtype.eq hC)
    contradiction
  have r_surj {k : ℕ} (hk : k ∈ Finset.range n) : ∃ i ∈ Finset.range n, r i = k := by
    have : ⟨k, hk⟩ ∈ r_list := by simp [r_list]
    obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.mp this
    rw [r_list_len] at hi
    use i; constructor
    · rwa [Finset.mem_range]
    · simp [r, hi, h]
  let v' (i : ℕ) : (ℝ × ℝ) := v (r i)
  use n, v'
  repeat' constructor
  · intro i hi
    simp only [v']
    exact hv1 _ (r_mem hi)
  · intro i hi j hj hij
    have hi1 : i + 1 ∈ Finset.range n := by
      have := List.mem_range.mp hj;
      rw [Finset.mem_range]; omega
    simp only [v']
    suffices (v (r i)).1 + (v (r i)).2 < (v (r (i + 1))).1 by
      have : (v (r (i + 1))).1 ≤ (v (r j)).1 := by apply r_mono <;> assumption
      refine lt_of_lt_of_le ?_ this; assumption
    have hL: (v (r i)).1 ≤ (v (r (i + 1))).1 := by apply r_mono <;> (first | assumption | omega)
    have disj := hv2 (r_mem hi) (r_mem hi1) (by apply r_inj <;> (first | assumption | omega))
    simp only [Disjoint, le_eq_subset, bot_eq_empty, subset_empty_iff] at disj
    specialize @disj {(v (r (i + 1))).1}
    by_contra hC
    have : (v (r (i + 1))).1 ≤ (v (r i)).1 + (v (r i)).2 := by linarith
    simp only [singleton_subset_iff, mem_Icc, hL, this, and_self, le_refl,
      le_add_iff_nonneg_right, true_and, singleton_ne_empty, imp_false, not_le,
      forall_const] at disj
    linarith [hv1 _ (r_mem hi1)]
  rw [MeasureTheory.measure_diff, MeasureTheory.measure_biUnion_finset] at hv3
  · simp only [Real.volume_Icc, Real.volume_Ioo, add_sub_cancel_left] at hv3
    have : ∑ i ∈ Finset.range n, (v' i).2 = ∑ x ∈ Finset.range n, (v x).2 := by
      dsimp only [v']
      symm
      have : Finset.range n = Finset.image r (Finset.range n) := by
        ext k; constructor
        · intro hk
          simp only [Finset.mem_image]
          obtain ⟨i, hi1, hi2⟩ := r_surj hk; use i, hi1
        · intro hk
          simp only [Finset.mem_image] at hk
          obtain ⟨i, hi1, hi2⟩ := hk
          exact hi2 ▸ r_mem hi1
      nth_rw 1 [this]
      apply @Finset.sum_image (g := r)
      dsimp only [InjOn]
      intro i hi j hj; contrapose!; exact r_inj hi hj
    rw [this]
    have : ∀ i ∈ Finset.range n, 0 ≤ (v i).2 := by intro i hi; linarith [hv1 i hi]
    rw [← ENNReal.ofReal_sum_of_nonneg, ← ENNReal.ofReal_sub] at hv3
    · exact (ENNReal.ofReal_lt_ofReal_iff hδ1).mp hv3
    · exact Finset.sum_nonneg this
    · exact this
  · assumption
  · simp +contextual
  · intro x hx
    simp only [Finset.mem_range, mem_iUnion, exists_prop] at hx
    obtain ⟨i, hi1, hi2⟩ := hx
    simp only [mem_Icc] at hi2
    rw [mem_Ioo]
    constructor <;> linarith [hv1 i (List.mem_range.mpr hi1)]
  · measurability
  · have : ∑ i ∈ Finset.range n, volume (Icc (v i).1 ((v i).1 + (v i).2)) ≠ ⊤ := by simp
    exact ne_top_of_le_ne_top this <| measure_biUnion_finset_le (Finset.range n)
      fun i ↦ Icc (v i).1 ((v i).1 + (v i).2)

lemma split_sum_even_odd (n : ℕ) (f : ℕ → ℝ) : ∑ i ∈ Finset.range (2 * n + 1), f i =
    ∑ i ∈ Finset.range (n + 1), f (2 * i) + ∑ i ∈ Finset.range n, f (2 * i + 1) := by
  let A : Finset ℕ := {i ∈ Finset.range (2 * n + 1) | Even i}
  let B : Finset ℕ := {i ∈ Finset.range (2 * n + 1) | Odd i}
  have disj : Disjoint A B := by
    suffices A ∩ B = ∅ by exact Finset.disjoint_iff_inter_eq_empty.mpr this
    suffices ¬∃ x, x ∈ A ∩ B by exact Finset.not_nonempty_iff_eq_empty.mp this
    by_contra hC
    obtain ⟨x, hx⟩ := hC
    simp [A, B] at hx
    have : ¬(Even x ∧ Odd x) := by simp
    tauto
  have union : Finset.range (2 * n + 1) = A.disjUnion B disj := by
    ext a; simp only [Finset.mem_range, Finset.disjUnion_eq_union, Finset.mem_union,
      Finset.mem_filter, A, B]
    constructor
    · intro ha
      have : Odd a ↔ ¬Even a := by simp
      tauto
    · tauto
  rw [union, Finset.sum_disjUnion]
  congr 1
  · let r (i : ℕ) := 2 * i
    have : A = Finset.image r (Finset.range (n + 1)) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, A, r]
      constructor
      · intro ⟨h1, ⟨b, hb⟩⟩; use b; omega
      · intro ⟨b, h1, h2⟩; constructor; · omega
        use b; omega
    rw [this]
    apply @Finset.sum_image (g := r)
    dsimp only [InjOn, r]
    intros; omega
  · let r (i : ℕ) := 2 * i + 1
    have : B = Finset.image r (Finset.range n) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, B, r]
      constructor
      · intro ⟨h1, ⟨b, hb⟩⟩; use b; omega
      · intro ⟨b, h1, h2⟩; constructor; · omega
        use b; omega
    rw [this]
    apply @Finset.sum_image (g := r)
    dsimp only [InjOn, r]
    intros; omega

/-- If `f` is absolutely continuous on `uIcc a b` and `f' x = 0` for a.e. `x ∈ uIcc a b`, then `f`
is constant on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_deriv_zero_const {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hf1 : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f 0 x) :
    ∃ C, ∀ x ∈ uIcc a b, f x = C := by
  wlog hab : a ≤ b
  · have S : uIcc a b = uIcc b a := by exact uIcc_comm a b
    exact S.symm ▸ @this f b a hf.symm (S ▸ hf1) (by linarith)
  suffices ∀ x ∈ uIcc a b, f x = f b by use f b
  by_contra hC
  push_neg at hC
  obtain ⟨d, hd1, hd2⟩ := hC
  simp only [Set.uIcc, mem_Icc,
    show min a b = a by simp [hab], show max a b = b by simp [hab] ] at hd1
  have had : a ≤ d := by linarith
  have hdb : d < b := lt_of_le_of_ne hd1.right fun hC ↦ hd2 (congrArg f hC)
  dsimp only [AbsolutelyContinuousOnInterval] at hf
  have hfdb: 0 < |f d - f b| / 2 := by
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right, abs_pos, ne_eq]
    rwa [sub_eq_zero]
  obtain ⟨δ, hδ1, hδ2⟩ := hf (|f d - f b| / 2) hfdb
  simp_rw [uIcc, show min a b = a by simp [hab], show max a b = b by simp [hab] ] at hf1 hδ2 ⊢
  replace hf1 : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f 0 x := by
    filter_upwards [hf1] with x hx1 hx2
    apply hx1
    suffices Icc d b ⊆ Icc a b by exact this hx2
    gcongr
  have hfdb': 0 < |f d - f b| / (2 * (b - d)) := by
    apply div_pos <;> linarith
  obtain ⟨n, v, hv1, hv2, hv3⟩ := ae_deriv_zero_fin_ordered_cover hf1 hfdb' hδ1
  let I (i : ℕ) :=
    if i < n then
      if i = 0 then (d, (v i).1) else ((v (i - 1)).1 + (v (i - 1)).2, (v i).1)
    else
      if i = n ∧ 0 < n then ((v (i - 1)).1 + (v (i - 1)).2, b) else (d, b)
  have hI1 : (I 0).1 = d := by
    dsimp only [I]
    split_ifs
    any_goals omega
    all_goals simp
  have hI2 : (I n).2 = b := by
    dsimp only [I]
    split_ifs
    any_goals omega
    all_goals simp
  have hI3 (i : ℕ) (hi : i ∈ Finset.range n) : (I (i + 1)).1 = (v i).1 + (v i).2 := by
    have := Finset.mem_range.mp hi
    dsimp only [I]
    split_ifs
    any_goals omega
    any_goals contradiction
    all_goals simp
  have hI4 (i : ℕ) (hi : i ∈ Finset.range n) : (I i).2 = (v i).1 := by
    have := Finset.mem_range.mp hi
    dsimp only [I]
    split_ifs
    all_goals simp
  have hI : ∀ i ∈ Finset.range (n + 1), a ≤ (I i).1 ∧ (I i).1 ≤ (I i).2 ∧ (I i).2 ≤ b := by
    · intro i hi
      by_cases hi1 : i < n
      · simp only [hi1, ↓reduceIte, I]
        · by_cases hi0 : i = 0
          · simp only [hi0, ↓reduceIte, true_and, had]
            constructor <;> linarith [hv1 0 (by rw [Finset.mem_range]; omega)]
          · simp only [hi0, ↓reduceIte]
            have := hv1 (i - 1) (by rw [Finset.mem_range]; omega)
            have := hv1 i (by rw [Finset.mem_range]; omega)
            have := hv2 (i - 1) (by rw [Finset.mem_range]; omega) i
              (by rw [Finset.mem_range]; omega) (by omega)
            constructor
            · linarith
            · constructor <;> linarith
      · simp only [hi1, ↓reduceIte, I]
        · by_cases hn : i = n ∧ 0 < n
          · simp only [hn, and_self, ↓reduceIte, le_refl, and_true]
            constructor <;> linarith [hv1 (n - 1) (by rw [Finset.mem_range]; omega)]
          · simp only [hn, ↓reduceIte, le_refl, and_true, true_and, had]
            exact hd1.right
  let r (i : ℕ) : ℝ :=
    if Even i then (I (i / 2)).1 else (I (i / 2)).2
  have hr1 (i : ℕ) : r (2 * i) = (I i).1 := by simp [r]
  have hr2 (i : ℕ) : r (2 * i + 1) = (I i).2 := by
    simp only [Nat.not_even_bit1, ↓reduceIte, r]
    congr; omega
  have hrd : d = r 0 := by rw [show 0 = 2 * 0 by rfl, hr1, hI1]
  have hrb : b = r (2 * n + 1) := by rw [hr2, hI2]
  have h_dist_sum : ∑ i ∈ Finset.range (n + 1), dist (I i).1 (I i).2 =
      b - d - ∑ i ∈ Finset.range n, (v i).2 := by
    rw [fun a b c ↦ show a = b - c ↔ b = a + c by constructor <;> (intro h; rw [h]; abel) ]
    calc
    _ = r (2 * n + 1) - r 0 := by rw [hrd, hrb]
    _ = ∑ k ∈ Finset.range (2 * n + 1), (r (k + 1) - r k) := by rw [← Finset.sum_range_sub]
    _ = ∑ i ∈ Finset.range (n + 1), (r (2 * i + 1) - r (2 * i)) +
        ∑ i ∈ Finset.range n, (r (2 * i + 1 + 1) - r (2 * i + 1)) := by
      rw [split_sum_even_odd]
    _ = ∑ i ∈ Finset.range (n + 1), dist (I i).1 (I i).2 + ∑ i ∈ Finset.range n, (v i).2 := by
      congr 1 <;> apply Finset.sum_congr rfl
      · intro i hi
        rw [hr1, hr2, Real.dist_eq, abs_eq_neg_self.mpr]
        · abel
        · linarith [hI i hi]
      · intro i hi
        rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, hr1, hr2, hI3, hI4] <;> try assumption
        abel
  have : ∑ i ∈ Finset.range (n + 1), dist (f (I i).1) (f (I i).2) < |f d - f b| / 2 := by
    apply hδ2 (n + 1) I
    · exact hI
    · intro i hi j hj hij
      wlog hij1 : i < j
      · exact (this hf hab d hd2 hd1 had hdb hfdb δ hδ1 hδ2 hf1 hfdb' n v hv1 hv2 hv3 hI1 hI2
          hI3 hI4 hI hr1 hr2 hrd hrb h_dist_sum hj hi hij.symm (by omega)).symm
      · simp only [Ioc_disjoint_Ioc, le_sup_iff, inf_le_iff]
        have hv2' {i j : ℕ} (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range n) (hij : i ≤ j) :
            (v i).1 ≤ (v j).1 := by
          by_cases hij0 : i = j
          · rw [hij0]
          · linarith [hv2 i hi j hj (by omega), hv1 i hi]
        right; left
        have hjn : j < n + 1 := by exact Finset.mem_range.mp hj
        have hin : i < n + 1 := by exact Finset.mem_range.mp hi
        replace hin : i < n := by omega
        simp only [hin, ↓reduceIte, I]
        have (a : ℝ) (ha : 0 < a) : 0 ≤ a := by exact le_of_lt ha
        split_ifs <;> (simp only; try omega)
        all_goals apply le_add_of_le_of_nonneg
        all_goals try refine le_of_lt (hv1 _ ?_).right.left
        all_goals try refine hv2' ?_ ?_ ?_
        all_goals try rw [Finset.mem_range]
        all_goals omega
    · convert hv3 using 1
  suffices |f d - f b| < |f d - f b| by linarith
  calc
  _ = |f (r 0) - f (r (2 * n + 1))| := by rw [hrd, hrb]
  _ = |(f ∘ r) 0 - (f ∘ r) (2 * n + 1)| := by simp
  _ = |∑ k ∈ Finset.range (2 * n + 1), ((f ∘ r) k - (f ∘ r) (k + 1))| := by
    rw [← Finset.sum_range_sub']
  _ = |∑ k ∈ Finset.range (2 * n + 1), (f (r k) - f (r (k + 1)))| := by simp
  _ ≤ ∑ k ∈ Finset.range (2 * n + 1), |f (r k) - f (r (k + 1))| := by
    apply Finset.abs_sum_le_sum_abs
  _ = ∑ i ∈ Finset.range (n + 1), |f (r (2 * i)) - f (r (2 * i + 1))| +
      ∑ i ∈ Finset.range n, |f (r (2 * i + 1)) - f (r (2 * i + 1 + 1))| := by
    rw [split_sum_even_odd]
  _ = ∑ i ∈ Finset.range (n + 1), dist (f (I i).1) (f (I i).2) +
      ∑ i ∈ Finset.range n, |f ((v i).1 + (v i).2) - f ((v i).1)| := by
    congr 1 <;> apply Finset.sum_congr rfl
    · intro i hi
      rw [hr1, hr2, Real.dist_eq]
    · intro i hi
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, hr1, hr2, hI3, hI4] <;> try assumption
      nth_rw 1 [← abs_neg]; congr 1; abel
  _ < |f d - f b| / 2 + ∑ i ∈ Finset.range n, |f ((v i).1 + (v i).2) - f ((v i).1)| := by
    gcongr 1
  _ ≤ |f d - f b| / 2 + ∑ i ∈ Finset.range n, (v i).2 * (|f d - f b| / (2 * (b - d))) := by
    gcongr with i hi
    specialize hv1 i hi
    linarith
  _ = |f d - f b| / 2 + (∑ i ∈ Finset.range n, (v i).2) * (|f d - f b| / (2 * (b - d))) := by
    rw [Finset.sum_mul]
  _ ≤ |f d - f b| / 2 + (b - d) * (|f d - f b| / (2 * (b - d))) := by
    gcongr
    suffices 0 ≤ (b - d) - ∑ i ∈ Finset.range n, (v i).2 by linarith
    rw [← h_dist_sum]
    apply Finset.sum_nonneg; simp
  _ = |f d - f b| := by field_simp [show b - d ≠ 0 by linarith]; ring

/-- *Fundamental Theorem of Calculus* for absolutely continuous functions: if `f` is absolutely
continuous on `uIcc a b`, then `∫ (x : ℝ) in a..b, deriv f x = f b - f a`. -/
theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ (x : ℝ) in a..b, deriv f x = f b - f a := by
  have f_deriv := hf.ae_hasDerivAt
  have f_deriv_integrable := hf.deriv_intervalIntegrable
  have f_deriv_integral_ac := hf.deriv_intervalIntegrable.integral_absolutelyContinuousOnInterval
  have f_deriv_integral_deriv := f_deriv_integrable.ae_eq_deriv_integral (c := a) (hc := by simp)
  let g (x : ℝ) := f x - ∫ (t : ℝ) in a..x, deriv f t
  have g_ac : AbsolutelyContinuousOnInterval g a b := hf.sub (f_deriv_integral_ac a (by simp))
  have g_ae_deriv_zero : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt g 0 x := by
    filter_upwards [f_deriv, f_deriv_integral_deriv] with x hx1 hx2 hx3
    convert (hx1 hx3).sub (hx2 hx3)
    abel
  have g_const := g_ac.ae_deriv_zero_const g_ae_deriv_zero
  obtain ⟨C, hC⟩ := g_const
  have C_val : C = f a := by
    specialize hC a (by simp)
    simp only [intervalIntegral.integral_same, sub_zero, g] at hC
    exact hC.symm
  specialize hC b (by simp)
  simp only [C_val, g] at hC
  rw [← hC]; abel

/-- The integral of the derivative of a product of two absolutely continuous functions. -/
theorem AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, deriv f x * g x + f x * deriv g x = f b * g b - f a * g a := by
  have fg_ac := hf.mul hg
  have fg_ac_FTC := fg_ac.integral_deriv_eq_sub
  simp only [Pi.mul_apply] at fg_ac_FTC
  rw [← fg_ac_FTC]
  apply intervalIntegral.integral_congr_ae
  have f_deriv := hf.ae_hasDerivAt
  have g_deriv := hg.ae_hasDerivAt
  filter_upwards [f_deriv, g_deriv] with x hx1 hx2 hx3
  have hx4 : x ∈ uIcc a b := by rw [uIcc]; rw [uIoc] at hx3; exact Ioc_subset_Icc_self hx3
  have hx5 := (hx1 hx4).mul (hx2 hx4)
  exact hx5.deriv.symm

/-- *Integration by parts* for absolutely continuous functions. -/
theorem AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, f x * deriv g x = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x := by
  rw [← AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hf hg,
      ← intervalIntegral.integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hf.deriv_intervalIntegrable.mul_continuousOn hg.continuousOn).add
      (hg.deriv_intervalIntegrable.continuousOn_mul hf.continuousOn)
  · exact hf.deriv_intervalIntegrable.mul_continuousOn hg.continuousOn
