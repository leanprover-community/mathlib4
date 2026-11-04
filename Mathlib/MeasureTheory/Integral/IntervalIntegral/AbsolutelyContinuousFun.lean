/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu, Dmitri Arkhipov
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

import Mathlib.Algebra.BigOperators.Group.Finset.Gaps
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Fundamental theorem of calculus and integration by parts for absolutely continuous functions

This file proves that:
* `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`: If `f` is absolutely continuous on
  `uIcc a b`, then *Fundamental Theorem of Calculus* holds for `f'` on `a..b`, i.e.
  `∫ (x : ℝ) in a..b, deriv f x = f b - f a`.
* `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`:
  *Integration by Parts* holds for absolutely continuous functions, i.e. if `f` and `g` are
  absolutely continuous on `uIcc a b`, then
  `∫ x in a..b, f x * deriv g x = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x`.

## Tags
absolutely continuous, fundamental theorem of calculus, integration by parts, potential drift
-/

/-!
This file also proves the *potential drift lemma* and its corollaries:
* `AbsolutelyContinuousOnInterval.measure_toReal_le_of_deriv_le`: if `deriv f ≤ -c` (`0 < c`)
a.e. on a measurable `s ⊆ Icc a b`, then `(volume s).toReal ≤ (f a - f b) / c`.
* `AbsolutelyContinuousOnInterval.measure_toReal_le_of_deriv_le_of_antitoneOn`: same, with the
sign condition derived from `AntitoneOn f (Icc a b)`.
* `AbsolutelyContinuousOnInterval.measure_toReal_inter_Icc_le_of_deriv_le_of_antitoneOn`:
escape-time corollary on `Ici 0`: total "bad time" at rate `c` is at most `f 0 / c`.
-/

open scoped Finset

public section

variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

open Filter Fin.NatCast Function MeasureTheory Set

open scoped Topology

/-- If `f` has derivative `f'` a.e. on `[d, b]` and `η` is positive, then there is a collection of
pairwise disjoint closed subintervals of `[a, b]` of total length `b - a` where the slope of `f`
on each subinterval `[x, y]` differs from `f' x` by at most `η`. -/
lemma exists_dist_slope_lt_pairwiseDisjoint_hasSum {f f' : ℝ → F} {d b η : ℝ}
    (hdb : d ≤ b) (hf : ∀ᵐ x, x ∈ Ioo d b → HasDerivAt f (f' x) x) (hη : 0 < η) :
    ∃ u : Set (ℝ × ℝ),
      (∀ z ∈ u, (d < z.1 ∧ z.1 < z.2 ∧ z.2 < b) ∧ dist (slope f z.1 z.2) (f' z.1) < η) ∧
      u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2) ∧
      HasSum (fun (z : u) ↦ z.val.2 - z.val.1) (b - d) := by
  -- Proof idea: Use `Vitali.exists_disjoint_covering_ae'` to get a Vitali cover of `[a, b]`
  -- consisting of closed subintervals `[x, y]` on which the slope of `f` differs from `f' x` by
  -- at most `η`.
  rcases hdb.eq_or_lt with rfl | hdb
  · exact ⟨∅, by simp⟩
  let t := {z : ℝ × ℝ | (d < z.1 ∧ z.1 < z.2 ∧ z.2 < b) ∧ dist (slope f z.1 z.2) (f' z.1) < η}
  let s := {x ∈ Ioo d b | HasDerivAt f (f' x) x}
  obtain ⟨u, ⟨hu₁, hu₂, hu₃, hu₄⟩⟩ : ∃ u ⊆ t, u.Countable ∧
      u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2) ∧ volume (s \ ⋃ z ∈ u, Icc z.1 z.2) = 0 := by
    apply Vitali.exists_disjoint_covering_ae' volume s t 6 (Prod.snd - Prod.fst) Prod.fst
      (fun z ↦ Icc z.1 z.2)
    · grind [Metric.closedBall, Real.dist_eq, Pi.sub_apply, abs_le']
    · intro A hA
      simp only [Pi.sub_apply, Real.volume_closedBall, ENNReal.coe_ofNat, Real.volume_Icc]
      rw [show 6 = ENNReal.ofReal 6 by simp, ← ENNReal.ofReal_mul (by simp),
          ENNReal.ofReal_le_ofReal_iff (by grind)]
      linarith
    · simp +contextual [t]
    · simp [isClosed_Icc]
    · intro x hx
      apply Eventually.frequently
      have := hasDerivAt_iff_tendsto_slope.mp hx.right
      obtain ⟨δ, hδ₁, hδ₂⟩ := (Metric.tendsto_nhdsWithin_nhds).mp
        (hasDerivAt_iff_tendsto_slope.mp hx.right) η hη
      have evn_bound {α : ℝ} (hα : 0 < α) : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, ε < α := by
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
        exact ⟨Ioo (-α) α, by grind, isOpen_Ioo, by grind⟩
      have evn_pos : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, 0 < ε := eventually_mem_nhdsWithin
      filter_upwards [evn_pos, evn_bound hη, evn_bound hδ₁,
                      evn_bound (α := (b - x) / 2) (by simp [hx.left.right])]
        with ε hε₁ hε₂ hε₃ hε₄
      refine ⟨(x, x + ε), ⟨⟨hx.1.1, by linarith, by linarith⟩, ?_⟩, by simp, rfl⟩
      exact hδ₂ (by grind) (by simp [abs_eq_self.mpr hε₁.le, hε₃])
  simp only [t, subset_def, mem_ofPred_eq] at hu₁
  refine ⟨u, ⟨hu₁, hu₃, ?_⟩⟩
  have : Countable u := by simp [hu₂]
  have : Pairwise (Disjoint on fun (z : u) ↦ Icc z.val.1 z.val.2) :=
    fun z₁ z₂ hz₁z₂ ↦ hu₃ z₁.prop z₂.prop (Subtype.coe_ne_coe.mpr hz₁z₂)
  replace hu₄ : volume (Ioo d b \ ⋃ z ∈ u, Icc z.1 z.2) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem] at hu₄ ⊢
    filter_upwards [hf, hu₄] with x hx₁ hx₂
    grind
  have vol_sum : volume (⋃ z : u, Icc z.val.1 z.val.2) = ENNReal.ofReal (b - d) := by
    convert
      Real.volume_Ioo ▸
        measure_eq_measure_of_null_sdiff (by simp only [iUnion_subset_iff]; grind) hu₄ using 2
    simp
  rw [measure_iUnion this (by simp)] at vol_sum
  simp_rw [Real.volume_Icc] at vol_sum
  apply_fun fun x ↦ x.toReal at vol_sum
  rw [ENNReal.tsum_toReal_eq (by simp), ENNReal.toReal_ofReal (by linarith),
      ← Summable.hasSum_iff (by grind [tsum_def])] at vol_sum
  grind [ENNReal.toReal_ofReal]

/-- If `f` is absolutely continuous on `[d, b]` and there is a collection of pairwise disjoint
closed subintervals of `(d, b)` of total length `b - d` such that the sum of `dist (f x) (f y)` for
`[x, y]` in the collection is equal to `y`, then `dist (f b) (f d) ≤ y`. -/
lemma AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum {f : ℝ → X} {d b y : ℝ}
    (hdb : d ≤ b) (hf : AbsolutelyContinuousOnInterval f d b) {u : Set (ℝ × ℝ)}
    (hu₁ : ∀ z ∈ u, d < z.1 ∧ z.1 < z.2 ∧ z.2 < b)
    (hu₂ : u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2))
    (hu₃ : HasSum (fun (z : u) ↦ z.val.2 - z.val.1) (b - d))
    (hu₄ : HasSum (fun (z : u) ↦ dist (f z.val.1) (f z.val.2)) y) :
    dist (f d) (f b) ≤ y := by
  -- Proof idea: The complement of the collection of subintervals of `[d, b]` encoded in `u` can
  -- be approached by the complement of subcollections encoded by finite subsets `s ⊆ u`. These
  -- complements are encoded using `Finset.intervalGapsWithin`.
  -- Their total length tends to `0` as `s` tends to `u` and by absolute continuity of `f`, the sum
  -- of `dist (f x) (f y)` for `[x, y]` in the complement tends to `0` as `s` tends to `u`.
  -- Finally we use the triangle inequality of `dist` to obtain the result.
  let u_coe (s : Finset u) : Finset (ℝ × ℝ) := s.image Subtype.val
  replace hu₁ (s : Finset u) : ∀ ⦃z : ℝ × ℝ⦄, z ∈ u_coe s → d ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := by
    grind
  replace hu₂ (s : Finset u) : (SetLike.coe (u_coe s)).PairwiseDisjoint fun z ↦ Icc z.1 z.2 :=
    hu₂.subset (by grind)
  let T (s : Finset u) :=
    (#(u_coe s) + 1, fun (i : ℕ) ↦ (u_coe s).intervalGapsWithin rfl d b i)
  have hT₁ (s : Finset u) (i : ℕ) := (u_coe s).intervalGapsWithin_le_fst rfl i (hu₁ s)
  have hT₂ (s : Finset u) (i : ℕ) :=
    (u_coe s).intervalGapsWithin_fst_le_snd rfl i hdb (hu₁ s) (hu₂ s)
  have hT₃ (s : Finset u) (i : ℕ) := (u_coe s).intervalGapsWithin_snd_le rfl i (hu₁ s)
  have hT₄ (s : Finset u) := (u_coe s).intervalGapsWithin_pairwiseDisjoint_Ioc rfl (hu₁ s)
  have hT : univ.MapsTo T (disjWithin d b) := by
    intro s _
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `simp`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
    problem in the new canonicalizer; a minimization would help. The original proof was:
    `grind [disjWithin, uIcc_of_le]` -/
    simp [disjWithin]
    grind [uIcc_of_le]
  have u_coe_sum (s : Finset u) (g : ℝ → ℝ → ℝ) :
      ∑ b ∈ s, (g b.val.1 b.val.2) = ∑ z ∈ u_coe s, (g z.1 z.2) :=
    Finset.sum_nbij Subtype.val (by simp [u_coe]) (by simp)
      (by simp only [Finset.coe_image, u_coe]; tauto) (by simp)
  replace hu₃ : Tendsto T atTop (totalLengthFilter ⊓ 𝓟 (disjWithin d b)) := by
    refine tendsto_inf.mpr ⟨?_, hT.tendsto.mono_left (by simp)⟩
    simp only [totalLengthFilter, tendsto_comap_iff]
    convert! hu₃.const_sub (b - d) with s
    · simp only [comp_apply]
      rw [Finset.sum_congr rfl (g := fun i ↦ ((T s).2 i).2 - ((T s).2 i).1)
            (fun i hi ↦ by rw [dist_comm, Real.dist_eq, abs_of_nonneg (by grind)])]
      convert! (u_coe s).sum_intervalGapsWithin_eq_sub_sub_sum rfl id
      exact u_coe_sum s fun x y ↦ y - x
    · abel
  rw [HasSum] at hu₄
  simp_rw [u_coe_sum _ fun x y ↦ dist (f x) (f y)] at hu₄
  have sum_tendsto := hf.comp hu₃ |>.add hu₄
  simp only [comp_apply, zero_add] at sum_tendsto
  have dist_le_sum (s : Finset u) :
      dist (f d) (f b) ≤
      ∑ i ∈ Finset.range (T s).1, dist (f ((T s).2 i).1) (f ((T s).2 i).2) +
      (∑ b ∈ u_coe s, dist (f b.1) (f b.2)) := by
    rw [Finset.sum_eq_sum_range_intervalGapsWithin _ rfl (fun x y ↦ dist (f x) (f y)),
        Finset.sum_range_succ, add_right_comm, ← Finset.sum_add_distrib]
    grw [← Finset.sum_le_sum (fun _ _ ↦ dist_triangle _ _ _),
        ← dist_le_range_sum_dist,
        ← dist_triangle]
    simp [T]
  exact le_of_tendsto_of_tendsto' (by simp) sum_tendsto dist_le_sum

/-- If `f` is absolutely continuous on `uIcc a b` and `f' x = 0` for a.e. `x ∈ uIcc a b`, then `f`
is constant on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero {f : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hf₀ : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f 0 x) :
    ∃ C, ∀ x ∈ uIcc a b, f x = C := by
  -- Proof idea : Assume wlog `a < b`. We need to show that `f d = f b` for any `d ∈ [a, b]`.
  -- Fix `d`. It suffices to show that `dist (f d) (f b) ≤ r` for any `r > 0`. Fix `r`.
  -- Use `exists_dist_slope_lt_pairwiseDisjoint_hasSum` with `η = r / (b - d)` to
  -- get a cover of `[d, b]` consisting of closed subintervals with total length `b - d` such that
  -- the slope of `f` on each subinterval has absolute value `≤ η`. The sum of `dist (f x) (f y)`
  -- for `[x, y]` in the cover must therefore be `≤ (b - d) * η = r`. Use
  -- `AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum` to conclude that
  -- `dist (f d) (f b) ≤ r`.
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ this (a := b) (b := a) hf.symm (uIcc_comm a b ▸ hf₀) (by linarith)
  suffices ∀ x ∈ uIcc a b, f x = f b by use f b
  rw [uIcc_of_le hab] at hf₀ ⊢
  intro d hd
  suffices ∀ r > 0, dist (f d) (f b) ≤ r by
    contrapose! this
    exact exists_between (dist_pos.mpr this)
  intro r hr
  rw [mem_Icc] at hd
  have had : a ≤ d := by linarith
  rcases hd.right.eq_or_lt with rfl | hdb
  · simp [hr.le]
  replace hf₀ : ∀ᵐ x, x ∈ Ioo d b → HasDerivAt f 0 x := by
    filter_upwards [hf₀] with x _ _ using by grind
  have hfdb' : 0 < r / (b - d) := by apply div_pos <;> linarith
  have ⟨u, hu₁, hu₂, hu₃⟩ :=
    exists_dist_slope_lt_pairwiseDisjoint_hasSum hd.right hf₀ hfdb'
  let g := fun (z : u) ↦ dist (f z.val.1) (f z.val.2)
  have g_nonneg : 0 ≤ g := by intro; simp [g]
  have g_finsum_bound (s : Finset u) : ∑ z ∈ s, g z ≤ r := by
    have (z : u) (hz : z ∈ s) : g z ≤ r / (b - d) * (z.val.2 - z.val.1) := by
      have slope_bound := hu₁ z (by simp) |>.right |>.le
      have : 0 < z.val.2 - z.val.1 := by linarith [hu₁ z (by simp)]
      grw [← slope_bound]
      simp only [dist_eq_norm, slope, vsub_eq_sub, sub_zero, g, mul_comm]
      nth_rw 1 [← Real.norm_of_nonneg this.le]
      simp only [norm_smul, Real.norm_eq_abs, norm_inv]
      field_simp
      rw [norm_sub_rev]
    grw [Finset.sum_le_sum this]
    rw [← Finset.mul_sum]
    have : ∑ z ∈ s, (z.val.2 - z.val.1) ≤ b - d :=
      hu₃.tsum_eq ▸ Summable.sum_le_tsum _ (by grind) hu₃.summable
    grw [this]
    field_simp
    grind
  have hu₄ := summable_of_sum_le g_nonneg g_finsum_bound |>.hasSum
  have g_sum_bound := Real.tsum_le_of_sum_le g_nonneg g_finsum_bound
  have := (hf.mono (by grind [uIcc_of_le])).dist_le_of_pairwiseDisjoint_hasSum hd.right
    (fun s hs ↦ hu₁ s hs |>.left) hu₂ hu₃ hu₄
  linarith

/-- *Fundamental Theorem of Calculus* for absolutely continuous functions: if `f` is absolutely
continuous on `uIcc a b`, then `∫ (x : ℝ) in a..b, deriv f x = f b - f a`. -/
theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ (x : ℝ) in a..b, deriv f x = f b - f a := by
  have f_deriv_integral_ac :=
    hf.intervalIntegrable_deriv.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by simp)
  let g (x : ℝ) := f x - ∫ (t : ℝ) in a..x, deriv f t
  have g_ac : AbsolutelyContinuousOnInterval g a b := hf.sub (f_deriv_integral_ac)
  have g_ae_deriv_zero : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt g 0 x := by
    filter_upwards [hf.ae_differentiableAt, hf.intervalIntegrable_deriv.ae_hasDerivAt_integral]
      with x hx₁ hx₂ hx₃
    convert (hx₁ hx₃).hasDerivAt.sub (hx₂ hx₃ a (by simp))
    abel
  obtain ⟨C, hC⟩ := g_ac.const_of_ae_hasDerivAt_zero g_ae_deriv_zero
  have : f a = g a := by simp [g]
  have := hC a (by simp)
  have := hC b (by simp)
  grind

/-- The integral of the derivative of a product of two absolutely continuous functions. -/
theorem AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, deriv f x * g x + f x * deriv g x = f b * g b - f a * g a := by
  rw [← (hf.fun_mul hg).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hf.ae_differentiableAt, hg.ae_differentiableAt] with x hx₁ hx₂ hx₃
  have hx₄ : x ∈ uIcc a b := uIoc_subset_uIcc hx₃
  have hx₅ := (hx₁ hx₄).hasDerivAt.mul (hx₂ hx₄).hasDerivAt
  exact hx₅.deriv.symm

/-- *Integration by parts* for absolutely continuous functions. -/
theorem AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, f x * deriv g x = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x := by
  rw [← AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hf hg,
      ← intervalIntegral.integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hf.intervalIntegrable_deriv.mul_continuousOn hg.continuousOn).add
      (hg.intervalIntegrable_deriv.continuousOn_mul hf.continuousOn)
  · exact hf.intervalIntegrable_deriv.mul_continuousOn hg.continuousOn

open Filter MeasureTheory Set Topology
open scoped ENNReal

section DriftLemma

variable {f : ℝ → ℝ} {a b c : ℝ} {s : Set ℝ}

/-- **Potential drift lemma**.  If `f` is absolutely continuous on `uIcc a b`, `deriv f ≤ 0`
a.e. on `Icc a b`, and `deriv f ≤ -c` on a measurable set `s ⊆ Icc a b` (with `c > 0`),
then the Lebesgue measure of `s` is at most the total drop of `f` over `[a, b]`, divided
by `c`. -/
theorem AbsolutelyContinuousOnInterval.measure_toReal_le_of_deriv_le
    (hab : a ≤ b) (hc : 0 < c)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hle : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), x ∈ Icc a b → deriv f x ≤ 0)
    (hs : MeasurableSet s) (hssub : s ⊆ Icc a b)
    (hbad : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), x ∈ s → deriv f x ≤ -c) :
    (volume s).toReal ≤ (f a - f b) / c := by
  classical
  have hint : IntervalIntegrable (deriv f) volume a b := hf.intervalIntegrable_deriv
  set t₁ : Set ℝ := Ioc a b ∩ s with ht₁
  set t₂ : Set ℝ := Ioc a b \ s with ht₂
  have ht₁meas : MeasurableSet t₁ := measurableSet_Ioc.inter hs
  have ht₂meas : MeasurableSet t₂ := measurableSet_Ioc.diff hs
  have hIocfin : volume (Ioc a b) < ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hfin₁ : volume t₁ ≠ ∞ :=
    ne_of_lt ((measure_mono inter_subset_left).trans_lt hIocfin)
  have hint₁ : IntegrableOn (deriv f) t₁ volume :=
    hint.1.mono inter_subset_left (le_refl _)
  have hint₂ : IntegrableOn (deriv f) t₂ volume :=
    hint.1.mono Set.sdiff_subset (le_refl _)
  have hconst₁ : IntegrableOn (fun _ : ℝ => (-c : ℝ)) t₁ volume :=
    integrableOn_const hfin₁ (by simp)
  -- The complement piece is nonpositive
  have hle₂ : ∀ᵐ (x : ℝ) ∂volume, x ∈ t₂ → 0 ≤ -deriv f x := by
    filter_upwards [hle] with x hx hxt₂
    have hxle := hx (Ioc_subset_Icc_self (ht₂ ▸ hxt₂).1)
    linarith
  have h₂ : ∫ x in t₂, deriv f x ∂volume ≤ 0 := by
    have hneg : 0 ≤ ∫ x in t₂, -deriv f x ∂volume :=
      setIntegral_nonneg_of_ae_restrict ((ae_restrict_iff' ht₂meas).mpr hle₂)
    have heq : ∫ x in t₂, -deriv f x ∂volume = -∫ x in t₂, deriv f x ∂volume :=
      integral_neg (deriv f) (μ := volume.restrict t₂)
    linarith
  -- The fast-drift piece is ≤ `-(volume t₁).toReal * c`
  have h₁ : ∫ x in t₁, deriv f x ∂volume ≤ -((volume t₁).toReal * c) := by
    have hmonoI : ∫ x in t₁, deriv f x ∂volume ≤ ∫ x in t₁, (-c : ℝ) ∂volume := by
      refine setIntegral_mono_on_ae hint₁ hconst₁ ht₁meas ?_
      filter_upwards [hbad] with x hxb hxt₁
      exact hxb (ht₁ ▸ hxt₁).2
    have hconstI : ∫ x in t₁, (-c : ℝ) ∂volume = -((volume t₁).toReal * c) := by
      rw [setIntegral_const, Measure.real, smul_eq_mul]
      ring
    linarith
  -- Reassemble the total drop via the fundamental theorem of calculus
  have hFTC : ∫ (x : ℝ) in a..b, deriv f x ∂volume = f b - f a :=
    hf.integral_deriv_eq_sub
  have hunion : t₁ ∪ t₂ = Ioc a b := by
    ext x
    simp only [ht₁, ht₂, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  have hsplit : ∫ (x : ℝ) in a..b, deriv f x ∂volume
      = ∫ x in t₁, deriv f x ∂volume + ∫ x in t₂, deriv f x ∂volume := by
    have hdisj : Disjoint t₁ t₂ := by
      rw [Set.disjoint_iff]
      intro x hx
      simp only [ht₁, ht₂, Set.mem_inter_iff, Set.mem_sdiff] at hx
      exact hx.2.2 hx.1.2
    rw [intervalIntegral.integral_of_le hab, ← hunion,
      setIntegral_union hdisj ht₂meas hint₁ hint₂]
  have key : (volume t₁).toReal * c ≤ f a - f b := by linarith
  -- `volume s = volume t₁` since `s \ t₁ ⊆ {a}`
  have hmeas_eq : volume s = volume t₁ := by
    have hset : s = t₁ ∪ (s ∩ {a}) := by
      ext x
      simp only [ht₁, mem_union, mem_inter_iff, mem_Ioc, mem_singleton_iff]
      constructor
      · intro hxs
        rcases eq_or_ne x a with rfl | hxa
        · exact Or.inr ⟨hxs, rfl⟩
        · exact Or.inl ⟨⟨lt_of_le_of_ne (hssub hxs).1 (Ne.symm hxa), (hssub hxs).2⟩, hxs⟩
      · rintro (⟨⟨_, _⟩, hxs⟩ | ⟨hxs, _⟩)
        · exact hxs
        · exact hxs
    have hdisj₂ : Disjoint t₁ (s ∩ {a}) := by
      rw [Set.disjoint_iff]
      intro x hx
      simp only [ht₁, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨hax, -⟩, -⟩, -, -, rfl⟩
      exact lt_irrefl a hax
    rw [hset, measure_union hdisj₂ (hs.inter (measurableSet_singleton a)),
      measure_mono_null Set.inter_subset_right Real.volume_singleton, add_zero]
  rw [hmeas_eq]
  exact (le_div_iff₀ hc).mpr key

/-- **Potential drift lemma, monotone form**.  If `f` is absolutely continuous and antitone on
`[a, b]`, and `deriv f ≤ -c` (with `c > 0`) on a measurable set `s ⊆ [a, b]`, then the Lebesgue
measure of `s` is at most the total drop of `f` over `[a, b]`, divided by `c`. -/
theorem AbsolutelyContinuousOnInterval.measure_toReal_le_of_deriv_le_of_antitoneOn
    (hab : a ≤ b) (hc : 0 < c)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hanti : AntitoneOn f (Icc a b))
    (hs : MeasurableSet s) (hssub : s ⊆ Icc a b)
    (hbad : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), x ∈ s → deriv f x ≤ -c) :
    (volume s).toReal ≤ (f a - f b) / c := by
  have hdiff : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), x ∈ uIcc a b → DifferentiableAt ℝ f x :=
    hf.ae_differentiableAt
  have hioo : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), x ∈ Ioo a b → deriv f x ≤ 0 := by
    filter_upwards [hdiff] with x hxd hx
    have hmem : Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    rw [← derivWithin_of_mem_nhds hmem]
    exact hanti.derivWithin_nonpos
  have hle : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), x ∈ Icc a b → deriv f x ≤ 0 := by
    rw [ae_iff]
    refine measure_mono_null
      (t := {x | ¬(x ∈ Ioo a b → deriv f x ≤ 0)} ∪ {a, b}) (fun x hx => ?_) ?_
    · have hx' := not_imp.mp hx
      by_cases hxb : x < b
      · by_cases hax : a < x
        · exact Or.inl (not_imp.mpr ⟨⟨hax, hxb⟩, hx'.2⟩)
        · exact Or.inr (by simp [le_antisymm (le_of_not_gt hax) hx'.1.1])
      · exact Or.inr (by simp [le_antisymm hx'.1.2 (le_of_not_gt hxb)])
    · simp only [Set.insert_eq]
      exact measure_union_null (ae_iff.mp hioo)
        (measure_union_null Real.volume_singleton Real.volume_singleton)
  exact measure_toReal_le_of_deriv_le hab hc hf hle hs hssub hbad

/-- **Escape-time corollary** (potential budget over escape rate).  Let `f` be an antitone
potential on the half-line `Ici 0` that is absolutely continuous on every `Icc 0 T` and
nonnegative there, and let `s` be a measurable set on which `deriv f ≤ -c` (with `c > 0`)
holds a.e.  Then for every horizon `T`, the Lebesgue measure of the "bad time" `s ∩ Icc 0 T`
is at most the initial potential `f 0` divided by the escape rate `c`. -/
theorem AbsolutelyContinuousOnInterval.measure_toReal_inter_Icc_le_of_deriv_le_of_antitoneOn
    {f : ℝ → ℝ} {c : ℝ} {s : Set ℝ} {T : ℝ}
    (hc : 0 < c)
    (hs : MeasurableSet s)
    (hfT : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T)
    (hanti : AntitoneOn f (Ici 0))
    (hfnn : ∀ x ∈ Ici 0, 0 ≤ f x)
    (hbad : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), x ∈ s → deriv f x ≤ -c) :
    (volume (s ∩ Icc 0 T)).toReal ≤ f 0 / c := by
  by_cases hT : 0 ≤ T
  · have hbad' : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), x ∈ s ∩ Icc 0 T → deriv f x ≤ -c := by
      filter_upwards [hbad] with x hxb hx
      exact hxb hx.1
    have hmain := measure_toReal_le_of_deriv_le_of_antitoneOn
      (f := f) (a := 0) (b := T) (c := c) (s := s ∩ Icc 0 T) hT hc (hfT T hT)
      (hanti.mono fun _ hx => hx.1) (hs.inter measurableSet_Icc) Set.inter_subset_right hbad'
    have h0T : 0 ≤ f T := hfnn T hT
    have h1 : f 0 - f T ≤ f 0 - 0 := by linarith
    exact hmain.trans
      ((div_le_div_of_nonneg_right h1 hc.le).trans_eq (by simp))
  · have hempty : s ∩ Icc 0 T = ∅ := by
      rw [Icc_eq_empty hT]
      simp
    rw [hempty]
    have h0 : (volume (∅ : Set ℝ)).toReal = 0 := by simp
    rw [h0]
    exact div_nonneg (hfnn 0 (by simp)) hc.le

end DriftLemma
