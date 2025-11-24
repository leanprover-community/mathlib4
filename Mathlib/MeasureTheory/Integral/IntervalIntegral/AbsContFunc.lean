/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Gaps
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

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
absolutely continuous, fundamental theorem of calculus, integration by parts
-/

@[expose] public section

open MeasureTheory Set Filter Function AbsolutelyContinuousOnInterval

open scoped Topology

/-- If `f` has derivative `f'` a.e. on `[d, b]` and `η` is positive, then there is a collection of
pairwise disjoint closed subintervals of `[a, b]` of total length `b - a` where the slope of `f`
on each subinterval `[x, y]` differs from `f' x` by at most `η`. -/
lemma ae_hasDerivAt_exists_slope_pairwiseDisjoint_hasSum_sub_sub {f f' : ℝ → ℝ} {d b η : ℝ}
    (hdb : d ≤ b) (hf : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f (f' x) x) (hη : 0 < η) :
    ∃ u : Set (ℝ × ℝ),
      (∀ z ∈ u, (d < z.1 ∧ z.1 < z.2 ∧ z.2 < b) ∧ dist (slope f z.1 z.2) (f' z.1) < η) ∧
      u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2) ∧
      HasSum (fun (z : u) ↦ z.val.2 - z.val.1) (b - d) := by
  -- Proof idea: Use `Vitali.exists_disjoint_covering_ae'` to get a Vitali cover of `[a, b]`
  -- consisting of closed subintervals `[x, y]` on which the slope of `f` differs from `f' x` by
  -- at most `η`.
  by_cases hdb : d = b
  · use ∅
    simp [hdb]
  replace hdb : d < b := by grind
  replace hf : ∀ᵐ x, x ∈ Ioo d b → HasDerivAt f (f' x) x := by
    filter_upwards [hf] with x hx1 hx2
    exact hx1 (Ioo_subset_Icc_self hx2)
  let t := {z : ℝ × ℝ | (d < z.1 ∧ z.1 < z.2 ∧ z.2 < b) ∧ dist (slope f z.1 z.2) (f' z.1) < η}
  let s := {x : ℝ | x ∈ Ioo d b ∧ HasDerivAt f (f' x) x}
  have : ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2) ∧
      volume (s \ ⋃ z ∈ u, Icc z.1 z.2) = 0 := by
    apply Vitali.exists_disjoint_covering_ae' volume s t 6 (Prod.snd - Prod.fst) Prod.fst
      (fun z ↦ Icc z.1 z.2)
    · simp only [Icc, Metric.closedBall, Real.dist_eq, Pi.sub_apply, abs_le', tsub_le_iff_right,
      sub_add_cancel, neg_sub, setOf_subset_setOf, and_imp, Prod.forall]
      intros; constructor <;> linarith
    · intro A hA
      simp only [Pi.sub_apply, Real.volume_closedBall, ENNReal.coe_ofNat, Real.volume_Icc]
      rw [show 6 = ENNReal.ofReal 6 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_le_ofReal_iff (by simp only [mem_setOf_eq, t] at hA; linarith)]
      linarith
    · simp +contextual [t]
    · simp [isClosed_Icc]
    · intro x hx
      apply Eventually.frequently
      have := hasDerivAt_iff_tendsto_slope.mp hx.right
      simp only at this
      obtain ⟨δ, hδ₁, hδ₂⟩ := (Metric.tendsto_nhdsWithin_nhds).mp
        (hasDerivAt_iff_tendsto_slope.mp hx.right) η hη
      have evn_bound {α : ℝ} (hα : 0 < α) : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, ε < α := by
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
        refine ⟨Ioo (-α) α, by grind, isOpen_Ioo, by grind⟩
      have evn_pos : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, 0 < ε :=
        eventually_mem_of_tendsto_nhdsWithin (fun _ a ↦ a)
      filter_upwards [evn_pos, evn_bound hη, evn_bound hδ₁,
                      @evn_bound ((b - x) / 2) (by simp [hx.left.right])]
        with ε hε₁ hε₂ hε₃ hε₄
      use (x, x + ε)
      repeat' constructor
      · exact hx.left.left
      · linarith
      · linarith
      · apply hδ₂
        · grind
        · simp [abs_eq_self.mpr hε₁.le, hε₃]
      · simp
  obtain ⟨u, ⟨hu₁, hu₂, hu₃, hu₄⟩⟩ := this
  simp only [t, Set.subset_def, mem_setOf_eq] at hu₁
  refine ⟨u, ⟨hu₁, hu₃, ?_⟩⟩
  have : Countable u := by simp [hu₂]
  have : Pairwise (Disjoint on fun (z : u) ↦ Icc z.val.1 z.val.2) :=
    fun z₁ z₂ hz₁z₂ ↦ hu₃ z₁.prop z₂.prop (Subtype.coe_ne_coe.mpr hz₁z₂)
  replace hu₄ : volume (Ioo d b \ ⋃ z ∈ u, Icc z.1 z.2) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem] at hu₄ ⊢
    filter_upwards [hf, hu₄] with x hx₁ hx₂
    grind
  have vol_sum : volume (⋃ z : u, Icc z.val.1 z.val.2) = ENNReal.ofReal (b - d) := by
    convert Real.volume_Ioo ▸
      measure_eq_measure_of_null_diff (by simp only [iUnion_subset_iff]; grind) hu₄
      using 2
    simp
  rw [measure_iUnion this (by simp)] at vol_sum
  simp_rw [Real.volume_Icc] at vol_sum
  apply_fun fun x ↦ x.toReal at vol_sum
  rw [ENNReal.tsum_toReal_eq (by simp), ENNReal.toReal_ofReal (by linarith),
      ← Summable.hasSum_iff (by rw [tsum_def] at vol_sum; grind)] at vol_sum
  convert vol_sum with z
  rw [ENNReal.toReal_ofReal]
  linarith [hu₁ z.val z.prop]

/-- If `f` is absolutely continuous on `[d, b]` and there is a collection of pairwise disjoint
closed subintervals of `[d, b]` of total length `b - d` such that the sum of `dist (f x) (f y)` for
`[x, y]` in the collection is equal to `y`, then `dist (f b) (f d) ≤ y`. -/
lemma AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum {f : ℝ → ℝ} {d b y : ℝ}
    (hdb : d ≤ b) (hf : AbsolutelyContinuousOnInterval f d b) {u : Set (ℝ × ℝ)}
    (hu₁ : ∀ z ∈ u, d < z.1 ∧ z.1 < z.2 ∧ z.2 < b)
    (hu₂ : u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2))
    (hu₃ : HasSum (fun (z : u) ↦ z.val.2 - z.val.1) (b - d))
    (hu₄ : HasSum (fun (z : u) ↦ dist (f z.val.1) (f z.val.2)) y) :
    dist (f d) (f b) ≤ y := by
  -- Proof idea: The complement of the collection of subintervals of `[d, b]` encoded in `u` can
  -- be approached by the complement of subcollections encoded by finite subsets `s ⊆ u`. The
  -- complement of finite subcollections are intervals encoded using `Finset.intervalGapsWithin`.
  -- Their total length tends to `0` as `s` tends to `u` and by absolute continuity of `f`, the sum
  -- of `dist (f x) (f y)` for `[x, y]` in the complement tends to `0` as `s` tends to `u`. Finally
  -- we use the traingle inequality of `dist` to obtain the result.
  let u_coe (s : Finset u) : Finset (ℝ × ℝ) := s.image Subtype.val
  replace hu₁ (s : Finset u) : ∀ ⦃z : ℝ × ℝ⦄, z ∈ u_coe s → d ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := by
    intro z hz
    have := hu₁ z (by grind)
    grind
  replace hu₂ (s : Finset u) : (SetLike.coe (u_coe s)).PairwiseDisjoint fun z ↦ Icc z.1 z.2 :=
    hu₂.subset (by grind)
  let T (s : Finset u) := ((u_coe s).card + 1, (u_coe s).intervalGapsWithin d b)
  have hT₁ (s : Finset u) (i : ℕ) := (u_coe s).intervalGapsWithin_le_fst (hu₁ s) i
  have hT₂ (s : Finset u) (i : ℕ) :=
    (u_coe s).intervalGapsWithin_fst_le_snd hdb (hu₁ s) (hu₂ s) i
  have hT₃ (s : Finset u) (i : ℕ) := (u_coe s).intervalGapsWithin_snd_le (hu₁ s) i
  have hT₄ (s : Finset u) := (u_coe s).intervalGapsWithin_pairwiseDisjoint_Ioc (hu₁ s)
  have hT : univ.MapsTo T (disjWithin d b) := by
    intro s _
    simp only [disjWithin, Finset.mem_range, Finset.coe_range, mem_setOf_eq, T]
    constructor
    · simp only [uIcc_of_le hdb, mem_Icc]
      grind
    · convert hT₄ s using 2 with _ i
      exact uIoc_of_le (hT₂ s i)
  have u_coe_sum (s : Finset u) (g : ℝ → ℝ → ℝ) :
      ∑ b ∈ s, (g b.val.1 b.val.2) = ∑ z ∈ u_coe s, (g z.1 z.2) :=
    Finset.sum_nbij Subtype.val (by simp [u_coe]) (by simp)
      (by simp only [Finset.coe_image, u_coe]; tauto) (by simp)
  replace hu₃ : Tendsto T atTop (totalLengthFilter ⊓ 𝓟 (disjWithin d b)) := by
    refine tendsto_inf.mpr ⟨?_, hT.tendsto.mono_left (by simp)⟩
    simp only [totalLengthFilter, tendsto_comap_iff]
    convert hu₃.const_sub (b - d) with s
    · simp only [comp_apply]
      rw [Finset.sum_congr rfl (g := fun i ↦ ((T s).2 i).2 - ((T s).2 i).1)
            (fun i hi ↦ by rw [dist_comm, Real.dist_eq, abs_of_nonneg (by grind)])]
      convert (u_coe s).sum_intervalGapsWithin_eq_sub_sub_sum id
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
    rw [dist_comm, Finset.sum_congr rfl fun i hi ↦ dist_comm (f ((T s).2 i).1) _,
        Finset.sum_congr rfl fun (b : ℝ × ℝ) hb ↦ dist_comm (f b.1) _]
    simp_rw [Real.dist_eq]
    rw [← (u_coe s).sum_intervalGapsWithin_add_sum_eq_sub]
    grw [abs_add_le, Finset.abs_sum_le_sum_abs, Finset.abs_sum_le_sum_abs]
  exact le_of_tendsto_of_tendsto' (by simp) sum_tendsto dist_le_sum

/-- If `f` is absolutely continuous on `uIcc a b` and `f' x = 0` for a.e. `x ∈ uIcc a b`, then `f`
-- is constant on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_deriv_zero_const {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hf₀ : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f 0 x) :
    ∃ C, ∀ x ∈ uIcc a b, f x = C := by
  -- Proof idea : Assume wlog `a < b`. We need to show that `f d = f b` for any `d ∈ [a, b]`.
  -- Fix `d`. It suffices to show that `dist (f d) (f b) ≤ r` for any `r > 0`. Fix `r`.
  -- Use `ae_hasDerivAt_exists_slope_pairwiseDisjoint_hasSum_sub_sub` with `η = r / (b - d)` to
  -- get a cover of `[d, b]` consisting of closed subintervals with total length `b - d` such that
  -- the slope of `f` on each subinterval has absolute value `≤ η`. The sum of `dist (f x) (f y)`
  -- for `[x, y]` in the cover must therefore be `≤ (b - d) * η = r`. Use
  -- `AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum` to conclude that
  -- `dist (f d) (f b) ≤ r`.
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ @this f b a hf.symm (uIcc_comm a b ▸ hf₀) (by linarith)
  suffices ∀ x ∈ uIcc a b, f x = f b by use f b
  rw [uIcc_of_le hab] at hf₀ ⊢
  intro d hd
  suffices ∀ r > 0, dist (f d) (f b) ≤ r by
    contrapose! this
    exact exists_between (dist_pos.mpr this)
  intro r hr
  rw [mem_Icc] at hd
  have had : a ≤ d := by linarith
  by_cases hdb₀ : d = b
  · simp [hdb₀, hr.le]
  have hdb : d < b := by grind
  replace hf₀ : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f 0 x := by
    filter_upwards [hf₀] with x hx1 hx2
    apply hx1
    suffices Icc d b ⊆ Icc a b from this hx2
    gcongr
  have hfdb': 0 < r / (b - d) := by apply div_pos <;> linarith
  have ⟨u, hu₁, hu₂, hu₃⟩ :=
    ae_hasDerivAt_exists_slope_pairwiseDisjoint_hasSum_sub_sub hd.right hf₀ hfdb'
  let g := fun (z : u) ↦ dist (f z.val.1) (f z.val.2)
  have g_nonneg : 0 ≤ g := by intro; simp [g]
  have g_finsum_bound (s : Finset u) : ∑ z ∈ s, g z ≤ r := by
    have (z : u) (hz : z ∈ s) : g z ≤ r / (b - d) * (z.val.2 - z.val.1) := by
      have slope_bound := hu₁ z (by simp) |>.right |>.le
      have : 0 < z.val.2 - z.val.1 := by linarith [hu₁ z (by simp)]
      simp only [Real.dist_eq, slope, vsub_eq_sub, smul_eq_mul, sub_zero, abs_mul,
        abs_inv] at slope_bound
      rwa [inv_mul_le_iff₀' (abs_pos_of_pos this), abs_of_pos this, abs_sub_comm] at slope_bound
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
  grind

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
      with x hx1 hx2 hx3
    convert (hx1 hx3).hasDerivAt.sub (hx2 hx3 a (by simp))
    abel
  obtain ⟨C, hC⟩ := g_ac.ae_deriv_zero_const g_ae_deriv_zero
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
  have hx₄ : x ∈ uIcc a b := by grind [uIcc, uIoc]
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
