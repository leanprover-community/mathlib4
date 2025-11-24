/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Order.Interval.Lex

-- import Mathlib.Order.Monotone.Nat
/-!
# Fundamental Theorem of Calculus and Integration by Parts for Absolutely Continuous Functions

This file proves that:
* If `f` is absolutely continuous on `uIcc a b`, then *Fundamental Theorem of Calculus* holds for
`f'` on `a..b`, i.e. `∫ (x : ℝ) in a..b, deriv f x = f b - f a`.
* *Integration by Parts* holds for absolutely continuous functions.

## Implementation notes

We need to prove that `f'` is interval integrable on `a..b` for any monotone function `f`. The
proof uses Fatou's lemma and is proved in `MonotoneOn.deriv_intervalIntegrable`. From this we get
`f'` is interval integrable on `a..b` for BV functions, proved in
`LocallyBoundedVariationOn.deriv_intervalIntegrable`,
and finally for absolutely continuous functions, proved in
`AbsolutelyContinuousOnInterval.deriv_intervalIntegrable`.

## Tags
absolutely continuous, fundamental theorem of calculus, integration by parts
-/

@[expose] public section

open MeasureTheory Set Filter Function AbsolutelyContinuousOnInterval

open scoped Topology ENNReal Interval NNReal

/-- If `f` is interval integrable on `a..b` and `c ∈ uIcc a b`, then `fun x ↦ ∫ v in c..x, f v` is
absolute continuous on `uIcc a b`. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral {f : ℝ → ℝ} {a b c : ℝ}
    (h : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have : Tendsto (⇑(volume.restrict (uIoc a b)) ∘ s) (totalLengthFilter ⊓ 𝓟 (disjWithin a b))
      (𝓝 0) := by
    rw [(hasBasis_totalLengthFilter.inf_principal _).tendsto_iff ENNReal.nhds_zero_basis_Iic]
    intro ε hε
    by_cases hε_top : ε = ⊤
    · exact ⟨1, by simp, by simp [hε_top]⟩
    replace hε := ENNReal.toReal_pos (hε.ne.symm) hε_top
    refine ⟨ε.toReal, hε, fun (n, I) hnI ↦ ?_⟩
    rw [mem_inter_iff] at hnI
    simp only [comp_apply, mem_Iic, s]
    rw [Measure.restrict_eq_self (h := union_subset_of_disjWithin hnI.right)]
    simp only [disjWithin, mem_setOf_eq] at hnI
    obtain ⟨hnI₁, hnI₂, hnI₃⟩ := hnI
    rw [MeasureTheory.measure_biUnion_finset hnI₃ (by simp [uIoc])]
    calc ∑ i ∈ Finset.range n, volume (uIoc (I i).1 (I i).2)
      _ = ∑ i ∈ Finset.range n, ENNReal.ofReal ((dist (I i).1 (I i).2)) := by
        apply Finset.sum_congr rfl
        simp [uIoc, Real.dist_eq, max_sub_min_eq_abs']
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (dist (I i).1 (I i).2)) := by
        simp [ENNReal.ofReal_sum_of_nonneg]
      _ ≤ ENNReal.ofReal ε.toReal :=
        ENNReal.ofReal_lt_ofReal_iff hε |>.mpr hnI₁ |>.le
      _ ≤ ε := ENNReal.ofReal_toReal_le
  have := MeasureTheory.tendsto_setLIntegral_zero
    (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
    (s := s)
    (l := totalLengthFilter ⊓ 𝓟 (disjWithin a b))
    this
  have := ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp this
  refine squeeze_zero' ?_ ?_ this
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [comp_apply, s]
  have : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [this] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_setOf_eq ▸ hnI
  simp only
  rw [← MeasureTheory.integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_uIoc.restrict),
      MeasureTheory.integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [Real.dist_eq,
        intervalIntegral.integral_interval_sub_left
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc])
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
        MeasureTheory.Measure.restrict_restrict_of_subset
          (subset_of_disjWithin hnI (Finset.mem_range.mp hi)),
        intervalIntegral.integral_symm, abs_neg,
        intervalIntegral.abs_intervalIntegral_eq]
    exact abs_integral_le_integral_abs
  · intro i hi
    unfold IntegrableOn
    have h_subset := subset_of_disjWithin hnI (Finset.mem_range.mp hi)
    rw [MeasureTheory.Measure.restrict_restrict_of_subset h_subset]
    exact MeasureTheory.IntegrableOn.mono_set h.def'.norm h_subset |>.integrable

/-- If `f` has derivative `f'` a.e. on `[d, b]` and `η` is positive, then there is a countable
collection of pairwise disjoint closed subinterval of `[a, b]` of total length `b - a` where the
slope of `f` on each subinterval `[x, y]` differs from `f' x` by at most `η`. -/
lemma ae_hasDerivAt_exists_countable_pairwiseDisjoint_tsum_sub_eq_sub {f f' : ℝ → ℝ} {d b η : ℝ}
    (hdb : d ≤ b)
    (hf : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f (f' x) x) (hη : 0 < η) :
    ∃ u : Set (ℝ × ℝ),
      (∀ z ∈ u, (d < z.1 ∧ z.1 < z.2 ∧ z.2 < b) ∧ dist (slope f z.1 z.2) (f' z.1) < η) ∧
      u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2) ∧
      HasSum (fun (z : u) ↦ z.val.2 - z.val.1) (b - d) := by
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
      apply Filter.Eventually.frequently
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
  rw [ENNReal.tsum_toReal_eq (by simp), ENNReal.toReal_ofReal (by linarith)] at vol_sum
  rw [← Summable.hasSum_iff (by rw [tsum_def] at vol_sum; grind)] at vol_sum
  convert vol_sum with z
  rw [ENNReal.toReal_ofReal]
  linarith [hu₁ z.val z.prop]


section IntervalGapsWithin

namespace Finset

variable (F : Finset (ℝ × ℝ)) (a b : ℝ) {i : ℕ}

noncomputable def intervalGapsWithin (i : ℕ) : ℝ × ℝ := (fst, snd) where
  fst := match i with
    | 0 => a
    | i + 1 => if hi : i < F.card then F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl ⟨i, hi⟩ |>.2 else a
  snd := if hi : i < F.card then F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl ⟨i, hi⟩ |>.1 else b

@[simp]
theorem intervalGapsWithin_zero_fst : (F.intervalGapsWithin a b 0).1 = a := by
  simp [intervalGapsWithin, intervalGapsWithin.fst]

@[simp]
theorem intervalGapsWithin_fst_of_card_lt (hi : F.card < i) :
    (F.intervalGapsWithin a b i).1 = a := by
  simp only [intervalGapsWithin, intervalGapsWithin.fst]
  grind

@[simp]
theorem intervalGapsWithin_card_snd : (F.intervalGapsWithin a b F.card).2 = b := by
  simp [intervalGapsWithin, intervalGapsWithin.snd]

@[simp]
theorem intervalGapsWithin_snd_of_card_le (hi : F.card ≤ i) :
    (F.intervalGapsWithin a b i).2 = b := by
  simp only [intervalGapsWithin, intervalGapsWithin.snd]
  grind

@[simp]
theorem intervalGapsWithin_snd_of_card_eq (hi : F.card = i) :
    (F.intervalGapsWithin a b i).2 = b :=
  intervalGapsWithin_snd_of_card_le F a b hi.le

theorem intervalGapsWithin_succ_fst_of_lt_card (hi : i < F.card) :
    (F.intervalGapsWithin a b (i + 1)).1 = (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl ⟨i, hi⟩).2 := by
  simp [intervalGapsWithin, intervalGapsWithin.fst, hi]

theorem intervalGapsWithin_fst_of_zero_lt_le_card (hi₀ : 0 < i) (hi : i ≤ F.card) :
    (F.intervalGapsWithin a b i).1 =
      (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl ⟨i - 1, Nat.sub_one_lt_of_le hi₀ hi⟩).2 := by
  convert F.intervalGapsWithin_succ_fst_of_lt_card a b (i := i - 1) (by omega)
  omega

theorem intervalGapsWithin_snd_of_lt_card (hi : i < F.card) :
    (F.intervalGapsWithin a b i).2 = (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl ⟨i, hi⟩).1 := by
  simp [intervalGapsWithin, intervalGapsWithin.snd, hi]

theorem intervalGapsWithin_mapsTo :
    (Set.Iio F.card).MapsTo
      (fun i ↦ ((F.intervalGapsWithin a b i).2, (F.intervalGapsWithin a b (i + 1)).1)) F := by
  intro i hi
  rw [Set.mem_Iio] at hi
  simp only [hi, intervalGapsWithin_snd_of_lt_card, intervalGapsWithin_succ_fst_of_lt_card]
  convert F.orderEmbOfFin_mem rfl ⟨i, hi⟩ using 1

theorem intervalGapsWithin_injOn :
    (Set.Iio F.card).InjOn
      (fun i ↦ ((F.intervalGapsWithin a b i).2, (F.intervalGapsWithin a b (i + 1)).1)) := by
  intro i hi j hj
  rw [Set.mem_Iio] at hi hj
  simp only [hi, hj, intervalGapsWithin_snd_of_lt_card, intervalGapsWithin_succ_fst_of_lt_card]
  exact fun hij ↦ Fin.ext_iff.mp (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl |>.injective hij)

theorem intervalGapsWithin_surjOn :
    (Set.Iio F.card).SurjOn
      (fun i ↦ ((F.intervalGapsWithin a b i).2, (F.intervalGapsWithin a b (i + 1)).1)) F := by
  intro z hz
  rw [← F.range_orderEmbOfFin rfl (α := ℝ ×ₗ ℝ)] at hz
  obtain ⟨i, hi⟩ := hz
  use i.val, i.prop
  simp [i.prop, intervalGapsWithin_snd_of_lt_card, intervalGapsWithin_succ_fst_of_lt_card, hi]

theorem intervalGapsWithin_le_fst {a b : ℝ} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (i : ℕ) :
    a ≤ (F.intervalGapsWithin a b i).1 := by
  by_cases hi : i = 0 ∨ F.card < i
  · rcases hi with hi | hi <;> simp [hi]
  · have := hFab (F.intervalGapsWithin_mapsTo a b (x := i - 1) (by grind))
    grind

theorem intervalGapsWithin_snd_le {a b : ℝ} (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (i : ℕ) :
    (F.intervalGapsWithin a b i).2 ≤ b := by
  by_cases hi : F.card ≤ i
  · simp [hi]
  · have := hFab (F.intervalGapsWithin_mapsTo a b (x := i) (by grind))
    grind

theorem intervalGapsWithin_fst_le_snd {a b : ℝ} (hab : a ≤ b)
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b)
    (hF : (SetLike.coe F).PairwiseDisjoint (fun z ↦ Set.Icc z.1 z.2)) (i : ℕ) :
    (F.intervalGapsWithin a b i).1 ≤ (F.intervalGapsWithin a b i).2 := by
  by_cases hi : i ≤ F.card
  swap
  · rwa [intervalGapsWithin_fst_of_card_lt _ _ _ (by omega),
      intervalGapsWithin_snd_of_card_le _ _ _ (by omega)]
  by_cases hi₁ : i = 0
  · simp only [hi₁, intervalGapsWithin_zero_fst]
    by_cases hi₂ : F.card = 0
    · simp [hi₂, hab]
    · exact hFab (F.intervalGapsWithin_mapsTo a b (by grind)) |>.left
  · by_cases hi₂ : F.card = i
    · simp only [hi₂.le, intervalGapsWithin_snd_of_card_le]
      convert hFab (F.intervalGapsWithin_mapsTo a b (x := i - 1) (by grind)) |>.right.right using 1
      simp only
      congr
      omega
    · replace hi₂ : i < F.card := by omega
      replace hi₁ : 0 < i := Nat.zero_lt_of_ne_zero hi₁
      simp only [hi₂, hi₁, hi, intervalGapsWithin_snd_of_lt_card,
        intervalGapsWithin_fst_of_zero_lt_le_card]
      set G := F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
      have hi' : (⟨i - 1, by omega⟩ : Fin F.card) < ⟨i, hi₂⟩ := Fin.mk_lt_mk.mpr (by omega)
      have hG : (G ⟨i - 1, by omega⟩).1 ≤ (G ⟨i, hi₂⟩).1 :=
        Prod.Lex.le_iff'.mp (G.monotone hi'.le) |>.left
      have := hF (by simp [G, F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ)])
        (by simp [G, F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ)]) (G.injective.ne hi'.ne)
      contrapose! this
      simp only [Set.not_disjoint_iff, Set.mem_Icc]
      use (G ⟨i, hi₂⟩).1
      have hFabi := hFab (z := G ⟨i, hi₂⟩) (by simp [G, F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ)])
      simp [hFabi, this.le, hG]

theorem intervalGapsWithin_pairwiseDisjoint_Ioc {a b : ℝ}
    (hFab : ∀ ⦃z⦄, z ∈ F → a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b) :
    (Set.Iio (F.card + 1)).PairwiseDisjoint
      (fun i ↦ Set.Ioc (F.intervalGapsWithin a b i).1 (F.intervalGapsWithin a b i).2) := by
  intro i hi j hj hij
  wlog hij' : i < j generalizing i j
  · exact (this hj hi hij.symm (by omega)).symm
  · rw [onFun, Set.disjoint_iff_inter_eq_empty]
    suffices (F.intervalGapsWithin a b i).2 ≤ (F.intervalGapsWithin a b j).1 by grind
    have hi : i < F.card := by grind
    have hj : j - 1 < F.card := by grind
    have hij'' : (⟨i, hi⟩ : Fin F.card) ≤ ⟨j - 1, hj⟩ := Fin.mk_le_mk.mpr (by omega)
    trans (F.intervalGapsWithin a b (j - 1)).2
    · simp only [hi, hj, intervalGapsWithin_snd_of_lt_card]
      exact Prod.Lex.le_iff'.mp (F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl |>.monotone hij'') |>.left
    · have := hFab (intervalGapsWithin_mapsTo F a b (x := j - 1) (by grind))
      grind

end Finset

end IntervalGapsWithin


theorem Finset.sum_intervalGapsWithin_add_sum_eq_sub (F : Finset (ℝ × ℝ)) {a b : ℝ} (g : ℝ → ℝ) :
    ∑ i ∈ Finset.range (F.card + 1),
      (g (F.intervalGapsWithin a b i).2 - g (F.intervalGapsWithin a b i).1) +
    ∑ z ∈ F, (g z.2 - g z.1) = g b - g a := by
  let p := F.intervalGapsWithin a b
  have := Finset.sum_bij (s := Finset.range F.card) (t := F) (g := fun z ↦ g z.2 - g z.1)
    (f := fun i ↦ (g (p (i + 1)).1 - g (p i).2))
    (fun i hi ↦ ((p i).2, (p (i + 1)).1))
    (fun i hi ↦ F.intervalGapsWithin_mapsTo a b (x := i) (by grind))
    (fun i hi j hj hij ↦ F.intervalGapsWithin_injOn a b (by grind) (by grind) hij)
    (fun z hz ↦ by
      obtain ⟨i, hi₁, hi₂⟩ := F.intervalGapsWithin_surjOn a b hz
      exact ⟨i, by grind, hi₂⟩)
    (by simp)
  rw [← this, add_comm, Finset.sum_range_succ, ← add_assoc,
      ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun _ _ ↦ sub_add_sub_cancel _ _ _),
      Finset.sum_range_sub (fun i ↦ g (F.intervalGapsWithin a b i).1)]
  simp

theorem Finset.sum_intervalGapsWithin_eq_sub_sub_sum (F : Finset (ℝ × ℝ)) {a b : ℝ} (g : ℝ → ℝ) :
    ∑ i ∈ Finset.range (F.card + 1),
      (g (F.intervalGapsWithin a b i).2 - g (F.intervalGapsWithin a b i).1) =
    g b - g a - ∑ z ∈ F, (g z.2 - g z.1) :=
  eq_sub_iff_add_eq.mpr (F.sum_intervalGapsWithin_add_sum_eq_sub g)

lemma AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum {f : ℝ → ℝ}
    {d b y : ℝ}
    (hdb : d ≤ b) (hf : AbsolutelyContinuousOnInterval f d b)
    {u : Set (ℝ × ℝ)}
    (hu₁ : ∀ z ∈ u, d < z.1 ∧ z.1 < z.2 ∧ z.2 < b)
    (hu₂ : u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2))
    (hu₃ : HasSum (fun (z : u) ↦ z.val.2 - z.val.1) (b - d))
    (hu₄ : HasSum (fun (z : u) ↦ dist (f z.val.1) (f z.val.2)) y) :
    dist (f d) (f b) ≤ y := by
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
    · convert hT₄ s using 2 with i
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

theorem Real.tsum_le_of_sum_le {ι : Type*} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ u : Finset ι, ∑ x ∈ u, f x ≤ c) : ∑' x, f x ≤ c :=
  (summable_of_sum_le hf h).tsum_le_of_sum_le h

/-- If `f` is absolutely continuous on `uIcc a b` and `f' x = 0` for a.e. `x ∈ uIcc a b`, then `f`
-- is constant on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_deriv_zero_const {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hf₀ : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f 0 x) :
    ∃ C, ∀ x ∈ uIcc a b, f x = C := by
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
    ae_hasDerivAt_exists_countable_pairwiseDisjoint_tsum_sub_eq_sub hd.right hf₀ hfdb'
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
theorem AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, f x * deriv g x = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x := by
  rw [← AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hf hg,
      ← intervalIntegral.integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hf.intervalIntegrable_deriv.mul_continuousOn hg.continuousOn).add
      (hg.intervalIntegrable_deriv.continuousOn_mul hf.continuousOn)
  · exact hf.intervalIntegrable_deriv.mul_continuousOn hg.continuousOn
