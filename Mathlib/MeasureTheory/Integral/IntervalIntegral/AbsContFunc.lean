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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

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

open MeasureTheory Set Filter Function AbsolutelyContinuousOnInterval

open scoped Topology ENNReal Interval NNReal

/-- If `f` is interval integrable on `a..b` and `c ∈ uIcc a b`, then `fun x ↦ ∫ v in c..x, f v` is
absolute continuous on `uIcc a b`. -/
theorem IntervalIntegrable.integral_absolutelyContinuousOnInterval {f : ℝ → ℝ} {a b c : ℝ}
    (h : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have : Tendsto (⇑(volume.restrict (uIoc a b)) ∘ s) (totalLengthFilter ⊓ 𝓟 (disjWithin a b))
      (𝓝 0) := by
    rw [(hasBasis_totalLengthFilter.inf_principal _).tendsto_iff ENNReal.nhds_zero_basis_Iic]
    intro ε hε
    by_cases hε_top : ε = ⊤
    · exact ⟨1, by simp, by simp[hε_top]⟩
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

/-- If `f` has derivative 0 a.e. on `[d, b]`, then there is a coultable Vitali cover of `[d, b]`
a.e., consisting of closed intervals, where each has small variations wrt `f`. -/
lemma ae_deriv_zero_ctb_cover {f : ℝ → ℝ} {d b η : ℝ}
    (hf : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f 0 x) (hη : 0 < η) :
    let t := {(x, h) : ℝ × ℝ | d < x ∧ 0 < h ∧ x + h < b ∧ |f (x + h) - f x| < h * η};
    let B : ℝ × ℝ → Set ℝ := fun (x, h) ↦ Icc x (x + h);
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧ volume (Ioo d b \ ⋃ a ∈ u, B a) = 0 := by
  intro t B
  replace hf : ∀ᵐ x, x ∈ Ioo d b → HasDerivAt f 0 x := by
    filter_upwards [hf] with x hx1 hx2
    exact hx1 (Ioo_subset_Icc_self hx2)
  let s := {x : ℝ | x ∈ Ioo d b ∧ HasDerivAt f 0 x}
  have : ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧ volume (s \ ⋃ a ∈ u, B a) = 0 := by
    apply Vitali.exists_disjoint_covering_ae' volume s t 6 (Prod.snd) (Prod.fst) B
    · simp only [Icc, Metric.closedBall, Real.dist_eq, abs_le', tsub_le_iff_right, neg_sub,
      setOf_subset_setOf, and_imp, Prod.forall, B]
      intros; constructor <;> linarith
    · intro A hA
      simp only [Real.volume_closedBall, ENNReal.coe_ofNat, Real.volume_Icc, add_sub_cancel_left, B]
      rw [show 6 = ENNReal.ofReal 6 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_le_ofReal_iff (by simp only [mem_setOf_eq, t] at hA; linarith)]
      linarith
    · simp +contextual [B, t]
    · simp [B, isClosed_Icc]
    · intro x hx
      apply Filter.Eventually.frequently
      have := hasDerivAt_iff_tendsto.mp hx.right
      simp only [Real.norm_eq_abs, smul_eq_mul, mul_zero, sub_zero] at this
      obtain ⟨δ, hδ₁, hδ₂⟩ := (Metric.tendsto_nhds_nhds).mp (hasDerivAt_iff_tendsto.mp hx.2) η hη
      have evn_bound {α : ℝ} (hα : 0 < α) : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, ε < α := by
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
        refine ⟨Ioo (-α) α, by grind, isOpen_Ioo, by grind⟩
      have evn_pos : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, 0 < ε :=
        eventually_mem_of_tendsto_nhdsWithin (fun _ a ↦ a)
      filter_upwards [evn_pos, evn_bound hη, evn_bound hδ₁,
                      @evn_bound ((b - x) / 2) (by simp [hx.left.right])]
        with ε hε₁ hε₂ hε₃ hε₄
      use (x, ε)
      repeat' constructor
      · exact hx.left.left
      · exact hε₁
      · linarith
      · specialize @hδ₂ (x := x + ε) (by simp [abs_eq_self.mpr hε₁.le, hε₃])
        simp only [add_sub_cancel_left, Real.norm_eq_abs, smul_eq_mul, mul_zero, sub_zero,
          dist_zero_right, norm_mul, norm_inv, abs_abs] at hδ₂
        rw [abs_eq_self.mpr hε₁.le, ← mul_lt_mul_iff_right₀ hε₁] at hδ₂
        convert hδ₂ using 1
        field_simp
  obtain ⟨u, ⟨hu₁, hu₂, hu₃, hu₄⟩⟩ := this
  refine ⟨u, ⟨hu₁, hu₂, hu₃, ?_⟩⟩
  rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hu₄ ⊢
  filter_upwards [hf, hu₄] with x hx₁ hx₂
  grind

/-- If `f` has derivative 0 a.e. on `[d, b]`, then there is a finite Vitali cover of `[d, b]`
except for measure at most `δ`, consisting of closed intervals, where each has small variations
wrt `f`. -/
lemma ae_deriv_zero_fin_cover {f : ℝ → ℝ} {d b η δ : ℝ}
    (hf : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f 0 x)
    (hη : 0 < η) (hδ : 0 < δ) :
    let t := {(x, h) : ℝ × ℝ | d < x ∧ 0 < h ∧ x + h < b ∧ |f (x + h) - f x| < h * η};
    let B : ℝ × ℝ → Set ℝ := fun (x, h) ↦ Icc x (x + h);
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
    exact ⟨fun ⟨h1, h2⟩ i ↦ by constructor <;> simp +contextual [h1, h2],
           fun h ↦ ⟨(h 0).left, fun x hx ↦ (h (e x + 1)).right x hx (by omega)⟩⟩
  rw [this] at hu4
  rw [MeasureTheory.measure_iInter_eq_iInf_measure_iInter_le] at hu4
  · clear this
    replace hu4 := hu4.symm ▸
      (show @OfNat.ofNat ℝ≥0∞ 0 Zero.toOfNat0 < ENNReal.ofReal δ by simp [hδ])
    obtain ⟨n, hn⟩ := iInf_lt_iff.mp hu4
    classical
    let enum := (Finset.equivFin {j ∈ Finset.range n | ∃ x ∈ u, e x = j}).symm
    set n' := Finset.card ({j ∈ Finset.range n | ∃ x ∈ u, e x = j})
    have hvi {i : ℕ} (hi : i < n') : ∃ x ∈ u, e x = enum ⟨i, hi⟩ := by
      have := (enum ⟨i, hi⟩).property
      simp only [Finset.mem_filter, Finset.mem_range] at this
      tauto
    let v (i : ℕ) : ℝ × ℝ := if hi : i < n' then Classical.choose (hvi hi) else (0, 0)
    have v_prop {i : ℕ} (hi : i < n') : v i ∈ u ∧ e (v i) = enum ⟨i, hi⟩ := by
      simp only [hi, ↓reduceDIte, v]
      exact Classical.choose_spec (hvi hi)
    refine ⟨n', v, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.coe_range, mem_image, mem_Iio] at hz
      obtain ⟨i, hi1, hi2⟩ := hz
      exact hi2 ▸ hu1 (v_prop hi1).left
    · intro i hi j hj hij
      have hi1 := v_prop (Finset.mem_range.mp hi)
      have hj1 := v_prop (Finset.mem_range.mp hj)
      apply hu3 hi1.left hj1.left
      intro hC
      have := Fin.mk.inj_iff.mp <| Equiv.injective enum <| Subtype.eq <| hj1.right ▸ hC ▸ hi1.right
      tauto
    · convert hn
      ext x
      simp only [Finset.mem_range, mem_diff, mem_iUnion, exists_prop, not_exists, not_and,
        mem_setOf_eq, mem_iInter, and_imp]
      constructor
      · intro ⟨hx1, hx2⟩ j hj
        refine ⟨by assumption, fun y hy1 hy2 ↦ ?_⟩
        have hy : e y ∈ {j ∈ Finset.range n | ∃ x ∈ u, e x = j} := by
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by use y⟩
        let i := enum.symm ⟨e y, hy⟩
        have hi : i < n' := i.isLt
        have : y = v i := by
          have : e y = enum i := by simp [i]
          exact he hy1 (v_prop hi).left (this ▸ (v_prop hi).right.symm)
        exact this.symm ▸ hx2 i hi
      · intro hx
        refine ⟨hx 0 (by omega) |>.left, fun i hi ↦ ?_⟩
        have := v_prop hi
        apply hx n (by omega) |>.right (v i)
        · tauto
        · rw [this.right]
          set j := enum ⟨i, hi⟩
          have := j.property
          simp only [Finset.mem_filter, Finset.mem_range] at this
          exact this.left
  · intro i
    dsimp only [B]
    apply NullMeasurableSet.diff (by measurability)
    exact NullMeasurableSet.biUnion (hu2.mono (by simp)) (by measurability)
  · use 0
    have : volume (Ioo d b) ≠ ∞ := by simp
    intro hC
    apply measure_mono_top (s₂ := Ioo d b) (by simp) at hC
    tauto

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
      exact ⟨i, List.mem_range.mp hi, rfl⟩
    simpa using this
  let r_list := @Finset.sort (Finset.range n) (fun (i j) ↦ (v i).1 ≤ (v j).1) _
    { trans := by intros; linarith }
    { antisymm := by
        intro i j h1 h2
        have hij: (v i).1 = (v j).1 := by linarith
        have := hv2 i.property j.property
        contrapose this
        push_neg
        refine ⟨Subtype.coe_ne_coe.mpr this, ?_⟩
        simp only [not_disjoint_iff, mem_Icc]
        exact ⟨(v i).1, ⟨by simp, by linarith [hv1 i.val i.property]⟩,
               ⟨by assumption, by linarith [hv1 j.val j.property]⟩⟩ }
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
    exact ⟨i, by rwa [Finset.mem_range], by simp [r, hi, h]⟩
  let v' (i : ℕ) : (ℝ × ℝ) := v (r i)
  refine ⟨n, v', ?_, ?_, ?_⟩
  · intro i hi
    simp only [v']
    exact hv1 _ (r_mem hi)
  · intro i hi j hj hij
    have hi1 : i + 1 ∈ Finset.range n := by rw [Finset.mem_range] at hj ⊢; omega
    simp only [v']
    suffices (v (r i)).1 + (v (r i)).2 < (v (r (i + 1))).1 by
      have : (v (r (i + 1))).1 ≤ (v (r j)).1 := by apply r_mono <;> assumption
      exact lt_of_lt_of_le (by assumption) this
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
  · rw [MeasureTheory.measure_diff, MeasureTheory.measure_biUnion_finset] at hv3
    · simp only [Real.volume_Icc, Real.volume_Ioo, add_sub_cancel_left] at hv3
      have : ∑ i ∈ Finset.range n, (v' i).2 = ∑ x ∈ Finset.range n, (v x).2 := by
        dsimp only [v']
        symm
        have : Finset.range n = Finset.image r (Finset.range n) := by
          ext k; simp only [Finset.mem_image]
          exact ⟨fun hk ↦ r_surj hk, fun ⟨_, hi1, hi2⟩ ↦ hi2 ▸ r_mem hi1⟩
        nth_rw 1 [this]
        apply Finset.sum_image (g := r)
        dsimp only [InjOn]
        intro i hi j hj; contrapose!; exact r_inj hi hj
      rw [this]
      have : ∀ i ∈ Finset.range n, 0 ≤ (v i).2 := by intro i hi; linarith [hv1 i hi]
      rw [← ENNReal.ofReal_sum_of_nonneg this,
          ← ENNReal.ofReal_sub (hq := Finset.sum_nonneg this)] at hv3
      exact (ENNReal.ofReal_lt_ofReal_iff hδ1).mp hv3
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
  induction n with
  | zero => simp
  | succ n ih =>
    have : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [this, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    nth_rw 2 [Finset.sum_range_succ]
    nth_rw 3 [Finset.sum_range_succ]
    rw [this]
    abel

/-- If `f` is absolutely continuous on `uIcc a b` and `f' x = 0` for a.e. `x ∈ uIcc a b`, then `f`
is constant on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_deriv_zero_const {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hf1 : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f 0 x) :
    ∃ C, ∀ x ∈ uIcc a b, f x = C := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ @this f b a hf.symm (uIcc_comm a b ▸ hf1) (by linarith)
  suffices ∀ x ∈ uIcc a b, f x = f b by use f b
  by_contra hC
  push_neg at hC
  obtain ⟨d, hd1, hd2⟩ := hC
  rw [uIcc_of_le hab, mem_Icc] at hd1
  have had : a ≤ d := by linarith
  have hdb : d < b := lt_of_le_of_ne hd1.right fun hC ↦ hd2 (congrArg f hC)
  rw [absolutelyContinuousOnInterval_iff] at hf
  have hfdb: 0 < |f d - f b| / 2 := by
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right, abs_pos, ne_eq]
    rwa [sub_eq_zero]
  obtain ⟨δ, hδ1, hδ2⟩ := hf (|f d - f b| / 2) hfdb
  simp only [AbsolutelyContinuousOnInterval.disjWithin, mem_setOf_eq] at hδ2
  simp_rw [uIcc_of_le hab] at hf1 hδ2 ⊢
  replace hf1 : ∀ᵐ x, x ∈ Icc d b → HasDerivAt f 0 x := by
    filter_upwards [hf1] with x hx1 hx2
    apply hx1
    suffices Icc d b ⊆ Icc a b from this hx2
    gcongr
  have hfdb': 0 < |f d - f b| / (2 * (b - d)) := by apply div_pos <;> linarith
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
  have hI3 {i : ℕ} (hi : i ∈ Finset.range n) : (I (i + 1)).1 = (v i).1 + (v i).2 := by
    have := Finset.mem_range.mp hi
    dsimp only [I]
    split_ifs
    any_goals omega
    any_goals contradiction
    all_goals simp
  have hI4 {i : ℕ} (hi : i ∈ Finset.range n) : (I i).2 = (v i).1 := by
    have := Finset.mem_range.mp hi
    dsimp only [I]
    split_ifs
    all_goals simp
  have hI5 {i : ℕ} (hi : i ∈ Finset.range (n + 1)) : a ≤ (I i).1 ∧ (I i).1 ≤ (I i).2 ∧ (I i).2 ≤ b
      := by
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
          exact ⟨by linarith, by linarith, by linarith⟩
    · simp only [hi1, ↓reduceIte, I]
      · by_cases hn : i = n ∧ 0 < n
        · simp only [hn, and_self, ↓reduceIte, le_refl, and_true]
          constructor <;> linarith [hv1 (n - 1) (by rw [Finset.mem_range]; omega)]
        · simp only [hn, ↓reduceIte, le_refl, and_true, had, hd1.right]
  have hI6 {i : ℕ} (hi : i ∈ Finset.range (n + 1)) : (I i).1 ∈ Icc a b ∧ (I i).2 ∈ Icc a b := by
    simp only [mem_Icc]
    repeat' constructor
    all_goals linarith [hI5 hi]
  have hI7 {i j : ℕ} (hi : i ∈ Finset.range (n + 1)) (hj : j ∈ Finset.range (n + 1))
      (hij : i < j) : (I i).2 ≤ (I j).1:= by
    have hv2' {i j : ℕ} (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range n) (hij : i ≤ j) :
      (v i).1 ≤ (v j).1 := by
      by_cases hij0 : i = j
      · rw [hij0]
      · linarith [hv2 i hi j hj (by omega), hv1 i hi]
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    have hin : i < n + 1 := Finset.mem_range.mp hi
    replace hin : i < n := by omega
    simp only [hin, ↓reduceIte, I]
    have (a : ℝ) (ha : 0 < a) : 0 ≤ a := le_of_lt ha
    split_ifs <;> (simp only; try omega)
    all_goals try apply le_add_of_le_of_nonneg
    all_goals try refine le_of_lt (hv1 _ ?_).right.left
    all_goals try refine hv2' ?_ ?_ ?_
    all_goals try rw [Finset.mem_range]
    all_goals omega
  let r (i : ℕ) : ℝ := if Even i then (I (i / 2)).1 else (I (i / 2)).2
  have hr1 (i : ℕ) : r (2 * i) = (I i).1 := by simp [r]
  have hr2 (i : ℕ) : r (2 * i + 1) = (I i).2 := by
    simp only [Nat.not_even_bit1, ↓reduceIte, r]
    congr; omega
  have hrd : d = r 0 := by rw [show 0 = 2 * 0 by rfl, hr1, hI1]
  have hrb : b = r (2 * n + 1) := by rw [hr2, hI2]
  have h_dist_sum : ∑ i ∈ Finset.range (n + 1), dist (I i).1 (I i).2 =
      b - d - ∑ i ∈ Finset.range n, (v i).2 := by
    rw [fun a b c ↦ show a = b - c ↔ b = a + c by grind]
    calc
    _ = r (2 * n + 1) - r 0 := by rw [hrd, hrb]
    _ = ∑ k ∈ Finset.range (2 * n + 1), (r (k + 1) - r k) := by rw [← Finset.sum_range_sub]
    _ = ∑ i ∈ Finset.range (n + 1), (r (2 * i + 1) - r (2 * i)) +
        ∑ i ∈ Finset.range n, (r (2 * i + 1 + 1) - r (2 * i + 1)) := by rw [split_sum_even_odd]
    _ = ∑ i ∈ Finset.range (n + 1), dist (I i).1 (I i).2 + ∑ i ∈ Finset.range n, (v i).2 := by
      congr 1 <;> apply Finset.sum_congr rfl
      · intro i hi
        rw [hr1, hr2, Real.dist_eq, abs_eq_neg_self.mpr]
        · abel
        · linarith [hI5 hi]
      · intro i hi
        rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, hr1, hr2, hI3, hI4] <;> try assumption
        abel
  have : ∑ i ∈ Finset.range (n + 1), dist (f (I i).1) (f (I i).2) < |f d - f b| / 2 := by
    refine hδ2 ((n + 1), I) ⟨@hI6, ?_⟩ (by convert hv3 using 1)
    intro i hi j hj hij
    simp only [onFun, uIoc_of_le (hI5 hi).right.left, uIoc_of_le (hI5 hj).right.left]
    by_cases hij1 : i < j
    · exact Ioc_disjoint_Ioc_of_le (hI7 hi hj hij1)
    · exact Ioc_disjoint_Ioc_of_le (hI7 hj hi (by omega)) |>.symm
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
    linarith [hv1 i hi]
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
  have f_deriv_integral_ac := hf.deriv_intervalIntegrable.integral_absolutelyContinuousOnInterval
    (c := a) (by simp)
  let g (x : ℝ) := f x - ∫ (t : ℝ) in a..x, deriv f t
  have g_ac : AbsolutelyContinuousOnInterval g a b := hf.sub (f_deriv_integral_ac)
  have g_ae_deriv_zero : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt g 0 x := by
    filter_upwards [hf.ae_hasDerivAt, hf.deriv_intervalIntegrable.ae_hasDerivAt_integral]
      with x hx1 hx2 hx3
    convert (hx1 hx3).sub (hx2 hx3 a (by simp))
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
  rw [← (hf.mul hg).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hf.ae_hasDerivAt, hg.ae_hasDerivAt] with x hx₁ hx₂ hx₃
  have hx₄ : x ∈ uIcc a b := by grind [uIcc, uIoc]
  have hx₅ := (hx₁ hx₄).mul (hx₂ hx₄)
  exact hx₅.deriv.symm

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
