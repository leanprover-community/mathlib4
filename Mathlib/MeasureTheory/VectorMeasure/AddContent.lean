/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!
# Constructing a vector measure from an additive content

Consider a content defined on a semiring of sets. We investigate in this file
whether it is possible to extend it to a (countably additive) vector measure on the whole
sigma-algebra. We show that this is possible when the content is dominated by a finite
measure, see `exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom`.
-/

@[expose] public section

open MeasurableSpace
open scoped symmDiff

namespace MeasureTheory.VectorMeasure

variable {α : Type*} {hα : MeasurableSpace α} {E : Type*} [NormedAddCommGroup E]
[CompleteSpace E] {μ : Measure α}

/-- A finitely additive vector measure which is dominated by a finite positive measure is in
fact countably additive. -/
def of_additive_of_le_measure
    (m : Set α → E) (hm : ∀ s, ‖m s‖ₑ ≤ μ s) [IsFiniteMeasure μ]
    (h'm : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t)
    (h''m : ∀ s, ¬ MeasurableSet s → m s = 0) : VectorMeasure α E where
  measureOf' := m
  empty' := by simpa using h'm ∅ ∅ MeasurableSet.empty MeasurableSet.empty (by simp)
  not_measurable' := h''m
  m_iUnion' f f_meas f_disj := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm]; swap
    · simp only [← toReal_enorm]
      apply ENNReal.summable_toReal
      apply ne_of_lt
      calc ∑' i, ‖m (f i)‖ₑ
      _ ≤ ∑' i, μ (f i) := by gcongr; apply hm
      _ = μ (⋃ i, f i) := (measure_iUnion f_disj f_meas).symm
      _ < ⊤ := measure_lt_top μ (⋃ i, f i)
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp_rw [norm_sub_rev, ← toReal_enorm, ← ENNReal.toReal_zero]
    apply (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    have A n : m (⋃ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range n, m (f i) := by
      induction n with
      | zero => simpa using h'm ∅ ∅ MeasurableSet.empty MeasurableSet.empty (by simp)
      | succ n ih =>
        simp only [Finset.range_add_one]
        rw [Finset.sum_insert (by simp)]
        simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
        rw [h'm _ _ (f_meas n), ih]
        · exact Finset.measurableSet_biUnion _ (fun i hi ↦ f_meas i)
        · simp only [Finset.mem_range, Set.disjoint_iUnion_right]
          intro i hi
          exact f_disj hi.ne'
    have B n : m (⋃ i, f i) = m (⋃ i ∈ Finset.range n, f i) + m (⋃ i ∈ Set.Ici n, f i) := by
      have : ⋃ i, f i = (⋃ i ∈ Finset.range n, f i) ∪ (⋃ i ∈ Set.Ici n, f i) := by
        ext; simp; grind
      rw [this]
      apply h'm
      · exact Finset.measurableSet_biUnion _ (fun i hi ↦ f_meas i)
      · exact MeasurableSet.biUnion (Set.to_countable _) (fun i hi ↦ f_meas i)
      · simp only [Finset.mem_range, Set.mem_Ici, Set.disjoint_iUnion_right,
          Set.disjoint_iUnion_left]
        intro i hi j hj
        exact f_disj (hj.trans_le hi).ne
    have C n : m (⋃ i, f i) - ∑ i ∈ Finset.range n, m (f i) = m (⋃ i ∈ Set.Ici n, f i) := by
      rw [B n, A]; simp
    simp only [C]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun n ↦ μ (⋃ i ∈ Set.Ici n, f i)) ?_ (fun i ↦ bot_le) (fun i ↦ hm _)
    exact tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (fun i ↦ (f_meas i).nullMeasurableSet) f_disj

open scoped ENNReal

/-- Consider an additive content on a dense ring of sets. Assume that it is dominated by a finite
positive measure. Then it extends to a countably additive vector measure. -/
lemma exists_extension_of_isSetRing_of_le_measure_of_dense [IsFiniteMeasure μ]
    {C : Set (Set α)} {m : AddContent E C} (hC : IsSetRing C)
    (hCmeas : ∀ s ∈ C, MeasurableSet s) (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : ∀ t ε, MeasurableSet t → 0 < ε → ∃ s ∈ C, μ (s ∆ t) < ε) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  /- We will extend by continuity the function `m` from the class `C` to all measurable sets,
  thanks to the fact that `C` is dense. To implement this properly, we work in the space
  `MeasuredSets μ` with the distance `edist s t = μ (s ∆ t)`. The assumptions guarantee that
  `m` is Lipschitz on `C` there, and therefore extends to a Lipschitz function. We check that
  the extension is still finitely additive by approximating disjoint measurable sets by disjoint
  measurable sets in `C`. Moreover, the extension is still dominated by `μ`.
  The countable additivity follows from these two properties and
  Lemma `VectorMeasure.of_additive_of_le_measure`. -/
  classical
  -- Express things inside `MeasuredSets μ`.
  let C' : Set (MeasuredSets μ) := {s | ∃ c ∈ C, s = c}
  have C'C (s : MeasuredSets μ) (hs : s ∈ C') : (s : Set α) ∈ C := by
    rcases hs with ⟨t, ht, rfl⟩; exact ht
  have C'_dense : Dense C' := by
    simp only [Dense, EMetric.mem_closure_iff, gt_iff_lt]
    intro x ε εpos
    rcases h'C x ε x.2 εpos with ⟨s, sC, hs⟩
    refine ⟨⟨s, hCmeas s sC⟩, ⟨s, sC, rfl⟩, ?_⟩
    rw [edist_comm]
    exact hs
  /- Let `m₀` be the function `m` expressed on the subtype of `MeasuredSets μ` made of
  elements of `C`. -/
  let m₀ : C' → E := fun x ↦ m x
  -- It is Lipschitz continuous
  have lip : LipschitzWith 1 m₀ := by
    intro s t
    have : edist s t = edist (s : MeasuredSets μ) t := rfl
    simp only [ENNReal.coe_one, one_mul, this, MeasuredSets.edist_def, m₀, edist_eq_enorm_sub]
    rw [measure_symmDiff_eq (by exact s.1.2.nullMeasurableSet) (by exact t.1.2.nullMeasurableSet)]
    have Is : ((s : Set α) ∩ t) ∪ (s \ t) = (s : Set α) := Set.inter_union_diff _ _
    have It : ((t : Set α) ∩ s) ∪ (t \ s) = (t : Set α) := Set.inter_union_diff _ _
    nth_rewrite 1 [← Is]
    nth_rewrite 3 [← It]
    rw [addContent_union hC (hC.inter_mem (C'C _ t.2) (C'C _ s.2))
        (hC.diff_mem (C'C _ t.2) (C'C _ s.2)) Set.disjoint_sdiff_inter.symm,
      addContent_union hC (hC.inter_mem (C'C _ s.2) (C'C _ t.2))
        (hC.diff_mem (C'C _ s.2) (C'C _ t.2)) Set.disjoint_sdiff_inter.symm, Set.inter_comm]
    simp only [add_sub_add_left_eq_sub, ge_iff_le]
    apply enorm_sub_le.trans
    gcongr
    · exact hm _ (hC.diff_mem (C'C _ s.2) (C'C _ t.2))
    · exact hm _ (hC.diff_mem (C'C _ t.2) (C'C _ s.2))
  -- Let `m₁` be the extension of `m₀` to all elements of `MeasuredSets μ` by continuity
  let m₁ : MeasuredSets μ → E := C'_dense.extend m₀
  -- It is again Lipschitz continuous and bounded by `μ`
  have m₁_lip : LipschitzWith 1 m₁ := C'_dense.lipschitzWith_extend lip
  have hBound : ∀ s, ‖m₁ s‖ₑ ≤ μ s := by
    have : IsClosed {s | ‖m₁ s‖ₑ ≤ μ s} :=
      isClosed_le m₁_lip.continuous.enorm MeasuredSets.continuous_measure
    have : Dense {s | ‖m₁ s‖ₑ ≤ μ s} := by
      apply C'_dense.mono
      intro s hs
      simp only [Set.mem_setOf_eq]
      convert hm s (C'C s hs)
      exact C'_dense.extend_eq lip.continuous ⟨s, hs⟩
    simpa only [Dense, IsClosed.closure_eq, Set.mem_setOf_eq] using this
  /- Most involved technical step: show that the extension `m₁` of `m₀` is still finitely
  additive. -/
  have hAddit (s t : MeasuredSets μ) (h : Disjoint (s : Set α) t) :
      m₁ ⟨s ∪ t, s.2.union t.2⟩ = m₁ s + m₁ t := by
    suffices ∀ ε > 0, ‖m₁ (⟨s ∪ t, s.2.union t.2⟩) - m₁ s - m₁ t‖ₑ < ε by
      rw [← sub_eq_zero, ← enorm_eq_zero, sub_add_eq_sub_sub]
      exact eq_bot_iff.2 (le_of_forall_gt this)
    intro ε εpos
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ 8 * δ = ε :=
      ⟨ε / 8, (ENNReal.div_pos εpos.ne' (by simp)), ENNReal.mul_div_cancel (by simp) (by simp)⟩
    -- approximate `s` and `t` up to `δ` by sets `s'` and `t'` in `C`.
    obtain ⟨s', s'C, hs'⟩ : ∃ s' ∈ C, μ (s' ∆ s) < δ := h'C _ _ s.2 δpos
    obtain ⟨t', t'C, ht'⟩ : ∃ t' ∈ C, μ (t' ∆ t) < δ := h'C _ _ t.2 δpos
    have It : ‖m t' - m₁ t‖ₑ < δ := by
      have : m₁ ⟨t', hCmeas _ t'C⟩ = m t' :=
        C'_dense.extend_eq lip.continuous ⟨⟨t', hCmeas _ t'C⟩, ⟨t', t'C, rfl⟩⟩
      rw [← this, ← edist_eq_enorm_sub]
      apply (m₁_lip _ _).trans_lt
      simp only [ENNReal.coe_one, MeasuredSets.edist_def, one_mul]
      exact ht'
    -- `s'` and `t'` have no reason to be disjoint, but their intersection has small measure
    have hμ' : μ (s' ∩ t') < 2 * δ := calc
      μ (s' ∩ t')
      _ ≤ μ (s ∩ t ∪ (s' ∆ s) ∪ (t' ∆ t)) := measure_mono (by grind)
      _ = μ ((s' ∆ s) ∪ (t' ∆ t)) := by simp [Set.disjoint_iff_inter_eq_empty.mp h]
      _ ≤ μ (s' ∆ s) + μ (t' ∆ t) := measure_union_le _ _
      _ < δ + δ := by gcongr
      _ = 2 * δ := by ring
    -- Therefore, the set `s'' := s' \ t'` still approximates well the original set `s`, it belongs
    -- to `C`, and moreover `s''` and `t'` are disjoint.
    let s'' := s' \ t'
    have s''C : s'' ∈ C := hC.diff_mem s'C t'C
    have hs'' : μ (s'' ∆ s) < 3 * δ := calc
      μ (s'' ∆ s)
      _ ≤ μ (s'' ∆ s') + μ (s' ∆ s) := measure_symmDiff_le _ _ _
      _ < 2 * δ + δ := by gcongr; simp [s'', symmDiff, hμ']
      _ = 3 * δ := by ring
    have Is : ‖m s'' - m₁ s‖ₑ < 3 * δ := by
      have : m₁ ⟨s'', hCmeas _ s''C⟩ = m s'' :=
        C'_dense.extend_eq lip.continuous ⟨⟨s'', hCmeas _ s''C⟩, ⟨s'', s''C, rfl⟩⟩
      rw [← this, ← edist_eq_enorm_sub]
      apply (m₁_lip _ _).trans_lt
      simp only [ENNReal.coe_one, MeasuredSets.edist_def, one_mul]
      exact hs''
    -- `s'' ∪ t'` also approximates well `s ∪ t`.
    have Ist : ‖m (s'' ∪ t') - m₁ ⟨s ∪ t, s.2.union t.2⟩‖ₑ < 4 * δ := by
      have s''t'C : s'' ∪ t' ∈ C := hC.union_mem s''C t'C
      have : m₁ ⟨s'' ∪ t', hCmeas _ s''t'C⟩ = m (s'' ∪ t') :=
        C'_dense.extend_eq lip.continuous ⟨⟨s'' ∪ t', hCmeas _ s''t'C⟩, ⟨s'' ∪ t', s''t'C, rfl⟩⟩
      rw [← this, ← edist_eq_enorm_sub]
      apply (m₁_lip _ _).trans_lt
      simp only [ENNReal.coe_one, MeasuredSets.edist_def, one_mul]
      change μ ((s'' ∪ t') ∆ (s ∪ t)) < 4 * δ
      calc μ ((s'' ∪ t') ∆ (s ∪ t))
      _ ≤ μ (s'' ∆ s ∪ t' ∆ t) := measure_mono (Set.union_symmDiff_union_subset ..)
      _ ≤ μ (s'' ∆ s) + μ (t' ∆ t) := measure_union_le _ _
      _ < 3 * δ + δ := by gcongr
      _ = 4 * δ := by ring
    -- conclusion: to estimate `m₁ (s ∪ t) - m₁ s - m₁ t`, replace it up to a small error by
    -- `m₁ (s'' ∪ t') - m₁ s'' - m₁ t'`, which is zero as `m₁` is additive on `C` and these
    -- two sets are disjoint
    calc ‖m₁ (⟨s ∪ t, s.2.union t.2⟩) - m₁ s - m₁ t‖ₑ
    _ = ‖(m (s'' ∪ t') - m s'' - m t') + (m₁ ⟨s ∪ t, s.2.union t.2⟩ - m (s'' ∪ t'))
          + (m s'' - m₁ s) + (m t' - m₁ t)‖ₑ := by abel_nf
    _ ≤ ‖m (s'' ∪ t') - m s'' - m t'‖ₑ + ‖m₁ ⟨s ∪ t, s.2.union t.2⟩ - m (s'' ∪ t')‖ₑ
          + ‖m s'' - m₁ s‖ₑ + ‖m t' - m₁ t‖ₑ := enorm_add₄_le
    _ = ‖m₁ ⟨s ∪ t, s.2.union t.2⟩ - m (s'' ∪ t')‖ₑ + ‖m s'' - m₁ s‖ₑ + ‖m t' - m₁ t‖ₑ := by
      rw [addContent_union hC s''C t'C Set.disjoint_sdiff_left]
      simp
    _ < 4 * δ + 3 * δ + δ := by
      gcongr
      rwa [enorm_sub_rev]
    _ = 8 * δ := by ring
    _ = ε := hδ
  -- conclusion of the proof: the function `s ↦ m₁ s` if `s` is measurable, and `0` otherwise,
  -- defines a vector measure satisfying the required properties
  let m' (s : Set α) := if hs : MeasurableSet s then m₁ ⟨s, hs⟩ else 0
  let m'' : VectorMeasure α E := by
    apply VectorMeasure.of_additive_of_le_measure m' (μ := μ)
    · intro s
      by_cases hs : MeasurableSet s
      · simpa [hs, m'] using hBound _
      · simp [hs, m']
    · intro s t hs ht hst
      simp only [hs, ht, MeasurableSet.union, ↓reduceDIte, m']
      exact hAddit ⟨s, hs⟩ ⟨t, ht⟩ hst
    · intro s hs
      simp [m', hs]
  refine ⟨m'', fun s hs ↦ ?_, fun s ↦ ?_⟩
  · change m' s = m s
    simp only [hCmeas s hs, ↓reduceDIte, m']
    exact C'_dense.extend_eq lip.continuous ⟨⟨s, hCmeas _ hs⟩, ⟨s, hs, rfl⟩⟩
  · change ‖m' s‖ₑ ≤ μ s
    by_cases hs : MeasurableSet s
    · simp only [hs, ↓reduceDIte, m']
      exact hBound ⟨s, hs⟩
    · simp [m', hs]

/-- Consider an additive content on a semi-ring of sets whose finite unions are dense. Assume that
it is dominated by a finite positive measure. Then it extends to a countably additive
vector measure. -/
lemma exists_extension_of_isSetSemiring_of_le_measure_of_dense [IsFiniteMeasure μ]
    {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hCmeas : ∀ s ∈ C, MeasurableSet s) (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : ∀ t ε, MeasurableSet t → 0 < ε → ∃ s ∈ supClosure C, μ (s ∆ t) < ε) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  set m₀ : AddContent E (supClosure C) := m.supClosure hC with hm₀
  have A (s) (hs : s ∈ supClosure C) : ‖m₀ s‖ₑ ≤ μ s := by
    rw [hC.mem_supClosure_iff] at hs
    rcases hs with ⟨P, PC⟩
    nth_rewrite 2 [← P.sup_parts]
    rw [hm₀, AddContent.supClosure_apply_finpartition hC _ PC, Finset.sup_set_eq_biUnion,
      measure_biUnion_finset P.disjoint (fun b hb ↦ hCmeas _ (PC hb))]
    apply (enorm_sum_le _ _).trans
    gcongr with t ht
    exact hm _ (PC ht)
  have B (s) (hs : s ∈ supClosure C) : MeasurableSet s := by
    rw [hC.mem_supClosure_iff] at hs
    rcases hs with ⟨P, PC⟩
    rw [← P.sup_parts, Finset.sup_set_eq_biUnion]
    exact Finset.measurableSet_biUnion _ (fun b hb ↦ hCmeas _ (PC hb))
  rcases VectorMeasure.exists_extension_of_isSetRing_of_le_measure_of_dense
    hC.isSetRing_supClosure B A h'C with ⟨m', hm', m'bound⟩
  refine ⟨m', fun s hs ↦ ?_, m'bound⟩
  rw [hm' _ (subset_supClosure hs)]
  exact AddContent.supClosure_apply_of_mem _ _ hs

/-- Consider an additive content `m ` on a semi-ring of sets `C`, which is dominated by a finite
measure `μ`. Assume that `C` generates the sigma-algebra and covers the space up to measure zero.
Then `m` extends to a countably additive vector measure which is dominated by `μ`. -/
private lemma exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom_of_cover
    [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : hα = generateFrom C) (h''C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  apply VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_dense hC ?_ hm ?_
  · intro s hs
    rw [h'C]
    exact measurableSet_generateFrom hs
  · intro t ε ht εpos
    exact exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring hC h''C h'C ht εpos

/-- Consider an additive content `m ` on a semi-ring of sets `C`, which is dominated by a finite
measure `μ`. Assume that `C` generates the sigma-algebra.
Then `m` extends to a countably additive vector measure which is dominated by `μ`. -/
/- TODO: weaken the assumption that `C` generates the sigma-algebra to measurability of all
elements of `C`, once integrals wrt vector measures is available (by composing the integral wrt `m'`
on the generated sigma-algebra, with conditional expectation of the indicator function to project
on the generated sigma-algebra). -/
theorem exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s) (h'C : hα = generateFrom C) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  have M (s) (hs : s ∈ C) : MeasurableSet s := by
    rw [h'C]; exact measurableSet_generateFrom hs
  rcases Measure.exists_ae_subset_biUnion_countable μ M with ⟨D, DC, D_count, hD⟩
  have MD : MeasurableSet (⋃₀ D) := MeasurableSet.sUnion D_count (fun t ht ↦ M _ (DC ht))
  let μ' := μ.restrict (⋃₀ D)
  obtain ⟨m', h, h'⟩ : ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ' s := by
    apply exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom_of_cover hC
      (fun s hs ↦ ?_) h'C ?_
    · exact ⟨D, D_count, DC, by simp [μ', Measure.restrict_apply' MD]⟩
    · apply (hm s hs).trans
      simp only [Measure.restrict_apply' MD, μ']
      apply measure_mono_ae
      nth_rewrite 1 [← Set.inter_self s]
      exact ae_le_set_inter Filter.EventuallyLE.rfl (hD s hs)
  exact ⟨m', h, fun s ↦ (h' s).trans (Measure.restrict_apply_le (⋃₀ D) s)⟩

end MeasureTheory.VectorMeasure
