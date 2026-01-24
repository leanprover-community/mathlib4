/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Vector valued Stieltjes measure associated to a bounded variation function

-/


/-
Stratégie globale :
1 - définir une distance sur les ensembles mesurables, donnée par la mesure de leur différence
symétrique
2 - si `m` est une mesure vectorielle finiment additive sur une classe d'ensembles mesurables
dense, majorée par une mesure finie `μ`, alors elle s'étend aux ensembles mesurables en une mesure
vectorielle dénombrablement additive
3 - Cas particulier pour construire une mesure finiment additive sur une classe d'ensembles assez
grande. On part d'un SetSemiring `C` (par exemple les intervalles semi-ouverts) avec une fonction
additive `m` dessus (i.e., si les `sᵢ` sont tous dans `C`, ainsi que leur union disjointe finie,
alors  `m (⋃ sᵢ) = ∑ i, m (sᵢ)`). Alors `m` s'étend aux unions finies d'éléments de `C` en y restant
additive. Idée : si `c` s'écrit à la fois comme union disjointe des `sᵢ` et des `tⱼ`, il faut voir
que `∑ m (sᵢ) = ∑ m (tⱼ)`. On le réécrit comme `∑ m (sᵢ ∩ tⱼ)` et on somme soit d'abord sur les `i`
soit d'abord sur les `j`.
4 - implémenter ça pour les mesures de Stieltjes, avec `m ((a, b]) = f b - f a` pour `C` la classe
des intervalles semi-ouverts. Alors 3. est satisfait.
-/

@[expose] public section

open Filter Set MeasureTheory MeasurableSpace
open scoped symmDiff Topology NNReal ENNReal

variable {α : Type*} [hα : MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]
[CompleteSpace E]

namespace MeasureTheory

lemma exists_measure_symmDiff_lt_of_generateFrom_isSetRing {α : Type*}
    [mα : MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {C : Set (Set α)}
    (hC : IsSetRing C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ C, μ (t ∆ s) < ε := by
  apply MeasurableSpace.induction_on_inter (C := fun s hs ↦ ∀ (ε : ℝ≥0∞) (hε : 0 < ε),
    ∃ t ∈ C, μ (t ∆ s) < ε) h hC.isSetSemiring.isPiSystem ?_ ?_ ?_ ?_ s hs ε hε
  · intro ε εpos
    exact ⟨∅, hC.empty_mem, by simp [εpos]⟩
  · intro s hs ε εpos
    exact ⟨s, hs, by simp [εpos]⟩
  · intro s hs h's ε εpos
    obtain ⟨t, tC, ht⟩ : ∃ t ∈ C, μ (t ∆ s) < ε / 2 := h's _ (ENNReal.half_pos εpos.ne')
    obtain ⟨t', t'C, ht'⟩ : ∃ t' ∈ C, μ (t'ᶜ) < ε / 2 := by
      obtain ⟨D, D_count, DC, hD, Dne⟩ :
          ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0 ∧ D.Nonempty := by
        rcases h'C with ⟨D, D_count, DC, hD⟩
        refine ⟨D ∪ {∅}, D_count.union (by simp), ?_⟩
        simp only [union_subset_iff, DC, singleton_subset_iff, true_and, and_true, hC.empty_mem]
        simp only [union_singleton, sUnion_insert, empty_union, insert_nonempty, and_true, hD]
      obtain ⟨f, hf⟩ : ∃ f : ℕ → Set α, D = Set.range f := Set.Countable.exists_eq_range D_count Dne
      have fC n : Set.accumulate f n ∈ C := hC.accumulate_mem (fun n ↦ DC (by simp [hf])) n
      have : Tendsto (fun n ↦ μ (Set.accumulate f n)ᶜ) atTop (𝓝 0) := by
        have : ⋃₀ D = ⋃ n, Set.accumulate f n := by simp [hf, iUnion_accumulate]
        rw [show (⋃₀ D)ᶜ = ⋂ n, (Set.accumulate f n)ᶜ by simp [this]] at hD
        rw [← hD]
        apply tendsto_measure_iInter_atTop (fun i ↦ ?_)
          (fun i j hij ↦ by simpa using monotone_accumulate hij) ⟨0, by simp⟩
        apply MeasurableSet.nullMeasurableSet
        rw [h]
        exact (measurableSet_generateFrom (fC i)).compl
      obtain ⟨n, hn⟩ : ∃ n, μ (accumulate f n)ᶜ < ε / 2 :=
        ((tendsto_order.1 this).2 _ (ENNReal.half_pos εpos.ne')).exists
      exact ⟨accumulate f n, fC n, hn⟩
    refine ⟨t' \ t, hC.diff_mem t'C tC, ?_⟩
    calc μ ((t' \ t) ∆ sᶜ)
      _ ≤ μ (t ∆ s ∪ t'ᶜ) := by gcongr; grind
      _ ≤ μ (t ∆ s) + μ (t'ᶜ) := measure_union_le _ _
      _ < ε / 2 + ε / 2 := by gcongr
      _ = ε := ENNReal.add_halves ε
  · intro f f_disj f_meas hf ε εpos
    rcases ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos εpos.ne').ne' ℕ with ⟨δ, δpos, hδ⟩
    have A i : ∃ t ∈ C, μ (t ∆ (f i)) < δ i := hf i _ (δpos i)
    choose! t tC ht using A
    have : Tendsto (fun n ↦ μ (⋃ i ∈ Ici n, f i)) atTop (𝓝 0) :=
      tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun i ↦ (f_meas i).nullMeasurableSet) f_disj
    obtain ⟨n, hn⟩ : ∃ n, μ (⋃ i ∈ Ici n, f i) < ε / 2 :=
      ((tendsto_order.1 this).2 _ (ENNReal.half_pos εpos.ne')).exists
    refine ⟨⋃ i ∈ Finset.range n, t i, hC.biUnion_mem _ (fun i hi ↦ tC _), ?_⟩
    calc μ ((⋃ i ∈ Finset.range n, t i) ∆ (⋃ i, f i))
    _ ≤ μ ((⋃ i ∈ Finset.range n, (t i) ∆ (f i)) ∪ ⋃ i ∈ Ici n, f i) := by
      gcongr
      intro x hx
      simp only [Finset.mem_range, mem_symmDiff, mem_iUnion, exists_prop, not_exists, not_and,
        mem_Ici, mem_union] at hx ⊢
      grind
    _ ≤ ∑ i ∈ Finset.range n, μ (t i ∆ f i) + μ (⋃ i ∈ Ici n, f i) := by
      apply (measure_union_le _ _).trans
      gcongr
      apply measure_biUnion_finset_le
    _ ≤ ∑ i ∈ Finset.range n, δ i + μ (⋃ i ∈ Ici n, f i) := by
      gcongr with i; exact (ht i).le
    _ ≤ ∑' i, δ i + μ (⋃ i ∈ Ici n, f i) := by
      gcongr; exact ENNReal.sum_le_tsum (Finset.range n)
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε :=  ENNReal.add_halves ε

#check  borel_eq_generateFrom_Ioc_le

lemma exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring {α : Type*}
    [mα : MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {C : Set (Set α)}
    (hC : IsSetSemiring C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ C.finiteUnions, μ (t ∆ s) < ε := by
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC.isSetRing_finiteUnions ?_
    ?_ hs hε
  · rcases h'C with ⟨D, D_count, DC, hD⟩
    exact ⟨D, D_count, DC.trans (self_subset_finiteUnions C), hD⟩
  · rw [h]
    apply



#exit

MeasurableSpace.induction_on_inter

set_option linter.unusedVariables false in
/-- The subtype of all measurable sets. We define it as `MeasuredSets μ` to be able to define
a distance on it given by `edist s t = μ (s ∆ t)` -/
@[nolint unusedArguments]
def MeasuredSets (μ : Measure α) : Type _ :=
  {s : Set α // MeasurableSet s}

variable {μ : Measure α}

instance : SetLike (MeasuredSets μ) α where
  coe s := s.1
  coe_injective' := Subtype.coe_injective

instance : PseudoEMetricSpace (MeasuredSets μ) where
  edist s t := μ ((s : Set α) ∆ t)
  edist_self := by simp
  edist_comm := by grind
  edist_triangle s t u := measure_symmDiff_le _ _ _

lemma MeasuredSets.edist_def (s t : MeasuredSets μ) : edist s t = μ ((s : Set α) ∆ t) := rfl

lemma MeasuredSets.continuous_measure : Continuous (fun (s : MeasuredSets μ) ↦ μ s) := by
  apply continuous_iff_continuousAt.2 (fun x ↦ ?_)
  simp only [ContinuousAt]
  rcases eq_top_or_lt_top (μ x) with hx | hx
  · simp only [hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [EMetric.ball_mem_nhds _ zero_lt_one] with y hy
    simp only [EMetric.mem_ball, edist_def] at hy
    contrapose! hy
    simp [measure_symmDiff_eq_top hy.symm hx]
  · apply (ENNReal.hasBasis_nhds_of_ne_top hx.ne).tendsto_right_iff.2 (fun ε εpos ↦ ?_)
    filter_upwards [EMetric.ball_mem_nhds _ εpos] with a ha
    simp only [EMetric.mem_ball, edist_def] at ha
    refine ⟨?_, ?_⟩
    · apply tsub_le_iff_right.mpr
      calc μ x
      _ ≤ μ a + μ (x \ a) := by
        rw [← measure_union Set.disjoint_sdiff_right (by exact x.2.diff a.2)]
        apply measure_mono
        exact Set.diff_subset_iff.mp fun ⦃a_1⦄ a ↦ a
      _ ≤ μ a + μ (a ∆ x) := by
        gcongr
        simp [symmDiff]
      _ ≤ μ a + ε := by
        gcongr
    · calc μ a
      _ ≤ μ x + μ (a \ x) := by
        rw [← measure_union Set.disjoint_sdiff_right (by exact a.2.diff x.2)]
        apply measure_mono
        exact Set.diff_subset_iff.mp fun ⦃a_1⦄ a ↦ a
      _ ≤ μ x + μ (a ∆ x) := by
        gcongr
        simp [symmDiff]
      _ ≤ μ x + ε := by
        gcongr

open scoped ENNReal

/-- A finitely additive vector measure which is dominated by a finite positive measure is in
fact countably additive. -/
def VectorMeasure.of_additive_of_le_measure
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

/-- Consider a finitely additive vector measure on a dense class of measurable sets which is a ring
of sets. Assume that it is dominated by a finite positive measure. Then it extends to a countably
additive vector measure. -/
lemma VectorMeasure.exists_extension_of_isSetRing_of_le_measure_of_dense [IsFiniteMeasure μ]
    {C : Set (Set α)} {m : AddContent E C} (hCs : IsSetRing C)
    (hC : ∀ s ∈ C, MeasurableSet s) (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
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
    refine ⟨⟨s, hC s sC⟩, ⟨s, sC, rfl⟩, ?_⟩
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
    rw [measure_symmDiff_eq]; rotate_left
    · exact s.1.2.nullMeasurableSet
    · exact t.1.2.nullMeasurableSet
    have Is : ((s : Set α) ∩ t) ∪ (s \ t) = (s : Set α) := Set.inter_union_diff _ _
    have It : ((t : Set α) ∩ s) ∪ (t \ s) = (t : Set α) := Set.inter_union_diff _ _
    nth_rewrite 1 [← Is]
    nth_rewrite 3 [← It]
    rw [addContent_union hCs (hCs.inter_mem (C'C _ t.2) (C'C _ s.2))
        (hCs.diff_mem (C'C _ t.2) (C'C _ s.2)) Set.disjoint_sdiff_inter.symm,
      addContent_union hCs (hCs.inter_mem (C'C _ s.2) (C'C _ t.2))
        (hCs.diff_mem (C'C _ s.2) (C'C _ t.2)) Set.disjoint_sdiff_inter.symm, Set.inter_comm]
    simp only [add_sub_add_left_eq_sub, ge_iff_le]
    apply enorm_sub_le.trans
    gcongr
    · exact hm _ (hCs.diff_mem (C'C _ s.2) (C'C _ t.2))
    · exact hm _ (hCs.diff_mem (C'C _ t.2) (C'C _ s.2))
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
      rw [← sub_eq_zero, ← enorm_eq_zero]
      contrapose! this
      exact ⟨‖m₁ ⟨s ∪ t, s.2.union t.2⟩ - (m₁ s + m₁ t)‖ₑ, this.bot_lt, le_of_eq (by abel_nf)⟩
    intro ε εpos
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ 8 * δ = ε :=
      ⟨ε / 8, (ENNReal.div_pos εpos.ne' (by simp)), ENNReal.mul_div_cancel (by simp) (by simp)⟩
    -- approximate `s` and `t` up to `δ` by sets `s'` and `t'` in `C`.
    obtain ⟨s', s'C, hs'⟩ : ∃ s' ∈ C, μ (s' ∆ s) < δ := h'C _ _ s.2 δpos
    obtain ⟨t', t'C, ht'⟩ : ∃ t' ∈ C, μ (t' ∆ t) < δ := h'C _ _ t.2 δpos
    have It : ‖m t' - m₁ t‖ₑ < δ := by
      have : m₁ ⟨t', hC _ t'C⟩ = m t' :=
        C'_dense.extend_eq lip.continuous ⟨⟨t', hC _ t'C⟩, ⟨t', t'C, rfl⟩⟩
      rw [← this, ← edist_eq_enorm_sub]
      apply (m₁_lip _ _).trans_lt
      simp only [ENNReal.coe_one, MeasuredSets.edist_def, one_mul]
      exact ht'
    -- `s'` and `t'` have no reason to be disjoint, but their intersection has small measure
    have I : s' ∩ t' ⊆ s ∩ t ∪ (s' ∆ s) ∪ (t' ∆ t) := by
      intro x ⟨hxs', hxt'⟩
      by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
        simp [hxs, hxt, hxs', hxt', symmDiff]
    have hμ' : μ (s' ∩ t') < 2 * δ := calc
      μ (s' ∩ t')
      _ ≤ μ (s ∩ t ∪ (s' ∆ s) ∪ (t' ∆ t)) := measure_mono I
      _ = μ ((s' ∆ s) ∪ (t' ∆ t)) := by simp [Set.disjoint_iff_inter_eq_empty.mp h]
      _ ≤ μ (s' ∆ s) + μ (t' ∆ t) := measure_union_le _ _
      _ < δ + δ := by gcongr
      _ = 2 * δ := by ring
    -- Therefore, the set `s'' := s' \ t'` still approximates well the original set `s`, it belongs
    -- to `C`, and moreover `s''` and `t'` are disjoint.
    let s'' := s' \ t'
    have s''C : s'' ∈ C := hCs.diff_mem s'C t'C
    have hs'' : μ (s'' ∆ s) < 3 * δ := calc
      μ (s'' ∆ s)
      _ ≤ μ (s'' ∆ s') + μ (s' ∆ s) := measure_symmDiff_le _ _ _
      _ < 2 * δ + δ := by gcongr; simp [s'', symmDiff, hμ']
      _ = 3 * δ := by ring
    have Is : ‖m s'' - m₁ s‖ₑ < 3 * δ := by
      have : m₁ ⟨s'', hC _ s''C⟩ = m s'' :=
        C'_dense.extend_eq lip.continuous ⟨⟨s'', hC _ s''C⟩, ⟨s'', s''C, rfl⟩⟩
      rw [← this, ← edist_eq_enorm_sub]
      apply (m₁_lip _ _).trans_lt
      simp only [ENNReal.coe_one, MeasuredSets.edist_def, one_mul]
      exact hs''
    -- `s'' ∪ t'` also approximates well `s ∪ t`.
    have Ist : ‖m (s'' ∪ t') - m₁ ⟨s ∪ t, s.2.union t.2⟩‖ₑ < 4 * δ := by
      have s''t'C : s'' ∪ t' ∈ C := hCs.union_mem s''C t'C
      have : m₁ ⟨s'' ∪ t', hC _ s''t'C⟩ = m (s'' ∪ t') :=
        C'_dense.extend_eq lip.continuous ⟨⟨s'' ∪ t', hC _ s''t'C⟩, ⟨s'' ∪ t', s''t'C, rfl⟩⟩
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
      rw [addContent_union hCs s''C t'C Set.disjoint_sdiff_left]
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
    simp only [hC s hs, ↓reduceDIte, m']
    exact C'_dense.extend_eq lip.continuous ⟨⟨s, hC _ hs⟩, ⟨s, hs, rfl⟩⟩
  · change ‖m' s‖ₑ ≤ μ s
    by_cases hs : MeasurableSet s
    · simp only [hs, ↓reduceDIte, m']
      exact hBound ⟨s, hs⟩
    · simp [m', hs]

lemma VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_dense [IsFiniteMeasure μ]
    {C : Set (Set α)} {m : AddContent E C} (hCs : IsSetSemiring C)
    (hC : ∀ s ∈ C, MeasurableSet s) (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : ∀ t ε, MeasurableSet t → 0 < ε → ∃ s ∈ C.finiteUnions, μ (s ∆ t) < ε) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  set m₀ : AddContent E C.finiteUnions := m.extendUnion hCs with hm₀
  have A (s) (hs : s ∈ C.finiteUnions) : ‖m₀ s‖ₑ ≤ μ s := by
    rcases hs with ⟨J, JC, Jdisj, rfl⟩
    rw [hm₀, AddContent.extendUnion_eq hCs _ JC Jdisj rfl]
    simp only [Set.sUnion_eq_biUnion, SetLike.mem_coe]
    rw [measure_biUnion_finset (by exact Jdisj) (fun b hb ↦ hC _ (JC hb))]
    apply (enorm_sum_le _ _).trans
    gcongr with s hs
    exact hm _ (JC hs)
  have B : ∀ s ∈ C.finiteUnions, MeasurableSet s := by
    rintro s ⟨J, JC, Jdisj, rfl⟩
    apply MeasurableSet.sUnion J.countable_toSet (fun t ht ↦ hC _ (JC ht))
  rcases VectorMeasure.exists_extension_of_isSetRing_of_le_measure_of_dense
    hCs.isSetRing_finiteUnions B A h'C with ⟨m', hm', m'bound⟩
  refine ⟨m', fun s hs ↦ ?_, m'bound⟩
  rw [hm' _ (Set.self_subset_finiteUnions _ hs)]
  exact AddContent.extendUnion_eq_of_mem _ _ hs

/-- Consider an additive content `m ` on a semi-ring of sets `C`, which is dominated by a finite
measure `μ`. Assume that `C` generates the sigma-algebra and covers the space. Then `m` extends
to a countably additive vector measure, which is dominated by `μ`. -/
theorem VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hCs : IsSetSemiring C)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : hα = generateFrom C) (h''C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  apply VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_dense hCs ?_ hm ?_
  · intro s hs
    rw [h'C]
    exact measurableSet_generateFrom hs
  · intro t ε ht εpos
    exact exists_measure_symmDiff_lt_of_generateFrom hCs h''C h'C ht

end MeasureTheory

open MeasureTheory

namespace BoundedVariationOn

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [SecondCountableTopology α]
  [CompactIccSpace α] [BorelSpace α] [DenselyOrdered α] {f : α → E} {a b : α}

/-- The Stieltjes function associated to a bounded variation function. It is given by
the variation between a base point and the current point of the function `f.rightLim`.
Using right limits ensures the right continuity, which is used to construct Sieltjes measures. -/
@[simps] noncomputable def stieltjesFunctionRightLim
    (hf : BoundedVariationOn f univ) (x₀ : α) : StieltjesFunction α where
  toFun x := variationOnFromTo f.rightLim univ x₀ x
  mono' := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn hf.rightLim.locallyBoundedVariationOn (mem_univ _)
  right_continuous' x := hf.continuousWithinAt_variationOnFromTo_rightLim_Ici

open scoped Classical in
/-- Auxiliary measure used to construct the vector measure associated to a bounded variation
function. This is *not* the total variation of this measure in general, as we need to adjust things
when there is a bot element by adding a Dirac mass there. -/
noncomputable def measureAux
    (hf : BoundedVariationOn f univ) : Measure α :=
  if h : Nonempty α then (hf.stieltjesFunctionRightLim h.some).measure else 0

instance (hf : BoundedVariationOn f univ) : IsFiniteMeasure hf.measureAux := by
  by_cases h : Nonempty α; swap
  · simp only [BoundedVariationOn.measureAux, h, ↓reduceDIte]
    infer_instance
  simp only [BoundedVariationOn.measureAux, h, ↓reduceDIte]
  set x₀ := h.some
  apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
    (C := (eVariationOn f.rightLim univ).toReal) _ (fun x ↦ ?_)
  exact variationOnFromTo.abs_le_eVariationOn hf.rightLim

lemma exists_vectorMeasure_le_measureAux (hf : BoundedVariationOn f univ) :
    ∃ m : VectorMeasure α E, (∀ u v, u ≤ v → m (Set.Ioc u v) = f.rightLim v - f.rightLim u) ∧
      m botSet = 0 ∧ ∀ s, ‖m s‖ₑ ≤ hf.measureAux s := by
  rcases isEmpty_or_nonempty α with h'α | h'α
  · exact ⟨0, by simp⟩
  let m := AddContent.onIoc f.rightLim
  have A : ∀ s ∈ {s | ∃ u v, u ≤ v ∧ s = Ioc u v}, ‖m s‖ₑ ≤ hf.measureAux s := by
    rintro s ⟨u, v, huv, rfl⟩
    rw [AddContent.onIoc_apply huv]
    simp only [BoundedVariationOn.measureAux, h'α, ↓reduceDIte, StieltjesFunction.measure_Ioc,
      BoundedVariationOn.stieltjesFunctionRightLim_apply]
    rw [← variationOnFromTo.add hf.rightLim.locallyBoundedVariationOn
      (mem_univ h'α.some) (mem_univ u) (mem_univ v)]
    simp only [add_sub_cancel_left, variationOnFromTo, huv, ↓reduceIte, univ_inter]
    rw [ENNReal.ofReal_toReal]; swap
    · exact ((eVariationOn.mono _ (subset_univ _)).trans_lt hf.rightLim.lt_top).ne
    rw [← edist_eq_enorm_sub]
    exact eVariationOn.edist_le _ (by grind) (by grind)
  have B : hα = generateFrom {s | ∃ u v, u ≤ v ∧ s = Ioc u v} := by
    borelize α
    convert borel_eq_generateFrom_Ioc_le α using 2
    grind only
  have C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ {s | ∃ u v, u ≤ v ∧ s = Ioc u v}
      ∧ hf.measureAux (⋃₀ D)ᶜ = 0 := by
    obtain ⟨s, s_count, s_dense, s_bot, s_top⟩ :
        ∃ s, s.Countable ∧ Dense s ∧ (∀ (x : α), IsBot x → x ∈ s) ∧ ∀ (x : α), IsTop x → x ∈ s :=
      exists_countable_dense_bot_top α
    let D := {t : Set α | ∃ u v, u ≤ v ∧ t = Ioc u v ∧ u ∈ s ∧ v ∈ s}
    refine ⟨D, ?_, by grind, ?_⟩
    · have : D ⊆ (fun (p : α × α) ↦ Ioc p.1 p.2) '' (s ×ˢ s) := by
        rintro - ⟨u, v, -, rfl, us, vs⟩
        exact mem_image_of_mem (x := (u, v)) _ (by simp [us, vs])
      exact Countable.mono this ((s_count.prod s_count).image _)
    have : (⋃₀ D)ᶜ ⊆ botSet := by
      rw [compl_subset_comm, botSet]
      intro x hx
      simp only [mem_sUnion]
      obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := by
        have : (Iio x).Nonempty := by simpa [IsBot] using hx
        exact s_dense.exists_mem_open isOpen_Iio this
      by_cases h'x : IsTop x
      · exact ⟨Ioc y x, ⟨y, x, hy.le, rfl, ys, s_top _ h'x⟩, ⟨hy, le_rfl⟩⟩
      obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := by
        have : (Ioi x).Nonempty := by simpa [IsTop] using h'x
        exact s_dense.exists_mem_open isOpen_Ioi this
      exact ⟨Ioc y z, ⟨y, z, (hy.trans hz).le, rfl, ys, zs⟩, ⟨hy, hz.le⟩⟩
    exact measure_mono_null this (by simp [measureAux, h'α])
  rcases VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    IsSetSemiring.Ioc A B C with ⟨m', hm', h'm'⟩
  refine ⟨m', fun u v huv ↦ ?_, ?_, h'm'⟩
  · rw [hm']
    · exact AddContent.onIoc_apply huv
    · exact ⟨u, v, huv, rfl⟩
  · apply enorm_eq_zero.1
    apply le_bot_iff.1
    exact (h'm' _).trans (by simp [measureAux, h'α])

open scoped Classical in
/-- The vector measure associated to a bounded variation function `f`, giving mass
`f.rightLim b - f.leftLim a` to closed intervals `[a, b]`, and similarly for other intervals. -/
noncomputable irreducible_def vectorMeasure (hf : BoundedVariationOn f univ) : VectorMeasure α E :=
  hf.exists_vectorMeasure_le_measureAux.choose +
  (if h : ∃ x, IsBot x then VectorMeasure.dirac h.choose (f.rightLim h.choose - f h.choose) else 0)

lemma vectorMeasure_Ioc (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Ioc a b) = f.rightLim b - f.rightLim a := by
  classical
  have A : hf.exists_vectorMeasure_le_measureAux.choose (Ioc a b) =
      f.rightLim b - f.rightLim a :=
    hf.exists_vectorMeasure_le_measureAux.choose_spec.1 a b h
  have B : (if hx : ∃ (x : α), IsBot x then VectorMeasure.dirac hx.choose
      (f.rightLim hx.choose - f hx.choose) else 0) (Ioc a b) = 0 := by
    by_cases hx : ∃ (x : α), IsBot x
    · simp only [hx, ↓reduceDIte]
      rw [VectorMeasure.dirac_apply_of_notMem]
      simp only [mem_Ioc, not_and_or, not_lt, not_le]
      exact Or.inl (hx.choose_spec _)
    · simp [hx]
  simp [vectorMeasure, A, B]

lemma vectorMeasure_singleton (hf : BoundedVariationOn f univ) :
    hf.vectorMeasure {a} = f.rightLim a - f.leftLim a := by
  by_cases ha : IsBot a
  · have h : ∃ x, IsBot x := ⟨a, ha⟩
    have heqa : h.choose = a := by
      have := h.choose_spec
      apply subsingleton_isBot _ h.choose_spec ha
    have A : hf.exists_vectorMeasure_le_measureAux.choose {a} = 0 := by
      rw [← botSet_eq_singleton_of_isBot ha]
      exact hf.exists_vectorMeasure_le_measureAux.choose_spec.2.1
    simp only [vectorMeasure, h, ↓reduceDIte, VectorMeasure.coe_add, Pi.add_apply, A,
      zero_add]
    rw [VectorMeasure.dirac_apply_of_mem (MeasurableSet.singleton a)]
    · simpa only [heqa, sub_right_inj] using (leftLim_eq_of_isBot ha).symm
    · simp [heqa]
  obtain ⟨b, hb⟩ : ∃ b, b < a := by simpa only [IsBot, not_forall, not_le] using ha
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n : ℕ, u n ∈ Ioo b a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto' hb
  replace u_lt_a n : u n < a := (u_lt_a n).2
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
    replace hx : ∀ (i : ℕ), u i < x ∧ x ≤ a := by simpa using hx
    have : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n ↦ hf.vectorMeasure (Ioc (u n) a)) atTop (𝓝 (hf.vectorMeasure {a})) := by
    rw [A]
    apply VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat ?_ (fun n ↦ measurableSet_Ioc)
    exact fun m n hmn ↦ Ioc_subset_Ioc_left (u_mono.monotone hmn)
  have L2 : Tendsto (fun n ↦ hf.vectorMeasure (Ioc (u n) a)) atTop
      (𝓝 (f.rightLim a - f.leftLim a)) := by
    simp_rw [hf.vectorMeasure_Ioc (u_lt_a _).le]
    apply tendsto_const_nhds.sub
    have : Tendsto u atTop (𝓝[<] a) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      u_lim (Eventually.of_forall u_lt_a)
    convert (hf.rightLim.tendsto_leftLim a).comp this using 2
    have : (𝓝[<] a).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' ⟨b, hb⟩]
      exact self_mem_Iic
    exact (leftLim_rightLim (hf.tendsto_leftLim _)).symm
  exact tendsto_nhds_unique L1 L2

lemma vectorMeasure_Icc (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Icc a b) = f.rightLim b - f.leftLim a := by
  rw [← Icc_union_Ioc_eq_Icc le_rfl h, VectorMeasure.of_union (by simp)
    measurableSet_Icc measurableSet_Ioc, Icc_self, hf.vectorMeasure_singleton,
    hf.vectorMeasure_Ioc h]
  simp

theorem vectorMeasure_Ioo (hf : BoundedVariationOn f univ) (h : a < b) :
    hf.vectorMeasure (Ioo a b) = f.leftLim b - f.rightLim a := by
  have := hf.vectorMeasure_Ioc h.le
  rw [← Ioo_union_Icc_eq_Ioc h le_rfl, VectorMeasure.of_union (by simp) measurableSet_Ioo
    measurableSet_Icc, hf.vectorMeasure_Icc le_rfl] at this
  grind

theorem vectorMeasure_Ico (hf : BoundedVariationOn f univ) (h : a ≤ b) :
    hf.vectorMeasure (Ico a b) = f.leftLim b - f.leftLim a := by
  rcases h.eq_or_lt with rfl | h'
  · simp
  rw [← Icc_union_Ioo_eq_Ico le_rfl h', VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioo, hf.vectorMeasure_Icc le_rfl, hf.vectorMeasure_Ioo h']
  abel

end BoundedVariationOn
