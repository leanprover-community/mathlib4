/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib

/-!
# Vector valued Stieltjes measure

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

open Filter
open scoped symmDiff Topology NNReal

variable {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]
[CompleteSpace E]

namespace MeasureTheory

set_option linter.unusedVariables false in
/-- The subtype of all measurable sets. We define it as `MeasuredSets μ` to be able to define
a distance on it given by `edist s t = μ (s ∆ t)` -/
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

/-- Consider a finitely additive vector measure on a dense class of measurable sets which is stable
under binary intersection, union and complement. Assume that it is dominated by a finite positive
measure. Then it extends to a countably additive vector measure. -/
lemma VectorMeasure.exists_extension_of_additive_of_le_measure [IsFiniteMeasure μ]
    (C : Set (Set α)) (m : Set α → E)
    (hC : ∀ s ∈ C, MeasurableSet s) (hC_diff : ∀ s ∈ C, ∀ t ∈ C, s \ t ∈ C)
    (hC_inter : ∀ s ∈ C, ∀ t ∈ C, s ∩ t ∈ C)
    (hC_union : ∀ s ∈ C, ∀ t ∈ C, s ∪ t ∈ C)
    (h'C : ∀ t ε, MeasurableSet t → 0 < ε → ∃ s ∈ C, μ (s ∆ t) < ε)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s) (h'm : ∀ s ∈ C, ∀ t ∈ C, Disjoint s t → m (s ∪ t) = m s + m t) :
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
    rw [h'm _ (hC_inter _ (C'C _ t.2) _ (C'C _ s.2)) _ (hC_diff _ (C'C _ t.2) _ (C'C _ s.2))
        Set.disjoint_sdiff_inter.symm,
      h'm _ (hC_inter _ (C'C _ s.2) _ (C'C _ t.2)) _ (hC_diff _ (C'C _ s.2) _ (C'C _ t.2))
        Set.disjoint_sdiff_inter.symm, Set.inter_comm]
    simp only [add_sub_add_left_eq_sub, ge_iff_le]
    apply enorm_sub_le.trans
    gcongr
    · exact hm _ (hC_diff _ (C'C _ s.2) _ (C'C _ t.2))
    · exact hm _ (hC_diff _ (C'C _ t.2) _ (C'C _ s.2))
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
    have s''C : s'' ∈ C := hC_diff _ s'C _ t'C
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
      have s''t'C : s'' ∪ t' ∈ C := hC_union _ s''C _ t'C
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
      rw [h'm _ s''C _ t'C Set.disjoint_sdiff_left]
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


#check Set.PairwiseDisjoint

open Set

/-- Assume that a function is finitely additive on the elements of a set semiring `C`
(i.e. `m (⋃ i, s i) = ∑ i, m (s i)` whenever the `s i` are disjoint elements in `C`
with union in `C`). Then its extension to finite unions of elements of `C` is well defined, i.e.,
it does not depend on the decomposition of a set as such a finite union. -/
lemma glouk (C : Set (Set α)) (hC : IsSetSemiring C) {ι ι' : Type*} (a : Finset ι) (a' : Finset ι')
    (f : ι → Set α) (hfC : ∀ i ∈ a, f i ∈ C) (hfdisj : PairwiseDisjoint a f)
    (f' : ι' → Set α) (hf'C : ∀ i ∈ a', f' i ∈ C) (hf'disj : PairwiseDisjoint a' f')
    (h : ⋃ i ∈ a, f i = ⋃ i ∈ a', f' i)
    (m : Set α → E)
    (hm : ∀ (b : Finset (Set α)), (∀ s ∈ b, s ∈ C) → PairwiseDisjoint (b : Set (Set α)) id →
      (⋃ s ∈ b, s) ∈ C → m (⋃ s ∈ b, s) = ∑ s ∈ b, m s) :
    ∑ i ∈ a, m (f i) = ∑ i ∈ a', m (f' i) := by
  let g : ι × ι' → Set α := fun p ↦ f p.1 ∩ f' p.2
  have : ∀ p ∈ a ×ˢ a', g p ∈ C := by
    intro p hp
    simp only [Finset.mem_product] at hp
    apply hC.inter_mem _ (hfC _ hp.1) _ (hf'C _ hp.2)
  calc ∑ i ∈ a, m (f i)
  _ = ∑ i ∈ a, (∑ j ∈ a', m (f i ∩ f' j)) := by
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    have : f i = ⋃ j ∈ a', f i ∩ f' j := by
      apply Subset.antisymm _ (by simp)
      intro x hx
      have A : x ∈ ⋃ j ∈ a', f' j := by
        rw [← h]
        simp only [mem_iUnion, exists_prop]
        exact ⟨i, hi, hx⟩
      simpa [mem_iUnion, mem_inter_iff, exists_and_left, exists_prop, hx] using A
    nth_rewrite 1 [this]










#exit
