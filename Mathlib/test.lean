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
open scoped symmDiff Topology

variable {α : Type*} [MeasurableSpace α] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
[CompleteSpace E]

namespace MeasureTheory

set_option linter.unusedVariables false in
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


lemma exists_extension (C : Set (Set α)) (hC : ∀ s ∈ C, MeasurableSet s) (m : Set α → E)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'm : ∀ s ∈ C, ∀ t ∈ C, Disjoint s t → m (s ∪ t) = m s + m t)
    (hm_diff : ∀ s ∈ C, ∀ t ∈ C, s \ t ∈ C)
    (hm_inter : ∀ s ∈ C, ∀ t ∈ C, s ∩ t ∈ C)
    (h'C : ∀ t ε, MeasurableSet t → 0 < ε → ∃ s ∈ C, μ (s ∆ t) < ε) :
    ∃ m' : VectorMeasure α E, ∀ s ∈ C, m' s = m s ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  let C' : Set (MeasuredSets μ) := {s | ∃ c ∈ C, s = c}
  have C'C (s : MeasuredSets μ) (hs : s ∈ C') : (s : Set α) ∈ C := by
    rcases hs with ⟨t, ht, rfl⟩
    exact ht
  have C'_dense : Dense C' := by
    simp only [Dense, EMetric.mem_closure_iff, gt_iff_lt]
    intro x ε εpos
    rcases h'C x ε x.2 εpos with ⟨s, sC, hs⟩
    refine ⟨⟨s, hC s sC⟩, ⟨s, sC, rfl⟩, ?_⟩
    rw [edist_comm]
    exact hs
  have A {s t : Set α} : Disjoint (s ∩ t) (s \ t) := Set.disjoint_sdiff_inter.symm
  let m₀ : C' → E := fun x ↦ m x
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
    rw [h'm _ (hm_inter _ (C'C _ t.2) _ (C'C _ s.2)) _ (hm_diff _ (C'C _ t.2) _ (C'C _ s.2)) A,
      h'm _ (hm_inter _ (C'C _ s.2) _ (C'C _ t.2)) _ (hm_diff _ (C'C _ s.2) _ (C'C _ t.2)) A,
      Set.inter_comm]
    simp only [add_sub_add_left_eq_sub, ge_iff_le]
    apply enorm_sub_le.trans
    gcongr
    · exact hm _ (hm_diff _ (C'C _ s.2) _ (C'C _ t.2))
    · exact hm _ (hm_diff _ (C'C _ t.2) _ (C'C _ s.2))
  let m₁ : MeasuredSets μ → E := C'_dense.extend m₀
  have m₁_cont : UniformContinuous m₁ := C'_dense.uniformContinuous_extend lip.uniformContinuous
  have B s : ‖m₁ s‖ₑ ≤ μ s := by
    have : IsClosed {s | ‖m₁ s‖ₑ ≤ μ s} :=
      isClosed_le m₁_cont.continuous.enorm MeasuredSets.continuous_measure




  classical
  have A (s : MeasuredSets μ) : Cauchy (map m₀ (𝓝[C'] s)) := by
    have W := LipschitzOnWith.cauchySeq_comp
    apply Metric.cauchy_iff.2 ⟨?_, ?_⟩
    · have : (𝓝[C'] s).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (C'_dense s)
      exact map_neBot
    · intro ε εpos
      simp


  let m' (s : Set α) := if h : MeasurableSet s then limUnder (𝓝[C'] ⟨s, h⟩) (fun t ↦ m t) else 0


#exit
