/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Prod
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Integration by parts for vector measures associated to bounded variation functions

-/


@[expose] public section

open Filter Set MeasureTheory MeasurableSpace MeasureTheory
open scoped Topology NNReal ENNReal

variable {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [CompactIccSpace α] [hα : MeasurableSpace α] [BorelSpace α]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {f : α → E} {g : α → F}

namespace MeasureTheory

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Two vector measures which agree on closed intervals are equal. -/
theorem VectorMeasure.ext_of_Icc {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α]
    (μ ν : VectorMeasure α E) (hμ : ∀ ⦃a b⦄, a ≤ b → μ (Icc a b) = ν (Icc a b)) : μ = ν := by
  rcases isEmpty_or_nonempty α with hα | hα
  · ext s hs
    have : s = ∅ := Subsingleton.elim _ _
    simp [this]
  apply VectorMeasure.ext_of_generateFrom _ _
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Icc α)) (isPiSystem_Icc id id); swap
  · rintro s ⟨l, u, hlu, rfl⟩
    exact hμ hlu
  obtain ⟨u, u_mono, hu⟩ : ∃ u : ℕ → α, Monotone u ∧ Tendsto u atTop atTop :=
    Filter.exists_seq_monotone_tendsto_atTop_atTop _
  obtain ⟨v, v_mono, hv⟩ : ∃ v : ℕ → α, Antitone v ∧ Tendsto v atTop atBot :=
    Filter.exists_seq_antitone_tendsto_atTop_atBot _
  have : ⋃ n, Icc (v n) (u n) = univ := by
    apply eq_univ_iff_forall.2 (fun x ↦ ?_)
    simp only [mem_iUnion, mem_Icc]
    exact ((tendsto_atBot.1 hv x).and (tendsto_atTop.1 hu x)).exists
  rw [← this]
  have M : Monotone (fun n ↦ Icc (v n) (u n)) := by
    intro m n hmn x hx
    grind [Monotone, Antitone]
  apply tendsto_nhds_unique (VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat M (v := μ)
    (fun n ↦ measurableSet_Icc))
  have A a b : μ (Icc a b) = ν (Icc a b) := by
    rcases lt_or_ge b a with hab | hab
    · simp [hab]
    · exact hμ hab
  simp only [A]
  exact VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat M (fun n ↦ measurableSet_Icc)

lemma foo (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    {B : E →L[ℝ] F →L[ℝ] G} :
    (hf.bilinear_comp hg B).vectorMeasure = hf.vectorMeasure.withDensity g.rightLim B.flip
      + hg.vectorMeasure.withDensity f.leftLim B := by
  apply VectorMeasure.ext_of_Icc _ _ (fun a b hab ↦ ?_)



end MeasureTheory
