/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.CDF

/-!
# Representation of kernels

This file contains results about isolation of kernels randomness. In particular, it shows that,
when the target space is a standard Borel space, any Markov kernel can be represented as the image
of the uniform measure on `[0,1]` by a deterministic map. It corresponds to Lemma 4.22 in
"Foundations of Modern Probability" by Olav Kallenberg, 2021.

## Statements

* `ProbabilityTheory.Kernel.unitInterval_representation`:
  for a Markov kernel `κ : Kernel α I`, there exists a jointly measurable function
  `f : α → I → I` such that for all `a : α`, `volume.map (f a) = κ a`.

* `ProbabilityTheory.Kernel.embedding_representation`:
  for a measurable embedding `g : β → I` and a Markov kernel `κ : Kernel α β`,
  there exists a jointly measurable function `f : α → I → β` such that for all `a : α`,
  `volume.map (f a) = κ a`.

* `ProbabilityTheory.Kernel.representation`:
  for a Markov kernel `κ : Kernel α β` with `β` a standard Borel space,
  there exists a jointly measurable function `f : α → I → β` such that for all `a : α`,
  `volume.map (f a) = κ a`.
  This is a consequence of `ProbabilityTheory.Kernel.embedding_representation` and the fact that
  any standard Borel space can be embedded in `ℝ`, and then composed with `unitInterval.sigmoid`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ENNReal unitInterval Filter Topology Function

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α]

lemma unitInterval_representation (κ : Kernel α I) [IsMarkovKernel κ] :
    ∃ (f : α → I → I), Measurable (uncurry f) ∧ ∀ a, volume.map (f a) = κ a := by
  let f := fun s (t : I) ↦ sSup {x | (κ s).real (Icc 0 x) < t}
  have measurable_f : Measurable (uncurry f) := by
    refine measurable_of_Ioi fun a ↦ ?_
    simp only [preimage, uncurry, mem_Ioi]
    have h_monotone s : Monotone (fun x ↦ (κ s).real (Icc 0 x)) := by
      intro x y hxy
      suffices h : Icc 0 x ⊆ Icc 0 y from measureReal_mono h
      exact Icc_subset_Icc_right hxy
    have sSup_eq_iUnion_rat : {x : α × I | a < f x.1 x.2} = ⋃ (q : ℚ), ⋃ (hqI : ↑q ∈ I),
        ⋃ (_ : a < (q : ℝ)), {e | (κ e.1).real (Icc 0 ⟨q, hqI⟩) < e.2} := by
      ext e
      simp only [f]
      constructor
      · intro (he : a < sSup {x | (κ e.1).real (Icc 0 x) < e.2})
        simp_rw [Set.mem_iUnion]
        rw [lt_sSup_iff] at he
        obtain ⟨y, y_mem, (hy : a.1 < y.1)⟩ := he
        obtain ⟨q, hqa, hqy⟩ := exists_rat_btwn hy
        have q_in_I : (q : ℝ) ∈ I := ⟨a.2.1.trans hqa.le, hqy.le.trans y.2.2⟩
        refine ⟨q, q_in_I, hqa, ?_⟩
        exact lt_of_lt_of_le' y_mem (h_monotone e.1 hqy.le)
      · intro he
        simp_all only [lt_sSup_iff, Set.mem_iUnion]
        obtain ⟨q, q_in_I, hqa, h⟩ := he
        exact ⟨⟨q, q_in_I⟩, h, hqa⟩
    rw [sSup_eq_iUnion_rat]
    refine MeasurableSet.iUnion (fun b ↦ MeasurableSet.iUnion
      (fun bI ↦ MeasurableSet.iUnion (fun _ ↦ ?_)))
    refine measurableSet_lt ?_ measurable_snd.subtype_val
    simp_rw [measureReal_def]
    have hκ := κ.measurable_coe (s := Icc 0 ⟨b, bI⟩) measurableSet_Icc
    fun_prop
  refine ⟨f, measurable_f, fun a ↦ (volume.map (f a)).ext_of_Iic (κ a) fun x ↦ ?_⟩
  rw [volume.map_apply measurable_f.of_uncurry_left measurableSet_Iic, preimage]
  simp only [mem_Iic]
  have Iic_to_Icc : Iic x = Icc 0 x := by ext; simp
rw [Iic_to_Icc, ← ofReal_measureReal (measure_ne_top (κ a) _)]
  have κ_in_I : ((κ a).real (Icc 0 x)) ∈ I := ⟨measureReal_nonneg, measureReal_le_one⟩
  rw [← volume_Iic ⟨_, κ_in_I⟩]
  congr with ξ
  constructor
  swap
  · intro (hξ : ξ ≤ (κ a).real (Icc 0 x))
    simp only [sSup_le_iff, f]
    intro c hc
    have le1 := lt_of_le_of_lt' hξ hc
    by_contra h
    push_neg at h
    have le2 : (κ a).real (Icc 0 x) ≤ (κ a).real (Icc 0 c) := by
      suffices h : Icc 0 x ⊆ Icc 0 c from measureReal_mono h
      refine (Icc_subset_Icc_iff unitInterval.nonneg').mpr ?_
      exact ⟨nonneg', h.le⟩
    linarith
  · intro (hξ : f a ξ ≤ x)
    change ξ ≤ (κ a).real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y ↦ (κ a).real (Icc 0 y)
    letI nebot : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      use 1
      exact lt_of_le_of_ne x.2.2 hx
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf ((κ a).map Subtype.val)
      have h_continuousWithinAt := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real (κ a)]
      exact h_continuousWithinAt.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy ↦ hy)
    · apply eventually_nhdsWithin_of_forall
      intro y hy
      by_contra h
      push_neg at h
      simp only [sSup_le_iff, f] at hξ
      specialize hξ y h
      grind

lemma embedding_representation {β : Type*} [Nonempty β] [MeasurableSpace β] {g : β → I}
    (hg : MeasurableEmbedding g) (κ : Kernel α β) [IsMarkovKernel κ] :
    ∃ (f : α → I → β), Measurable (uncurry f) ∧ ∀ a, volume.map (f a) = κ a := by
  have hκg : IsMarkovKernel (κ.map g) := Kernel.IsMarkovKernel.map κ hg.measurable
  classical
  have hg'κ : κ = (κ.map g).map hg.invFun := by
    rw [← Kernel.map_comp_right _ hg.measurable (by fun_prop), LeftInverse.id hg.leftInverse_invFun,
      Kernel.map_id]
  obtain ⟨f', hf', hf'κ⟩ := (κ.map g).unitInterval_representation
  refine ⟨fun a u ↦ hg.invFun (f' a u), by fun_prop, fun a ↦ ?_⟩
  rw [hg'κ, Kernel.map_apply _ (by fun_prop), ← hf'κ, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem representation {β : Type*} [Nonempty β] [MeasurableSpace β] [StandardBorelSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    ∃ (f : α → I → β), Measurable (uncurry f) ∧ ∀ a, volume.map (f a) = κ a :=
  κ.embedding_representation (measurableEmbedding_sigmoid_comp_embeddingReal β)

end ProbabilityTheory.Kernel
