/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Kernel.Defs

import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Probability.CDF

/-!
# Representation of kernels

This file contains results about isolation of kernels randomness. In particular, it shows that,
when the target space is a standard Borel space, any Markov kernel can be represented as the image
of the uniform measure on `[0,1]` by a deterministic map. It corresponds to Lemma 4.22 in
"Foundations of Modern Probability" by Olav Kallenberg, 2021.

## Auxiliary lemmas

* `ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval₀`:
  for a Markov kernel `κ : Kernel α I`, there exists a jointly measurable function
  `f : α → I → I` such that for all `a : α`, `volume.map (f a) = κ a`.

## Main results

* `ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`:
  for a Markov kernel `κ : Kernel α β` with `β` a standard Borel space,
  there exists a jointly measurable function `f : α → I → β` such that for all `a : α`,
  `volume.map (f a) = κ a`.
  This is a consequence of `ProbabilityTheory.Kernel.embedding_representation` and the fact that
  any standard Borel space can be embedded in `ℝ`, and then composed with `unitInterval.sigmoid`.

* `ProbabilityTheory.Kernel.exists_measurable_map_eq_not_countable`:
  for a Markov kernel `κ : Kernel α β` with `β` a standard Borel space
  and `ι` a non-countable standard Borel space, there exists a jointly
  measurable function `f : α → ι → β` such that for all `a : α`,
  `volume.map (f a ∘ equiv) = κ a`, where `equiv : I ≃ᵐ ι` is a measurable equivalence
  between `I` and `ι`.
  This is a consequence of `ProbabilityTheory.Kernel.unitInterval_representation` and the
  fact that any non-countable standard Borel space is measurably equivalent to `I`.

* `ProbabilityTheory.Kernel.exists_measurable_map_eq`:
  for a probability measure `μ` on a standard Borel space `β`,
  there exists a measurable function `f : I → β` such that `volume.map f = μ`.
  This is a consequence of `ProbabilityTheory.Kernel.unitInterval_representation`.
-/

public section

open MeasureTheory ProbabilityTheory Set unitInterval Filter Topology Function

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} [Nonempty β] {mβ : MeasurableSpace β}
    [StandardBorelSpace β]

lemma exists_measurable_map_eq_unitInterval₀ (κ : Kernel α I) [IsMarkovKernel κ] :
    ∃ (f : α → I → I), Measurable (uncurry f) ∧ ∀ a, volume.map (f a) = κ a := by
  let f := fun s (t : I) ↦ sSup {x | (κ s).real (Icc 0 x) < t}
  have measurable_f : Measurable (uncurry f) := by
    refine measurable_of_Ioi fun a ↦ ?_
    simp only [preimage, uncurry, mem_Ioi]
    have h_monotone s : Monotone (fun x ↦ (κ s).real (Icc 0 x)) :=
      fun x y hxy ↦ measureReal_mono (by gcongr)
    have sSup_eq_iUnion_rat : {x : α × I | a < f x.1 x.2} =
        ⋃ (q : ℚ) (hqI : ↑q ∈ I) (_ : a < (q : ℝ)), {e | (κ e.1).real (Icc 0 ⟨q, hqI⟩) < e.2} := by
      ext e
      simp only [f]
      constructor
      · intro (he : a < sSup {x | (κ e.1).real (Icc 0 x) < e.2})
        simp_rw [Set.mem_iUnion]
        rw [lt_sSup_iff] at he
        obtain ⟨y, y_mem, (hy : a.1 < y.1)⟩ := he
        obtain ⟨q, hqa, hqy⟩ := exists_rat_btwn hy
        have q_in_I : (q : ℝ) ∈ I := ⟨a.2.1.trans hqa.le, hqy.le.trans y.2.2⟩
        exact ⟨q, q_in_I, hqa, lt_of_lt_of_le' y_mem (h_monotone e.1 hqy.le)⟩
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
    by_contra! h
    have h_lt : ¬ (κ a).real (Icc 0 x) ≤ (κ a).real (Icc 0 c) := not_le.mpr (lt_of_le_of_lt' hξ hc)
    refine h_lt ?_
    gcongr
    simp
  · intro (hξ : f a ξ ≤ x)
    change ξ ≤ (κ a).real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y ↦ (κ a).real (Icc 0 y)
    have : NeBot (𝓝[>] x) := nhdsGT_neBot_of_exists_gt ⟨1, lt_of_le_of_ne x.2.2 hx⟩
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf ((κ a).map Subtype.val)
      have h_continuousWithinAt := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real (κ a)]
      exact h_continuousWithinAt.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy ↦ hy)
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      by_contra! h
      simp only [sSup_le_iff, f] at hξ
      specialize hξ y h
      grind

theorem exists_measurable_map_eq_unitInterval (κ : Kernel α β) [IsMarkovKernel κ] :
    ∃ (f : α → I → β), Measurable (uncurry f) ∧ ∀ a, volume.map (f a) = κ a := by
  let g := sigmoid ∘ embeddingReal β
  have hg := measurableEmbedding_sigmoid_comp_embeddingReal β
  have hκg : IsMarkovKernel (κ.map g) := IsMarkovKernel.map κ hg.measurable
  have hg'κ : κ = (κ.map g).map hg.invFun := by
    rw [← map_comp_right _ hg.measurable (by fun_prop), LeftInverse.id hg.leftInverse_invFun,
      map_id]
  obtain ⟨f', hf', hf'κ⟩ := (κ.map g).exists_measurable_map_eq_unitInterval₀
  refine ⟨fun a u ↦ hg.invFun (f' a u), by fun_prop, fun a ↦ ?_⟩
  rw [hg'κ, map_apply _ (by fun_prop), ← hf'κ, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem exists_measurable_map_eq_not_countable {ι : Type*}
    [MeasurableSpace ι] [StandardBorelSpace ι]
    (hι : ¬ Countable ι) (κ : Kernel α β) [IsMarkovKernel κ] :
    ∃ (f : α → ι → β), Measurable (uncurry f) ∧ ∀ a, (volume.map <|
      (f a) ∘ PolishSpace.measurableEquivOfNotCountable not_countable_unitInterval hι) = κ a := by
  obtain ⟨f, hfm, hf⟩ := κ.exists_measurable_map_eq_unitInterval
  set equiv_I_ι := PolishSpace.measurableEquivOfNotCountable not_countable_unitInterval hι
  let f' : α → ι → β := fun a i ↦ f a (equiv_I_ι.symm i)
  refine ⟨f', by fun_prop, ?_⟩
  intro a
  ext s hs
  rw [volume.map_apply (by fun_prop) hs]
  specialize hf a
  replace hf : volume.map (f a) s = κ a s := DFunLike.congr_fun hf s
  rw [volume.map_apply (by fun_prop) hs] at hf
  simp_all [f', preimage]

end ProbabilityTheory.Kernel

theorem MeasureTheory.Measure.exists_measurable_map_eq {β : Type*} {mβ : MeasurableSpace β}
    [Nonempty β] [StandardBorelSpace β] (μ : Measure β) [IsProbabilityMeasure μ] :
    ∃ (f : I → β), Measurable f ∧ volume.map f = μ := by
  obtain ⟨f, hf_meas, hf_map⟩ := (Kernel.const Unit μ).exists_measurable_map_eq_unitInterval
  exact ⟨f (), by fun_prop, by simpa using hf_map ()⟩
