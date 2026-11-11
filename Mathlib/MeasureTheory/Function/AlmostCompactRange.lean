/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# The range of a strongly measurable function is almost compact

Consider a function from a space with a finite measure to a complete space.
Then most of the values of the function land in a compact subset of the target space.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X]
  [TopologicalSpace Y] [TopologicalSpace.IsCompletelyPseudoMetrizableSpace Y]

/-- A function on a finite measure space takes with high probability its values in a compact
subset. -/
lemma StronglyMeasurable.exists_isCompact_measure_preimage_compl_le {g : X → Y}
    (ν : Measure X) [IsFiniteMeasure ν] (hg : StronglyMeasurable g) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ L : Set Y, IsCompact L ∧ ν (g ⁻¹' L)ᶜ < ε := by
  let := TopologicalSpace.upgradeIsCompletelyPseudoMetrizable Y
  borelize Y
  let T : Set Y := closure (Set.range g)
  have hTclosed : IsClosed T := isClosed_closure
  have hTsep : TopologicalSpace.IsSeparable T := hg.isSeparable_range.closure
  have hgT : ∀ x, g x ∈ T := fun x => subset_closure (Set.mem_range_self x)
  let gT : X → T := fun x => ⟨g x, hgT x⟩
  have hgTae : AEMeasurable gT ν := hg.aestronglyMeasurable.aemeasurable.subtype_mk
  have : SecondCountableTopology T := hTsep.secondCountableTopology
  let μT : Measure T := (ν : Measure X).map gT
  obtain ⟨K, hKcomp, hKμ⟩ := exists_isCompact_closure_measure_compl_lt μT ε hε
  refine ⟨Subtype.val '' closure K, hKcomp.image continuous_subtype_val, ?_⟩
  have hmap : μT (closure K)ᶜ = ν (g ⁻¹' (Subtype.val '' closure K))ᶜ := by
    rw [Measure.map_apply_of_aemeasurable hgTae isClosed_closure.measurableSet.compl]
    congr
    ext
    simp [gT, hgT]
  rw [← hmap]
  exact (measure_mono (Set.compl_subset_compl.2 subset_closure)).trans_lt hKμ

/-- A function on a finite measure space takes with high probability its values in a compact
subset. -/
lemma AEStronglyMeasurable.exists_isCompact_measure_preimage_compl_le {g : X → Y}
    (ν : Measure X) [IsFiniteMeasure ν] (hg : AEStronglyMeasurable g ν) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ L : Set Y, IsCompact L ∧ ν (g ⁻¹' L)ᶜ < ε := by
  obtain ⟨L, hL, hLε⟩ :=
    StronglyMeasurable.exists_isCompact_measure_preimage_compl_le (g := hg.mk g) (ν := ν)
      hg.stronglyMeasurable_mk hε
  refine ⟨L, hL, ?_⟩
  have hsets : (g ⁻¹' L)ᶜ =ᵐ[(ν : Measure X)] (hg.mk g ⁻¹' L)ᶜ := by
    filter_upwards [hg.ae_eq_mk] with x hx
    simp only [Set.mem_compl_iff, Set.mem_preimage, hx]
  rw [measure_congr hsets]
  exact hLε

/-- A function on a finite measure space takes with high probability its values in a compact
subset. -/
lemma StronglyMeasurable.exists_isCompact_measureReal_preimage_compl_le {g : X → Y}
    (ν : Measure X) [IsFiniteMeasure ν] (hg : StronglyMeasurable g) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Set Y, IsCompact L ∧ ν.real (g ⁻¹' L)ᶜ < ε := by
  obtain ⟨L, hL, hLε⟩ := StronglyMeasurable.exists_isCompact_measure_preimage_compl_le ν hg
    (ENNReal.ofReal_pos.2 hε)
  exact ⟨L, hL, ENNReal.toReal_lt_of_lt_ofReal hLε⟩

/-- A function on a finite measure space takes with high probability its values in a compact
subset. -/
lemma AEStronglyMeasurable.exists_isCompact_measureReal_preimage_compl_le {g : X → Y}
    (ν : Measure X) [IsFiniteMeasure ν] (hg : AEStronglyMeasurable g ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Set Y, IsCompact L ∧ ν.real (g ⁻¹' L)ᶜ < ε := by
  obtain ⟨L, hL, hLε⟩ := AEStronglyMeasurable.exists_isCompact_measure_preimage_compl_le ν hg
    (ENNReal.ofReal_pos.2 hε)
  exact ⟨L, hL, ENNReal.toReal_lt_of_lt_ofReal hLε⟩

end MeasureTheory
