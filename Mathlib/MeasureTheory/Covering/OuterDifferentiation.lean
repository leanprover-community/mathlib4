/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Covering.VitaliFamily
import Mathlib.MeasureTheory.Measure.Regular

open MeasureTheory Measure
open scoped ENNReal

namespace VitaliFamily

variable {X : Type*} [TopologicalSpace X] {m : MeasurableSpace X} {μ : Measure X} {s : Set X}

/-- For every point `x`, sufficiently small sets in a Vitali family around `x` have finite measure.
(This is a trivial result, following from the fact that the measure is locally finite). -/
theorem eventually_measure_lt_top [IsLocallyFiniteMeasure μ] (v : VitaliFamily μ) (x : X) :
    ∀ᶠ t in v.filterAt x, μ t < ∞ :=
  (μ.finiteAt_nhds x).eventually.filter_mono inf_le_left
#align vitali_family.eventually_measure_lt_top VitaliFamily.eventually_measure_lt_top

theorem outerMeasure_le_of_ae_frequently_le [OuterRegular μ] {ρ : OuterMeasure X}
    (v : VitaliFamily μ) (hac : ∀ ⦃t⦄, μ t = 0 → ρ t = 0)
    (h : ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ t in v.filterAt x, ρ t ≤ μ t) : ρ s ≤ μ s := by
  refine le_of_forall_lt' fun a ha ↦ ?_
  rcases s.exists_isOpen_lt_of_lt _ ha with ⟨o, hso, ho, hoa⟩
  set f : v.FineSubfamilyOn s := ⟨fun _ ↦ {t | ρ t ≤ μ t}, h⟩
  set g := f.restrOpen o ho hso
  calc
    ρ s ≤ ∑' i, ρ (g.covering i) := g.outerMeasure_le_tsum_of_absolutelyContinuous hac
    _ ≤ ∑' i, μ (g.covering i) := ENNReal.tsum_le_tsum fun i ↦ (g.covering_mem i).1
    _ ≤ μ o := f.tsum_measure_covering_restrOpen_le _ _
    _ < a := hoa

theorem outerMeasure_le_lintegral [OuterRegular μ] {ρ : Outer
