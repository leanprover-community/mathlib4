import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Basic



open MeasureTheory.Measure NNReal

namespace MeasureTheory

namespace ModularCharacter

variable {G : Type*} [TopologicalSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]



noncomputable def modularCharacter : G →* ℝ≥0 := {
  toFun := fun g => haarScalarFactor μ (map (fun x ↦ x * g) μ),
  map_one' := haarScalarFactor_self_eq_one _,
  map_mul' := sorry
}

end ModularCharacter

end
