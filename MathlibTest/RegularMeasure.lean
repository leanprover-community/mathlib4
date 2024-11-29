import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Metrizable.Urysohn

/-! Check that typeclass inference knows that a Haar measure on a locally compact second countable
topological group is automatically regular and inner regular. -/

open MeasureTheory Measure

variable {G : Type*} [MeasurableSpace G] [Group G] [TopologicalSpace G]
  [TopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]
  (μ : Measure G) [IsHaarMeasure μ]

example : Regular μ := inferInstance
example : InnerRegular μ := inferInstance

/- Check that typeclass inference works to guarantee regularity and inner regularity in
interesting situations. -/

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [LocallyCompactSpace α]
  [RegularSpace α] [BorelSpace α] [SecondCountableTopology α]

example (μ : Measure α) [IsFiniteMeasureOnCompacts μ] : Regular μ := inferInstance
example (μ : Measure α) [IsFiniteMeasureOnCompacts μ] : InnerRegular μ := inferInstance
