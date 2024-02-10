import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Measure.Haar.Unique

open TopologicalSpace Function MeasureTheory Measure
open scoped Uniformity Topology ENNReal Pointwise NNReal

namespace Measure

variable {G : Type*} [TopologicalSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]

open Classical

/-- The modular character of a group, defined using a choice of a haar measure `μ` on `G`. -/
-- @[to_additive "The modular character of a group, defined using a choice of a addHaar measure
-- `μ` on `G`."]
noncomputable def modularCharacter_map (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ] :
    G → ℝ≥0 := fun g => haarScalarFactor (map (· * g) μ) μ

theorem modularCharacter_map_eq (μ μ': Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ']
    [InnerRegular μ] [InnerRegular μ'] : modularCharacter_map μ' = modularCharacter_map μ := by
  ext g
  have : μ' = haarScalarFactor μ' μ • μ := isMulLeftInvariant_eq_smul_of_innerRegular _ _
  rw [modularCharacter_map, NNReal.coe_eq]
  apply haarScalarFactor_of_eq_smul (map (· * g) μ') μ'
  calc
    map (· * g) μ' = (haarScalarFactor (map (· * g) μ') μ') • μ' := by sorry -- isMulLeftInvariant_eq_smul_of_innerRegular _ _

-- lemma modularCharacter_eq (μ μ' : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ']


end Measure
