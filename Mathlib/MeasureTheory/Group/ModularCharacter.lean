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

/-- Definition of the modularCharacter map -/
@[to_additive addModularCharacter_map "Definition of the addModularCharacter map"]
noncomputable def modularCharacter_map (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ] :
    G → ℝ≥0 := fun g => haarScalarFactor (map (· * g) μ) μ

/-- The modular character does not depend on the choice of the haar measure. -/
@[to_additive]
theorem modularCharacter_map_eq (μ μ': Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ']
    [InnerRegular μ] [InnerRegular μ'] : modularCharacter_map μ' = modularCharacter_map μ := by
  ext g
  rw [modularCharacter_map, NNReal.coe_eq]
  apply haarScalarFactor_of_eq_smul (map (· * g) μ') μ'
  calc
    map (· * g) μ' = map (· * g) ((haarScalarFactor μ' μ) • μ) := by
      rw [←isMulLeftInvariant_eq_smul_of_innerRegular _ _]
    _ = (haarScalarFactor μ' μ) • (map (· * g) μ) := by rw [Measure.map_smul_nnreal]
    _ = (haarScalarFactor μ' μ) • (modularCharacter_map μ g • μ) := by
      rw [modularCharacter_map, ←isMulLeftInvariant_eq_smul_of_innerRegular _ _]
    _ = (modularCharacter_map μ g) • ((haarScalarFactor μ' μ) • μ) := by
      rw [smul_algebra_smul_comm (modularCharacter_map μ g) (haarScalarFactor μ' μ) μ]
    _ = (modularCharacter_map μ g) • μ' := by rw [←isMulLeftInvariant_eq_smul_of_innerRegular _ _]

noncomputable def modularCharacter (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ] :
    G →* ℝ≥0 where
  toFun := modularCharacter_map μ
  map_one' := by
    rw [modularCharacter_map]
    simp [haarScalarFactor_self_eq_one μ]
  map_mul' := fun g h => by
    calc
      modularCharacter_map μ (g * h) = haarScalarFactor (map (· * g) )) μ := by simp
      modularCharacter_map μ g * modularCharacter_map μ h := by sorry



end Measure
