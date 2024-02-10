import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Measure.Haar.Unique

open TopologicalSpace Function MeasureTheory Measure
open scoped Uniformity Topology ENNReal Pointwise NNReal

namespace MeasureTheory

namespace Measure

variable {G : Type*} [TopologicalSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]

open Classical

/-- Definition of the modularCharacter map -/
@[to_additive addModularCharacter_map "Definition of the addModularCharacter map"]
noncomputable def modularCharacter_map (μ : Measure G) [IsHaarMeasure μ] : G → ℝ≥0 :=
  fun g => haarScalarFactor (map (· * g) μ) μ

@[to_additive]
lemma eq_modularCharacter_smul (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ]
    (g : G) : (map (· * g) μ) = modularCharacter_map μ g • μ :=
  isMulLeftInvariant_eq_smul_of_innerRegular _ _

@[to_additive addModularCharacter_pos]
lemma modularCharacter_pos (μ : Measure G) [IsHaarMeasure μ] (g : G) :
    0 < modularCharacter_map μ g := haarScalarFactor_pos_of_isOpenPosMeasure _ μ

/-- The modular character does not depend on the choice of the haar measure. -/
@[to_additive addModularCharacter_map_eq "The additive modular character does not depend on the choice of
  the additive haar measure."]
theorem modularCharacter_map_eq (μ μ': Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ']
    [InnerRegular μ] [InnerRegular μ'] : modularCharacter_map μ' = modularCharacter_map μ := by
  ext g
  rw [modularCharacter_map, NNReal.coe_eq]
  have : map (· * g) μ' = modularCharacter_map μ g • μ' := by
    calc
      map (· * g) μ' = map (· * g) ((haarScalarFactor μ' μ) • μ) := by
        rw [←isMulLeftInvariant_eq_smul_of_innerRegular]
      _ = haarScalarFactor μ' μ • (map (· * g) μ) := by rw [Measure.map_smul_nnreal]
      _ = haarScalarFactor μ' μ • (modularCharacter_map μ g • μ) := by rw [eq_modularCharacter_smul]
      _ = modularCharacter_map μ g • (haarScalarFactor μ' μ • μ) := by rw [smul_algebra_smul_comm]
      _ = modularCharacter_map μ g • μ' := by rw [←isMulLeftInvariant_eq_smul_of_innerRegular]
  simp [this]

-- theorem test (g h : G) : (· * (g * h)) = (· * h) ∘ (· * g) := by simp only [comp_mul_right]

-- noncomputable def modularCharacter (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ] :
--     G →* ℝ≥0 where
--   toFun := modularCharacter_map μ
--   map_one' := by simp [modularCharacter_map, haarScalarFactor_self_eq_one μ]
--   map_mul' := fun g h => by
--     haveI : IsHaarMeasure (map ((fun x ↦ x * h) ∘ fun x ↦ x * g) μ) := by
--       simp
--       exact inferInstance
--     have mul_g_meas : Measurable (· * g) := Measurable.mul_const (fun ⦃t⦄ a ↦ a) g
--     have mul_h_meas : Measurable (· * h) := Measurable.mul_const (fun ⦃t⦄ a ↦ a) h
--     haveI : IsHaarMeasure ((map (· * h) (modularCharacter_map μ g • μ))) := by
--       simp
--       refine IsHaarMeasure.smul (_ : modularCharacter_map μ g ≠ ∞) _
--     calc
--       modularCharacter_map μ (g * h) = haarScalarFactor (map (· * (g * h)) μ) μ := rfl
--       _ = haarScalarFactor (map ((· * h) ∘ (· * g)) μ) μ := by simp
--       _ = haarScalarFactor (map (· * h) (map (· * g) μ)) μ := by
--         simp_rw [←map_map mul_h_meas mul_g_meas]
--       _ = haarScalarFactor (map (· * h) (modularCharacter_map μ g • μ)) μ := by
--         simp_rw [← eq_modularCharacter_smul _ _]
--       _ = modularCharacter_map μ g * modularCharacter_map μ h := by sorry



end Measure

end MeasureTheory
