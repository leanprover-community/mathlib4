/-
Copyright (c) 2024 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Measure.Haar.Unique


/-!
# Modular character of a locally compact group

On a locally compact group, there is a natural character G → ℝ*, which for g : G gives the value
μ (· * g) / μ, where μ is an (inner regular) Haar measure. This file defines this character, called
the modular character, and shows that it is multiplicative and independent of the chosen Haar
measure.
TODO: Show that the character is continuous.

## Main Declarations

* `modularCharacter_fun`: Given a measure μ, define the modular character associated with this
  measure, using the (noncomputable) `haarScalarFactor`. The result that this does not depend on the
  measure chosen (as long as it is inner regular) is `modularCharacter_fun_eq`.
* `modularCharacter`: The homomorphism G →* ℝ≥0 whose toFun is `modularCharacter_fun`.
-/

open MeasureTheory
open scoped NNReal

namespace MeasureTheory

namespace Measure

variable {G : Type*} [TopologicalSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]

open Classical

/-- Definition of the modularCharacter map -/
@[to_additive addModularCharacter_fun "Definition of the addModularCharacter map"]
noncomputable def modularCharacter_fun (μ : Measure G) [IsHaarMeasure μ] : G → ℝ≥0 :=
  fun g => haarScalarFactor (map (· * g) μ) μ

@[to_additive map_right_add_eq_addModularCharacter_smul]
lemma map_right_mul_eq_modularCharacter_smul (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ]
    (g : G) : (map (· * g) μ) = modularCharacter_fun μ g • μ :=
  isMulLeftInvariant_eq_smul_of_innerRegular _ _

@[to_additive addModularCharacter_pos]
lemma modularCharacter_pos (μ : Measure G) [IsHaarMeasure μ] (g : G) :
    0 < modularCharacter_fun μ g := haarScalarFactor_pos_of_isHaarMeasure _ μ

/-- The modular character does not depend on the choice of the Haar measure. -/
@[to_additive addModularCharacter_eq "The additive modular character does not depend on the choice
of the additive Haar measure."]
theorem modularCharacter_eq (μ μ': Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ']
    [InnerRegular μ] [InnerRegular μ'] : modularCharacter_fun μ' = modularCharacter_fun μ := by
  ext g
  rw [modularCharacter_fun, NNReal.coe_inj]
  have : map (· * g) μ' = modularCharacter_fun μ g • μ' := by
    calc
      map (· * g) μ' = map (· * g) ((haarScalarFactor μ' μ) • μ) := by
        rw [← isMulLeftInvariant_eq_smul_of_innerRegular]
      _ = haarScalarFactor μ' μ • (map (· * g) μ) := by rw [Measure.map_smul_nnreal]
      _ = haarScalarFactor μ' μ • (modularCharacter_fun μ g • μ) := by
        rw [map_right_mul_eq_modularCharacter_smul]
      _ = modularCharacter_fun μ g • (haarScalarFactor μ' μ • μ) := by rw [smul_algebra_smul_comm]
      _ = modularCharacter_fun μ g • μ' := by rw [← isMulLeftInvariant_eq_smul_of_innerRegular]
  simp [this]

/-- The modular character homomorphism. -/
noncomputable def modularCharacter (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ] :
    G →* ℝ≥0 where
  toFun := modularCharacter_fun μ
  map_one' := by simp [modularCharacter_fun, haarScalarFactor_self μ]
  map_mul' := fun g h => by
    have mul_g_meas : Measurable (· * g) := Measurable.mul_const (fun ⦃_⦄ a ↦ a) g
    have mul_h_meas : Measurable (· * h) := Measurable.mul_const (fun ⦃_⦄ a ↦ a) h
    symm
    calc
      modularCharacter_fun μ g * modularCharacter_fun μ h =
        modularCharacter_fun μ h * modularCharacter_fun μ g := mul_comm _ _
      _ = modularCharacter_fun (map (· * g) μ) h * modularCharacter_fun μ g := by
        rw [modularCharacter_eq (map (· * g) μ) μ]
      _ = haarScalarFactor (map (· * h) (map (· * g) μ)) (map (· * g) μ) *
        haarScalarFactor (map (· * g) μ) μ := rfl
      _ = haarScalarFactor (map (· * (g * h)) μ) μ := by simp only [map_map mul_h_meas mul_g_meas,
        comp_mul_right, ← haarScalarFactor_eq_mul]

end Measure

end MeasureTheory
