/-
Copyright (c) 2025 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Modular character of a locally compact group

On a locally compact group, there is a natural homomorphism `G → ℝ≥0*`, which for `g : G` gives the
value `μ (· * g⁻¹) / μ`, where `μ` is an (inner regular) Haar measure. This file defines this
homomorphism, called the modular character, and shows that it is independent of the chosen Haar
measure.

TODO: Show that the character is continuous.

## Main Declarations

* `modularCharacterFun`: Define the modular character function. If `μ` is a left Haar measure on `G`
  and `g : G`, the measure `A ↦ μ (A g⁻¹)` is also a left Haar measure, so by uniqueness is of the
  form `Δ(g) μ`, for `Δ(g) ∈ ℝ≥0`. This `Δ` is the modular character. The result that this does not
  depend on the measure chosen is `modularCharacterFun_eq_haarScalarFactor`.
* `modularCharacter`: The homomorphism G →* ℝ≥0 whose toFun is `modularCharacterFun`.
-/

open MeasureTheory
open scoped NNReal

namespace MeasureTheory

namespace Measure

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The modular character as a map is `g ↦ μ (· * g⁻¹) / μ`, where `μ` is a left Haar measure.

  See also `modularCharacter` that defines the map as a homomorphism. -/
@[to_additive /-- The additive modular character as a map is `g ↦ μ (· - g) / μ`, where `μ` is an
  left additive Haar measure. -/]
noncomputable def modularCharacter : G →* ℝ≥0 :=
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  {
    toFun g := haarScalarFactor (DomMulAct.mk g • haar) (haar (G := G))
    map_one' := by simp
    map_mul' g g' := by
      simp_rw [DomMulAct.mk_mul]
      rw [haarScalarFactor_eq_mul _ (DomMulAct.mk g' • addHaar (G := A))]
      congr 1
      simp_rw [mul_smul]
      rw [haarScalarFactor_domSMul]
  }

/-- Independence of modularCharacterFun from the chosen Haar measure. -/
@[to_additive /-- Independence of addModularCharacterFun from the chosen Haar measure -/]
lemma modularCharacterFun_eq_haarScalarFactor [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] (g : G) : modularCharacterFun g = haarScalarFactor (map (· * g) μ) μ := by
  borelize G
  exact haarScalarFactor_smul_congr ..

@[to_additive]
lemma map_right_mul_eq_modularCharacterFun_smul [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] [InnerRegular μ] (g : G) : map (· * g) μ = modularCharacterFun g • μ := by
  rw [modularCharacterFun_eq_haarScalarFactor μ _]
  exact isMulLeftInvariant_eq_smul_of_innerRegular _ μ

@[to_additive]
lemma modularCharacterFun_pos (g : G) : 0 < modularCharacterFun g := by
  borelize G
  rw [modularCharacterFun_eq_haarScalarFactor MeasureTheory.Measure.haar g]
  exact haarScalarFactor_pos_of_isHaarMeasure _ _

@[to_additive]
lemma modularCharacterFun_map_one : modularCharacterFun (1 : G) = 1 := by
  simp [modularCharacterFun, haarScalarFactor_self]

@[to_additive]
lemma modularCharacterFun_map_mul (g h : G) : modularCharacterFun (g * h) =
    modularCharacterFun g * modularCharacterFun h := by
  borelize G
  have mul_g_meas : Measurable (· * g) := Measurable.mul_const (fun ⦃_⦄ a ↦ a) g
  have mul_h_meas : Measurable (· * h) := Measurable.mul_const (fun ⦃_⦄ a ↦ a) h
  let ν := MeasureTheory.Measure.haar (G := G)
  symm
  calc
    modularCharacterFun g * modularCharacterFun h =
      modularCharacterFun h * modularCharacterFun g := mul_comm _ _
    _ = haarScalarFactor (map (· * h) (map (· * g) ν)) (map (· * g) ν) *
      modularCharacterFun g := by
      rw [modularCharacterFun_eq_haarScalarFactor (map (· * g) ν) _]
    _ = haarScalarFactor (map (· * h) (map (· * g) ν)) (map (· * g) ν) *
      haarScalarFactor (map (· * g) ν) ν := rfl
    _ = haarScalarFactor (map (· * (g * h)) ν) ν := by simp only [map_map mul_h_meas mul_g_meas,
      comp_mul_right, ← haarScalarFactor_eq_mul]

/-- The modular character homomorphism. The underlying function is `modularCharacterFun`, which is
`g ↦ μ (· * g⁻¹) / μ`, where `μ` is a left Haar measure.
-/
noncomputable def modularCharacter : G →* ℝ≥0 where
  toFun := modularCharacterFun
  map_one' := modularCharacterFun_map_one
  map_mul' := modularCharacterFun_map_mul

end Measure

end MeasureTheory
