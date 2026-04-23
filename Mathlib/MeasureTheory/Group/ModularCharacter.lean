/-
Copyright (c) 2025 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.UrysohnsLemma

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

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MeasureTheory

namespace Measure

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The modular character as a map is `g ↦ μ (· * g⁻¹) / μ`, where `μ` is a left Haar measure.

  See also `modularCharacter` that defines the map as a homomorphism. -/
@[to_additive /-- The additive modular character as a map is `g ↦ μ (· - g) / μ`, where `μ` is an
  left additive Haar measure. -/]
noncomputable def modularCharacterFun (g : G) : ℝ≥0 :=
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haarScalarFactor (map (· * g) MeasureTheory.Measure.haar) MeasureTheory.Measure.haar

/-- Independence of modularCharacterFun from the chosen Haar measure. -/
@[to_additive /-- Independence of addModularCharacterFun from the chosen Haar measure -/]
lemma modularCharacterFun_eq_haarScalarFactor [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] (g : G) : modularCharacterFun g = haarScalarFactor (map (· * g) μ) μ := by
  let ν := MeasureTheory.Measure.haar (G := G)
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_one⟩ :
    ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_f_ne_zero (μ₀ : Measure G) [IsHaarMeasure μ₀] : ∫ x, f x ∂μ₀ ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  apply NNReal.coe_injective
  have t : (∫ x, f (x * g) ∂ν) = (∫ x, f (x * g) ∂(haarScalarFactor ν μ • μ)) := by
    refine integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ ?_ ?_
    · exact Continuous.comp' f_cont (continuous_mul_const g)
    · have j : (fun x ↦ f (x * g)) = (f ∘ (Homeomorph.mulRight g)) := rfl
      rw [j]
      exact HasCompactSupport.comp_homeomorph f_comp _
  have r : (haarScalarFactor ν μ : ℝ) / (haarScalarFactor ν μ) = 1 := by
    refine div_self ?_
    rw [NNReal.coe_ne_zero]
    apply (ne_of_lt (haarScalarFactor_pos_of_isHaarMeasure _ _)).symm
  calc
  ↑(modularCharacterFun g) = ↑(haarScalarFactor (map (· * g) ν) ν) := by borelize G; rfl
  _ = (∫ x, f x ∂(map (· * g) ν)) / ∫ x, f x ∂ν :=
    haarScalarFactor_eq_integral_div _ _ f_cont f_comp (int_f_ne_zero ν)
  _ = (∫ x, f (x * g) ∂ν) / ∫ x, f x ∂ν := by
    rw [integral_map (AEMeasurable.mul_const aemeasurable_id' _)
    (Continuous.aestronglyMeasurable f_cont)]
  _ = (∫ x, f (x * g) ∂(haarScalarFactor ν μ • μ)) / ∫ x, f x ∂ν := by rw [t]
  _ = (∫ x, f (x * g) ∂(haarScalarFactor ν μ • μ)) / ∫ x, f x ∂(haarScalarFactor ν μ • μ) := by
    rw [integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ f_cont f_comp]
  _ = (haarScalarFactor ν μ • ∫ x, f (x * g) ∂μ) / (haarScalarFactor ν μ • ∫ x, f x ∂μ) := by
    rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  _ = (haarScalarFactor ν μ / haarScalarFactor ν μ) * ((∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ) :=
    mul_div_mul_comm _ _ _ _
  _ = 1 * ((∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ) := by rw [r]
  _ = (∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ := by rw [one_mul]
  _ = (∫ x, f x ∂(map (· * g) μ)) / ∫ x, f x ∂μ := by
    rw [integral_map (AEMeasurable.mul_const aemeasurable_id' _)
    (Continuous.aestronglyMeasurable f_cont)]
  _ = haarScalarFactor (map (· * g) μ) μ :=
    (haarScalarFactor_eq_integral_div _ _ f_cont f_comp (int_f_ne_zero μ)).symm

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
