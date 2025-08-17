/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Scaling Haar measure by a continuous isomorphism

If `G` is a locally compact topological group and `μ` is a regular Haar measure
on `G`, then an isomorphism `φ : G ≃ₜ* G` scales this measure by some positive
real constant which we call `mulEquivHaarChar φ`.

## Main definitions

* `mulEquivHaarChar φ`: the positive real such that `(mulEquivHaarChar φ) • map φ μ = μ`
  for `μ` a regular Haar measure.
* `addEquivAddHaarChar φ`: the additive version.

-/

open MeasureTheory.Measure

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- If `φ : G ≃ₜ* G` then `mulEquivHaarChar φ` is the positive real factor by which
`φ` scales Haar measures on `G`. -/
@[to_additive /-- If `φ : A ≃ₜ+ A` then `addEquivAddHaarChar φ` is the positive
real factor by which `φ` scales Haar measures on `A`. -/]
noncomputable def mulEquivHaarChar (φ : G ≃ₜ* G) : ℝ≥0 :=
  haarScalarFactor haar (haar.map φ)

@[to_additive]
lemma mulEquivHaarChar_pos (φ : G ≃ₜ* G) : 0 < mulEquivHaarChar φ :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

@[to_additive]
lemma mulEquivHaarChar_eq (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = haarScalarFactor μ (μ.map φ) := by
  have smul := isMulLeftInvariant_eq_smul_of_regular haar μ
  unfold mulEquivHaarChar
  conv =>
    enter [1, 1]
    rw [smul]
  conv =>
    enter [1, 2, 2]
    rw [smul]
  simp_rw [MeasureTheory.Measure.map_smul]
  exact haarScalarFactor_smul_smul _ _ (haarScalarFactor_pos_of_isHaarMeasure haar μ).ne'

@[to_additive addEquivAddHaarChar_smul_map]
lemma mulEquivHaarChar_smul_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • μ.map φ = μ := by
  rw [mulEquivHaarChar_eq μ φ]
  have : Regular (map φ μ) := Regular.map φ.toHomeomorph
  exact (isMulLeftInvariant_eq_smul_of_regular μ (map φ μ)).symm

@[to_additive addEquivAddHaarChar_smul_eq_comap]
lemma mulEquivHaarChar_smul_eq_comap (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    (mulEquivHaarChar φ) • μ = μ.comap φ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  rw [show ⇑φ = ⇑e from rfl, ← e.map_symm, show ⇑e.symm = ⇑φ.symm from rfl]
  have : (map (φ.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← mulEquivHaarChar_smul_map (map φ.symm μ) φ, map_map]
  · simp
  · fun_prop
  · fun_prop

@[to_additive addEquivAddHaarChar_smul_integral_map]
lemma mulEquivHaarChar_smul_integral_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G → ℝ} (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • ∫ a, f a ∂(μ.map φ) = ∫ a, f a ∂μ := by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp

@[to_additive integral_comap_eq_addEquivAddHaarChar_smul]
lemma integral_comap_eq_mulEquivHaarChar_smul (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G → ℝ} (φ : G ≃ₜ* G) :
    ∫ a, f a ∂(μ.comap φ) = mulEquivHaarChar φ • ∫ a, f a ∂μ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  change ∫ a, f a ∂(comap e μ) = mulEquivHaarChar φ • ∫ a, f a ∂μ
  have : (map (e.symm) μ).IsHaarMeasure := φ.symm.isHaarMeasure_map μ
  have : (map (e.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← e.map_symm, ← mulEquivHaarChar_smul_integral_map (map e.symm μ) φ,
    map_map (by exact φ.toHomeomorph.toMeasurableEquiv.measurable) e.symm.measurable]
  -- congr -- breaks to_additive
  rw [show ⇑φ ∘ ⇑e.symm = id by ext; simp [e]]
  simp

@[to_additive addEquivAddHaarChar_smul_preimage]
lemma mulEquivHaarChar_smul_preimage
    (μ : Measure G) [IsHaarMeasure μ] [Regular μ] {X : Set G} (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • μ (φ ⁻¹' X) = μ X := by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp only [smul_apply, nnreal_smul_coe_apply]
  exact congr_arg _ <| (MeasurableEquiv.map_apply φ.toMeasurableEquiv X).symm

@[to_additive (attr := simp)]
lemma mulEquivHaarChar_refl :
    mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]
lemma mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ := by
  rw [mulEquivHaarChar_eq haar ψ, mulEquivHaarChar_eq haar (ψ.trans φ)]
  have hφ : Measurable φ := by fun_prop
  have hψ : Measurable ψ := by fun_prop
  simp_rw [ContinuousMulEquiv.coe_trans, ← map_map hφ hψ]
  have h_reg : (haar.map ψ).Regular := Regular.map ψ.toHomeomorph
  rw [MeasureTheory.Measure.haarScalarFactor_eq_mul haar (haar.map ψ),
    ← mulEquivHaarChar_eq (haar.map ψ)]

end MeasureTheory
