/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Volume measure for Euclidean geometry

In this file we introduce a `d`-dimensional measure for `n`-dimensional Euclidean affine space,
namely `MeasureTheory.Measure.euclideanHausdorffMeasure d` with notation `μHE[d]`.
This is the suitable measure to describe area and volume in an environment of arbitrary dimension.
It is characterized by the following properties:

* Coincides with Lebesgue measure when `d = n`.
* Preserved through isometry, and specifically through affine subspace inclusion.

Internally, this is defined as the `MeasureTheory.Measure.hausdorffMeasure` scaled by a factor.
The factor is defined nonconstructively as the `MeasureTheory.Measure.addHaarScalarFactor` between
the Hausdorff measure and the Lebesgue measure on a model Euclidean space.

TODO: show the scaling factor equals to the ratio between the volume of `d`-dimensional
`Metric.ball` with Euclidean metric and with sup metric.

## Main definitions

* `MeasureTheory.Measure.euclideanHausdorffMeasure`: the Euclidean Hausdorff measure.

## Main statements

* `EuclideanGeometry.measurePreserving_vaddConst`: `μHE[d]` on an affine space matches volume on the
  associated inner product space.
* `AffineSubspace.euclideanHausdorffMeasure_coe_image`: `μHE[d]` is preserved through subspace
  inclusion.

## Tags

Hausdorff measure, measure, metric measure, volume, area
-/

open MeasureTheory Measure

public section

instance (d : ℕ) : (μH[d] : Measure (EuclideanSpace ℝ (Fin d))).IsAddHaarMeasure := by
  simpa using MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℝ (Fin d))

variable {X Y : Type*}
variable [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/--
Euclidean Hausdorff measure `μHE[d]`, defined as `μH[d]` scaled to agree with Lebesgue measure
on a `d`-dimensional Euclidean space. While this is defined on any (e)metric space, it is intended
to be used for affine space associated with an inner product space, where it agrees with the volume
measure on the inner product space.
-/
noncomputable
def MeasureTheory.Measure.euclideanHausdorffMeasure (d : ℕ) : Measure X :=
  addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] • μH[d]

@[inherit_doc]
scoped[MeasureTheory] notation "μHE[" d "]" => MeasureTheory.Measure.euclideanHausdorffMeasure d

/-- show the scaling factor equals to the ratio between the volume of `d`-dimensional
`Metric.ball` with Euclidean metric and with sup metric (i.e. a cube), or explicity,
$\pi^{d/2} / (2^d \Gamma (d/2+1))$. -/
proof_wanted MeasureTheory.Measure.addHaarScalarFactor_hausdorffMeasure_eq (d : ℕ) :
    addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] =
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) / volume (Metric.ball (0 : Fin d -> ℝ) 1)

theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def (d : ℕ) :
    (μHE[d] : Measure X) =
    addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] • μH[d] := by
  rfl

set_option backward.isDefEq.respectTransparency false in -- needed by simplifying `1 • _`
/-- `μHE[0]` and `μH[0]` are equal. -/
@[simp]
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero :
    (μHE[0] : Measure X) = (μH[0] : Measure X) := by
  let basis : OrthonormalBasis (Fin 0) ℝ (EuclideanSpace ℝ (Fin 0)) :=
    EuclideanSpace.basisFun (Fin 0) ℝ
  have heq : ({0} : Set (EuclideanSpace ℝ (Fin 0))) = parallelepiped basis := by
    simp [parallelepiped]
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace ℝ (Fin 0))) μH[(0 : ℕ)]
  obtain h := congr($h.symm {0})
  conv_rhs at h => rw [heq, OrthonormalBasis.volume_parallelepiped]
  simp_rw [CharP.cast_eq_zero, smul_apply, hausdorffMeasure_zero_singleton, ENNReal.smul_def,
    smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h
  simp [euclideanHausdorffMeasure_def, h]

/-- The scalar that defines `μHE[d]` is non-zero. -/
theorem MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (d : ℕ) :
    addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] ≠ 0 := by
  intro h0
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d]
  obtain h := congr($h (parallelepiped (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d)))))
  simp [OrthonormalBasis.volume_parallelepiped, h0] at h

set_option backward.isDefEq.respectTransparency false in -- needed by `ENNReal.smul_def`
instance MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] : (μHE[Module.finrank ℝ E] : Measure E).IsAddHaarMeasure := by
  rw [euclideanHausdorffMeasure_def, ENNReal.smul_def]
  exact IsAddHaarMeasure.smul _
    (by simpa using addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Module.finrank ℝ E))
    (by simp)

set_option backward.isDefEq.respectTransparency false in -- needed by `ENNReal.smul_top`
/-- If `d₁ < d₂`, then for any set s we have either `μHE[d₂] s = 0`, or `μHE[d₁] s = ∞`. -/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top {d₁ d₂ : ℕ} (h : d₁ < d₂)
    (s : Set X) : μHE[d₂] s = 0 ∨ μHE[d₁] s = ⊤ := by
  simp_rw [euclideanHausdorffMeasure_def]
  obtain h | h := hausdorffMeasure_zero_or_top (show (d₁ : ℝ) < d₂ by simpa using h) s
  · simp [h]
  · right
    rw [smul_apply, h, ENNReal.smul_top]
    simp [addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]

/-!
### `μHE[d]` is preserved through isometry
-/

theorem IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (e : X ≃ᵢ Y) (d : ℕ) :
    MeasurePreserving e μHE[d] μHE[d] :=
  (IsometryEquiv.measurePreserving_hausdorffMeasure e d).smul_measure _

theorem Isometry.euclideanHausdorffMeasure_image {f : X → Y} {d : ℕ} (hf : Isometry f) (s : Set X) :
    μHE[d] (f '' s) = μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, smul_apply]
  rw [Isometry.hausdorffMeasure_image hf (by simp)]

theorem Isometry.euclideanHausdorffMeasure_preimage {f : X → Y} {d : ℕ} (hf : Isometry f)
    (s : Set Y) : μHE[d] (f ⁻¹' s) = μHE[d] (s ∩ Set.range f) := by
  simp_rw [euclideanHausdorffMeasure_def, smul_apply]
  rw [Isometry.hausdorffMeasure_preimage hf (by simp)]

theorem Isometry.map_euclideanHausdorffMeasure {f : X → Y} {d : ℕ} (hf : Isometry f) :
    μHE[d].map f = μHE[d].restrict (Set.range f) := by
  simp_rw [euclideanHausdorffMeasure_def]
  rw [Measure.map_smul, map_hausdorffMeasure hf (by simp), Measure.restrict_smul]

/-!
### Applying scalers to `μHE[d]`
-/

open Pointwise in
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ {𝕜 : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [MeasurableSpace E] [BorelSpace E] (d : ℕ) {r : 𝕜} (hr : r ≠ 0) (s : Set E) :
    μHE[d] (r • s) = ‖r‖₊ ^ d • μHE[d] s := by
  rw [euclideanHausdorffMeasure_def, Measure.smul_apply, hausdorffMeasure_smul₀ (by simp) hr,
    Measure.smul_apply, smul_comm]
  simp

section Homothety
variable {𝕜 V P : Type*} [NormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [MeasurableSpace P] [MetricSpace P] [NormedAddTorsor V P] [BorelSpace P]

theorem MeasureTheory.euclideanHausdorffMeasure_homothety_image (d : ℕ) (x : P) {c : 𝕜}
    (hc : c ≠ 0) (s : Set P) :
    μHE[d] (AffineMap.homothety x c '' s) = ‖c‖₊ ^ d • μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, smul_apply]
  rw [hausdorffMeasure_homothety_image (by simp) x hc, smul_comm, NNReal.rpow_natCast]

theorem MeasureTheory.euclideanHausdorffMeasure_homothety_preimage (d : ℕ) (x : P) {c : 𝕜}
    (hc : c ≠ 0) (s : Set P) :
    μHE[d] (AffineMap.homothety x c ⁻¹' s) = ‖c‖₊⁻¹ ^ d • μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, smul_apply]
  rw [hausdorffMeasure_homothety_preimage (by simp) x hc, smul_comm, NNReal.rpow_natCast]

end Homothety

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional ℝ V]
variable [MetricSpace P] [MeasurableSpace P] [BorelSpace P] [NormedAddTorsor V P]

/-!
### `μHE[d]` agree with the volume measure on inner product spaces
-/

theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume (d : ℕ) :
    (μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) = volume := by
  rw [euclideanHausdorffMeasure_def, ← isAddLeftInvariant_eq_smul]

theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume :
    (μHE[Module.finrank ℝ V] : Measure V) = volume := by
  rw [← (stdOrthonormalBasis ℝ V).measurePreserving_repr_symm.map_eq,
    ← (stdOrthonormalBasis ℝ V).repr.toIsometryEquiv
      |>.symm.measurePreserving_euclideanHausdorffMeasure _ |>.map_eq,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  simp

/-!
### `μHE[d]` on an affine space matches the volume measure on the associated inner product space.
-/
/- We may want to endow an affine space with a `MeasureSpace` that transfers `volume` from its
associated inner product space. If it is implemented, we can unify this lemma with the previous one.
-/
theorem EuclideanGeometry.euclideanHausdorffMeasure_eq (p : P) :
    μHE[Module.finrank ℝ V] = volume.map (IsometryEquiv.vaddConst p) := by
  have h := (IsometryEquiv.vaddConst p)
    |>.measurePreserving_euclideanHausdorffMeasure (Module.finrank ℝ V) |>.map_eq
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  exact h.symm

theorem EuclideanGeometry.measurePreserving_vaddConst (p : P) :
    MeasurePreserving (IsometryEquiv.vaddConst p) volume μHE[Module.finrank ℝ V] where
  measurable := (IsometryEquiv.vaddConst p).toHomeomorph.measurable
  map_eq := (euclideanHausdorffMeasure_eq p).symm

/-!
### `μHE[d]` is preserved through subspace inclusion
-/

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
theorem AffineSubspace.euclideanHausdorffMeasure_coe_image (d : ℕ) (s : AffineSubspace ℝ P)
    (t : Set s) : μHE[d] (Subtype.val '' t) = μHE[d] t :=
  isometry_subtype_coe.euclideanHausdorffMeasure_image _

/-!
### `μHE[d]` is translation invariant
-/

instance {α : Type*} [AddGroup α] [AddAction α X] [IsIsometricVAdd α X] (d : ℕ) :
    VAddInvariantMeasure α X μHE[d] := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

instance [AddGroup X] [IsIsometricVAdd X X] (d : ℕ) :
    (μHE[d] : Measure X).IsAddLeftInvariant := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

instance [AddGroup X] [IsIsometricVAdd Xᵃᵒᵖ X] (d : ℕ) :
    (μHE[d] : Measure X).IsAddRightInvariant := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance
