/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

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

TODO: show the scaling factor equals to $\pi^(d/2) / (2^d \Gamma (d/2+1))$, the volume ratio between
a ball and a cube.

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
on a Euclidean space. While this is defined on any (e)metric space, it is intended to be
used for affine space associated with an inner product space, where it agrees with the volume
measure on the inner product space.
-/
noncomputable
def MeasureTheory.Measure.euclideanHausdorffMeasure (d : ℕ) : Measure X :=
  addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] • μH[d]

@[inherit_doc]
scoped[MeasureTheory] notation "μHE[" d "]" => MeasureTheory.Measure.euclideanHausdorffMeasure d

/-!
### `μHE[d]` is preserved through isometry
-/

theorem IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (e : X ≃ᵢ Y) (d : ℕ) :
    MeasurePreserving e μHE[d] μHE[d] :=
  (IsometryEquiv.measurePreserving_hausdorffMeasure e d).smul_measure _

theorem Isometry.euclideanHausdorffMeasure_image {f : X → Y} {d : ℕ} (hf : Isometry f) (s : Set X) :
    μHE[d] (f '' s) = μHE[d] s := by
  unfold euclideanHausdorffMeasure
  simp_rw [smul_apply]
  rw [Isometry.hausdorffMeasure_image hf (by simp)]

theorem Isometry.euclideanHausdorffMeasure_preimage {f : X → Y} {d : ℕ} (hf : Isometry f)
    (s : Set Y) : μHE[d] (f ⁻¹' s) = μHE[d] (s ∩ Set.range f) := by
  unfold euclideanHausdorffMeasure
  simp_rw [smul_apply]
  rw [Isometry.hausdorffMeasure_preimage hf (by simp)]

theorem Isometry.map_euclideanHausdorffMeasure {f : X → Y} {d : ℕ} (hf : Isometry f) :
    μHE[d].map f = μHE[d].restrict (Set.range f) := by
  unfold euclideanHausdorffMeasure
  rw [Measure.map_smul, map_hausdorffMeasure hf (by simp), Measure.restrict_smul]

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional ℝ V]
variable [MetricSpace P] [MeasurableSpace P] [BorelSpace P] [NormedAddTorsor V P]

/-!
### `μHE[d]` agree with the volume measure on inner product spaces
-/

theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume (d : ℕ) :
    (μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) = volume := by
  rw [euclideanHausdorffMeasure, ← MeasureTheory.Measure.isAddLeftInvariant_eq_smul]

theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume :
    (μHE[Module.finrank ℝ V] : Measure V) = volume := by
  rw [← (stdOrthonormalBasis ℝ V).measurePreserving_repr_symm.map_eq]
  rw [← (stdOrthonormalBasis ℝ V).repr.toIsometryEquiv
      |>.symm.measurePreserving_euclideanHausdorffMeasure _ |>.map_eq]
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  rfl

/-!
### `μHE[d]` on an affine space matches the volume measure on the associated inner product space.
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
