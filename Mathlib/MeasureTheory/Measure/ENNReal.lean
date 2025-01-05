/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# MeasureSpace instance on NNReal and ENNReal

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open scoped ENNReal NNReal

open MeasureTheory Set

namespace NNReal

variable {a b : ℝ≥0}

@[simp]
lemma toReal_Ico : toReal '' (Ico a b) = Ico (a : ℝ) b := image_subtype_val_Ico (s := Ici 0) _ _

@[simp]
lemma toReal_Icc : toReal '' (Icc a b) = Icc (a : ℝ) b := image_subtype_val_Icc (s := Ici 0) _ _

@[simp]
lemma toReal_Ioo : toReal '' (Ioo a b) = Ioo (a : ℝ) b := image_subtype_val_Ioo (s := Ici 0) _ _

@[simp]
lemma toReal_Ioc : toReal '' (Ioc a b) = Ioc (a : ℝ) b := image_subtype_val_Ioc (s := Ici 0) _ _

@[simp] lemma toReal_Ici : toReal '' (Ici a) = Ici (a : ℝ) := image_subtype_val_Ici_Ici _

@[simp] lemma toReal_Ioi : toReal '' (Ioi a) = Ioi (a : ℝ) := image_subtype_val_Ici_Ioi _

@[simp] lemma toReal_Iic : toReal '' (Iic a) = Icc (0 : ℝ) (a : ℝ) := image_subtype_val_Ici_Iic _

@[simp] lemma toReal_Iio : toReal '' (Iio a) = Ico (0 : ℝ) (a : ℝ) := image_subtype_val_Ici_Iio _

@[simp]
lemma range_toReal : range toReal = Ici 0 := by
  ext x
  simp only [mem_range, mem_Ici]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩
  rw [← hy]
  exact y.prop

noncomputable
instance : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

lemma volume_apply_eq_volume_toReal {s : Set ℝ≥0} : volume s = volume (toReal '' s) :=
  comap_subtype_coe_apply measurableSet_Ici _ _

@[simp]
theorem volume_Ico : volume (Ico a b) = b - a := by
  simp [volume_apply_eq_volume_toReal, ENNReal.ofReal_sub]

@[simp]
theorem volume_Icc : volume (Icc a b) = b - a := by
  simp [volume_apply_eq_volume_toReal, ENNReal.ofReal_sub]

@[simp]
theorem volume_Ioo : volume (Ioo a b) = b - a := by
  simp [volume_apply_eq_volume_toReal, ENNReal.ofReal_sub]

@[simp]
theorem volume_Ioc : volume (Ioc a b) = b - a := by
  simp [volume_apply_eq_volume_toReal, ENNReal.ofReal_sub]

@[simp] theorem volume_Ici : volume (Ici a) = ∞ := by simp [volume_apply_eq_volume_toReal]

@[simp] theorem volume_Ioi : volume (Ioi a) = ∞ := by simp [volume_apply_eq_volume_toReal]

@[simp] theorem volume_Iic : volume (Iic a) = a := by simp [volume_apply_eq_volume_toReal]

@[simp] theorem volume_Iio : volume (Iio a) = a := by simp [volume_apply_eq_volume_toReal]

@[simp] theorem volume_singleton : volume ({a} : Set ℝ≥0) = 0 := by simp [← Icc_self a, - Icc_self]

@[simp] theorem volume_univ : volume (univ : Set ℝ≥0) = ∞ := by simp [volume_apply_eq_volume_toReal]

instance noAtoms_volume : NoAtoms (volume : Measure ℝ≥0) := ⟨fun _ => volume_singleton⟩

instance locallyFinite_volume : IsLocallyFiniteMeasure (volume : Measure ℝ≥0) where
  finiteAtNhds x := ⟨Iio (x + 1), IsOpen.mem_nhds isOpen_Iio (by simp), by simp⟩

instance isFiniteMeasure_restrict_Icc (x y : ℝ≥0) :
    IsFiniteMeasure (volume.restrict (Icc x y)) where
  measure_univ_lt_top := by
    simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, volume_Icc]
    exact mod_cast ENNReal.coe_lt_top

instance isFiniteMeasure_restrict_Ico (x y : ℝ≥0) :
    IsFiniteMeasure (volume.restrict (Ico x y)) where
  measure_univ_lt_top := by
    simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, volume_Ico]
    exact mod_cast ENNReal.coe_lt_top

instance isFiniteMeasure_restrict_Ioc (x y : ℝ≥0) :
    IsFiniteMeasure (volume.restrict (Ioc x y)) where
  measure_univ_lt_top := by
    simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, volume_Ioc]
    exact mod_cast ENNReal.coe_lt_top

instance isFiniteMeasure_restrict_Ioo (x y : ℝ≥0) :
    IsFiniteMeasure (volume.restrict (Ioo x y)) where
  measure_univ_lt_top := by
    simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, volume_Ioo]
    exact mod_cast ENNReal.coe_lt_top

end NNReal

namespace ENNReal

variable {a b : ℝ≥0∞}

@[simp] lemma preimage_ofNNReal_Ico {a b : ℝ≥0} : ofNNReal ⁻¹' (Ico a b) = Ico a b := by ext; simp

@[simp] lemma preimage_ofNNReal_Ico_top {a : ℝ≥0} : ofNNReal ⁻¹' (Ico a ∞) = Ici a := by ext; simp

@[simp] lemma preimage_ofNNReal_Ioo {a b : ℝ≥0} : ofNNReal ⁻¹' (Ioo a b) = Ioo a b := by ext; simp

@[simp] lemma preimage_ofNNReal_Ioo_top {a : ℝ≥0} : ofNNReal ⁻¹' (Ioo a ∞) = Ioi a := by ext; simp

@[simp] lemma preimage_ofNNReal_Ioc {a b : ℝ≥0} : ofNNReal ⁻¹' (Ioc a b) = Ioc a b := by ext; simp

@[simp] lemma preimage_ofNNReal_Ioc_top {a : ℝ≥0} : ofNNReal ⁻¹' (Ioc a ∞) = Ioi a := by ext; simp

@[simp] lemma preimage_ofNNReal_Icc {a b : ℝ≥0} : ofNNReal ⁻¹' (Icc a b) = Icc a b := by ext; simp

@[simp] lemma preimage_ofNNReal_Icc_top {a : ℝ≥0} : ofNNReal ⁻¹' (Icc a ∞) = Ici a := by ext; simp

@[simp] lemma preimage_ofNNReal_Ici {a : ℝ≥0} : ofNNReal ⁻¹' (Ici a) = Ici a := by ext; simp

@[simp] lemma preimage_ofNNReal_Ioi {a : ℝ≥0} : ofNNReal ⁻¹' (Ioi a) = Ioi a := by ext; simp

@[simp] lemma preimage_ofNNReal_Iic {a : ℝ≥0} : ofNNReal ⁻¹' (Iic a) = Iic a := by ext; simp

@[simp] lemma preimage_ofNNReal_Iio {a : ℝ≥0} : ofNNReal ⁻¹' (Iio a) = Iio a := by ext; simp

@[simp] lemma preimage_ofNNReal_Iio_top : ofNNReal ⁻¹' (Iio ∞) = univ := by ext; simp

@[simp] lemma preimage_ofNNReal_singleton_top : ofNNReal ⁻¹' {∞} = ∅ := by ext; simp

noncomputable
instance : MeasureSpace ℝ≥0∞ where
  volume := (volume : Measure ℝ≥0).map (↑)

lemma volume_apply_eq_volume_ofNNReal {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    volume s = volume (ofNNReal ⁻¹' s) := by
  simp_rw [volume, Measure.map_apply measurable_coe_nnreal_ennreal hs]

@[simp]
theorem volume_Ico : volume (Ico a b) = b - a := by
  rw [volume_apply_eq_volume_ofNNReal measurableSet_Ico]
  cases b <;> cases a <;> simp [ENNReal.sub_top]

@[simp]
theorem volume_Icc : volume (Icc a b) = b - a := by
  rw [volume_apply_eq_volume_ofNNReal measurableSet_Icc]
  cases b <;> cases a <;> simp [ENNReal.sub_top]

@[simp]
theorem volume_Ioo : volume (Ioo a b) = b - a := by
  rw [volume_apply_eq_volume_ofNNReal measurableSet_Ioo]
  cases b <;> cases a <;> simp [ENNReal.sub_top]

@[simp]
theorem volume_Ioc : volume (Ioc a b) = b - a := by
  rw [volume_apply_eq_volume_ofNNReal measurableSet_Ioc]
  cases b <;> cases a <;> simp [ENNReal.sub_top]

@[simp]
theorem volume_singleton : volume ({a} : Set ℝ≥0∞) = 0 := by simp [← Icc_self a, - Icc_self]

@[simp]
theorem volume_univ : volume (univ : Set ℝ≥0∞) = ∞ := by
  simp [volume_apply_eq_volume_ofNNReal MeasurableSet.univ]

-- The case `a = ∞` is handled by `volume_singleton`
@[simp]
theorem volume_Ici {a : ℝ≥0} : volume (Ici (a : ℝ≥0∞)) = ∞ := by
  simp [volume_apply_eq_volume_ofNNReal measurableSet_Ici]

@[simp]
theorem volume_Ioi {a : ℝ≥0} : volume (Ioi a) = ∞ := by
  simp [volume_apply_eq_volume_ofNNReal measurableSet_Ici]

@[simp]
theorem volume_Iic : volume (Iic a) = a := by
  simp [volume_apply_eq_volume_ofNNReal measurableSet_Iic]
  cases a <;> simp

@[simp]
theorem volume_Iio : volume (Iio a) = a := by
  simp [volume_apply_eq_volume_ofNNReal measurableSet_Iio]
  cases a <;> simp

instance noAtoms_volume : NoAtoms (volume : Measure ℝ≥0∞) := ⟨fun _ => volume_singleton⟩

end ENNReal
