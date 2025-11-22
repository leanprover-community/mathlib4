/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Volume forms and measures on inner product spaces

A volume form induces a Lebesgue measure on general finite-dimensional real vector spaces. In this
file, we discuss the specific situation of inner product spaces, where an orientation gives
rise to a canonical volume form. We show that the measure coming from this volume form gives
measure `1` to the parallelepiped spanned by any orthonormal basis, and that it coincides with
the canonical `volume` from the `MeasureSpace` instance.
-/

@[expose] public section

open Module MeasureTheory MeasureTheory.Measure Set WithLp

variable {ι E F : Type*}

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

namespace LinearIsometryEquiv

variable (f : E ≃ₗᵢ[ℝ] F)

/-- Every linear isometry equivalence is a measurable equivalence. -/
def toMeasurableEquiv : E ≃ᵐ F where
  toEquiv := f
  measurable_toFun := f.continuous.measurable
  measurable_invFun := f.symm.continuous.measurable

@[simp] theorem coe_toMeasurableEquiv : (f.toMeasurableEquiv : E → F) = f := rfl

@[simp] theorem toMeasurableEquiv_symm : f.symm.toMeasurableEquiv = f.toMeasurableEquiv.symm := rfl

@[simp] lemma coe_symm_toMeasurableEquiv : ⇑f.toMeasurableEquiv.symm = f.symm := rfl

end LinearIsometryEquiv

variable [Fintype ι]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

section
variable {m n : ℕ} [_i : Fact (finrank ℝ F = n)]

/-- The volume form coming from an orientation in an inner product space gives measure `1` to the
parallelepiped associated to any orthonormal basis. This is a rephrasing of
`abs_volumeForm_apply_of_orthonormal` in terms of measures. -/
theorem Orientation.measure_orthonormalBasis (o : Orientation ℝ F (Fin n))
    (b : OrthonormalBasis ι ℝ F) : o.volumeForm.measure (parallelepiped b) = 1 := by
  have e : ι ≃ Fin n := by
    refine Fintype.equivFinOfCardEq ?_
    rw [← _i.out, finrank_eq_card_basis b.toBasis]
  have A : ⇑b = b.reindex e ∘ e := by
    ext x
    simp only [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  rw [A, parallelepiped_comp_equiv, AlternatingMap.measure_parallelepiped,
    o.abs_volumeForm_apply_of_orthonormal, ENNReal.ofReal_one]

/-- In an oriented inner product space, the measure coming from the canonical volume form
associated to an orientation coincides with the volume. -/
theorem Orientation.measure_eq_volume (o : Orientation ℝ F (Fin n)) :
    o.volumeForm.measure = volume := by
  have A : o.volumeForm.measure (stdOrthonormalBasis ℝ F).toBasis.parallelepiped = 1 :=
    Orientation.measure_orthonormalBasis o (stdOrthonormalBasis ℝ F)
  rw [addHaarMeasure_unique o.volumeForm.measure
    (stdOrthonormalBasis ℝ F).toBasis.parallelepiped, A, one_smul]
  simp only [volume, Basis.addHaar]

end

/-- The volume measure in a finite-dimensional inner product space gives measure `1` to the
parallelepiped spanned by any orthonormal basis. -/
theorem OrthonormalBasis.volume_parallelepiped (b : OrthonormalBasis ι ℝ F) :
    volume (parallelepiped b) = 1 := by
  haveI : Fact (finrank ℝ F = finrank ℝ F) := ⟨rfl⟩
  let o := (stdOrthonormalBasis ℝ F).toBasis.orientation
  rw [← o.measure_eq_volume]
  exact o.measure_orthonormalBasis b

/-- The Haar measure defined by any orthonormal basis of a finite-dimensional inner product space
is equal to its volume measure. -/
theorem OrthonormalBasis.addHaar_eq_volume {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (b : OrthonormalBasis ι ℝ F) :
    b.toBasis.addHaar = volume := by
  rw [Basis.addHaar_eq_iff]
  exact b.volume_parallelepiped

/-- An orthonormal basis of a finite-dimensional inner product space defines a measurable
equivalence between the space and the Euclidean space of the same dimension. -/
noncomputable def OrthonormalBasis.measurableEquiv (b : OrthonormalBasis ι ℝ F) :
    F ≃ᵐ EuclideanSpace ℝ ι := b.repr.toHomeomorph.toMeasurableEquiv

/-- The measurable equivalence defined by an orthonormal basis is volume preserving. -/
theorem OrthonormalBasis.measurePreserving_measurableEquiv (b : OrthonormalBasis ι ℝ F) :
    MeasurePreserving b.measurableEquiv volume volume := by
  convert (b.measurableEquiv.symm.measurable.measurePreserving _).symm
  rw [← (EuclideanSpace.basisFun ι ℝ).addHaar_eq_volume]
  erw [MeasurableEquiv.coe_toEquiv_symm, Basis.map_addHaar _ b.repr.symm.toContinuousLinearEquiv]
  exact b.addHaar_eq_volume.symm

theorem OrthonormalBasis.measurePreserving_repr (b : OrthonormalBasis ι ℝ F) :
    MeasurePreserving b.repr volume volume := b.measurePreserving_measurableEquiv

theorem OrthonormalBasis.measurePreserving_repr_symm (b : OrthonormalBasis ι ℝ F) :
    MeasurePreserving b.repr.symm volume volume := b.measurePreserving_measurableEquiv.symm

section PiLp

variable (ι : Type*)

/-- `WithLp.equiv` as a `MeasurableEquiv`. -/
@[deprecated MeasurableEquiv.toLp (since := "2025-11-02")]
protected def EuclideanSpace.measurableEquiv : EuclideanSpace ℝ ι ≃ᵐ (ι → ℝ) :=
  (MeasurableEquiv.toLp 2 (ι → ℝ)).symm

set_option linter.deprecated false in
@[deprecated MeasurableEquiv.coe_toLp (since := "2025-11-02")]
theorem EuclideanSpace.measurableEquiv_toEquiv :
    (EuclideanSpace.measurableEquiv ι).toEquiv = WithLp.equiv 2 (ι → ℝ) := rfl

set_option linter.deprecated false in
@[deprecated MeasurableEquiv.coe_toLp (since := "2025-11-02")]
theorem EuclideanSpace.coe_measurableEquiv :
    ⇑(EuclideanSpace.measurableEquiv ι) = ofLp := rfl

set_option linter.deprecated false in
@[deprecated MeasurableEquiv.coe_toLp_symm (since := "2025-11-02")]
theorem EuclideanSpace.coe_measurableEquiv_symm :
    ⇑(EuclideanSpace.measurableEquiv ι).symm = toLp 2 := rfl

variable [Fintype ι]

/-- The measure equivalence between `EuclideanSpace ℝ ι` and `ι → ℝ` is volume preserving. -/
theorem EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp :
    MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)).symm := by
  suffices volume = map (MeasurableEquiv.toLp 2 (ι → ℝ)) volume by
    convert ((MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.measurePreserving _).symm
  rw [← addHaarMeasure_eq_volume_pi, ← Basis.parallelepiped_basisFun, ← Basis.addHaar_def,
    MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ, Basis.map_addHaar]
  exact (EuclideanSpace.basisFun _ _).addHaar_eq_volume.symm

@[deprecated (since := "2025-07-26")] alias EuclideanSpace.volume_preserving_measurableEquiv :=
  EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp

/-- A copy of `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`
for the canonical spelling of the equivalence. -/
theorem PiLp.volume_preserving_ofLp : MeasurePreserving (@ofLp 2 (ι → ℝ)) :=
  EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι

/-- The reverse direction of `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`, since
`MeasurePreserving.symm` only works for `MeasurableEquiv`s. -/
theorem PiLp.volume_preserving_toLp : MeasurePreserving (@toLp 2 (ι → ℝ)) :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm

lemma volume_euclideanSpace_eq_dirac [IsEmpty ι] :
    (volume : Measure (EuclideanSpace ℝ ι)) = Measure.dirac 0 := by
  rw [← (PiLp.volume_preserving_toLp ι).map_eq, volume_pi_eq_dirac 0,
    map_dirac (measurable_toLp 2 _), toLp_zero]

end PiLp

namespace LinearIsometryEquiv

/-- Every linear isometry on a real finite-dimensional Hilbert space is measure-preserving. -/
theorem measurePreserving (f : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving f := by
  refine ⟨f.continuous.measurable, ?_⟩
  rcases exists_orthonormalBasis ℝ E with ⟨w, b, _hw⟩
  erw [← OrthonormalBasis.addHaar_eq_volume b, ← OrthonormalBasis.addHaar_eq_volume (b.map f),
    Basis.map_addHaar _ f.toContinuousLinearEquiv]
  congr

end LinearIsometryEquiv
