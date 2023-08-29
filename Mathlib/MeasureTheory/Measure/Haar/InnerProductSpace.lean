/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

#align_import measure_theory.measure.haar.inner_product_space from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Volume forms and measures on inner product spaces

A volume form induces a Lebesgue measure on general finite-dimensional real vector spaces. In this
file, we discuss the specific situation of inner product spaces, where an orientation gives
rise to a canonical volume form. We show that the measure coming from this volume form gives
measure `1` to the parallelepiped spanned by any orthonormal basis, and that it coincides with
the canonical `volume` from the `MeasureSpace` instance.
-/


open FiniteDimensional MeasureTheory MeasureTheory.Measure Set

variable {ι F : Type*}

variable [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

section

variable {m n : ℕ} [_i : Fact (finrank ℝ F = n)]

/-- The volume form coming from an orientation in an inner product space gives measure `1` to the
parallelepiped associated to any orthonormal basis. This is a rephrasing of
`abs_volumeForm_apply_of_orthonormal` in terms of measures. -/
theorem Orientation.measure_orthonormalBasis (o : Orientation ℝ F (Fin n))
    (b : OrthonormalBasis ι ℝ F) : o.volumeForm.measure (parallelepiped b) = 1 := by
  have e : ι ≃ Fin n := by
    refine' Fintype.equivFinOfCardEq _
    rw [← _i.out, finrank_eq_card_basis b.toBasis]
  have A : ⇑b = b.reindex e ∘ e := by
    ext x
    simp only [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  rw [A, parallelepiped_comp_equiv, AlternatingMap.measure_parallelepiped,
    o.abs_volumeForm_apply_of_orthonormal, ENNReal.ofReal_one]
#align orientation.measure_orthonormal_basis Orientation.measure_orthonormalBasis

/-- In an oriented inner product space, the measure coming from the canonical volume form
associated to an orientation coincides with the volume. -/
theorem Orientation.measure_eq_volume (o : Orientation ℝ F (Fin n)) :
    o.volumeForm.measure = volume := by
  have A : o.volumeForm.measure (stdOrthonormalBasis ℝ F).toBasis.parallelepiped = 1 :=
    Orientation.measure_orthonormalBasis o (stdOrthonormalBasis ℝ F)
  rw [addHaarMeasure_unique o.volumeForm.measure
    (stdOrthonormalBasis ℝ F).toBasis.parallelepiped, A, one_smul]
  simp only [volume, Basis.addHaar]
  -- 🎉 no goals
#align orientation.measure_eq_volume Orientation.measure_eq_volume

end

/-- The volume measure in a finite-dimensional inner product space gives measure `1` to the
parallelepiped spanned by any orthonormal basis. -/
theorem OrthonormalBasis.volume_parallelepiped (b : OrthonormalBasis ι ℝ F) :
    volume (parallelepiped b) = 1 := by
  haveI : Fact (finrank ℝ F = finrank ℝ F) := ⟨rfl⟩
  -- ⊢ ↑↑volume (parallelepiped ↑b) = 1
  let o := (stdOrthonormalBasis ℝ F).toBasis.orientation
  -- ⊢ ↑↑volume (parallelepiped ↑b) = 1
  rw [← o.measure_eq_volume]
  -- ⊢ ↑↑(AlternatingMap.measure (Orientation.volumeForm o)) (parallelepiped ↑b) = 1
  exact o.measure_orthonormalBasis b
  -- 🎉 no goals
#align orthonormal_basis.volume_parallelepiped OrthonormalBasis.volume_parallelepiped
