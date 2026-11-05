/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Convex.Parallelepiped
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Additive Haar measure constructed from a basis

Given a basis of a finite-dimensional real vector space, we define the corresponding Lebesgue
measure, which gives measure `1` to the parallelepiped spanned by the basis.

## Main definitions

* `Basis.parallelepiped` is the parallelepiped associated to a basis, seen as a compact set with
  nonempty interior.
* `Basis.addHaar` is the Lebesgue measure associated to a basis, giving measure `1` to the
  corresponding parallelepiped.

In particular, we declare a `MeasureSpace` instance on any finite-dimensional inner product space,
by using the Lebesgue measure associated to some orthonormal basis (which is in fact independent
of the basis).
-/

@[expose] public section


open Set TopologicalSpace MeasureTheory MeasureTheory.Measure Module

noncomputable section

variable {ι ι' E F : Type*}

section Fintype

variable [Fintype ι] [Fintype ι']

-- The parallelepiped associated to an orthonormal basis of `ℝ` is either `[0, 1]` or `[-1, 0]`.
theorem parallelepiped_orthonormalBasis_one_dim (b : OrthonormalBasis ι ℝ ℝ) :
    parallelepiped ℝ b = Icc 0 1 ∨ parallelepiped ℝ b = Icc (-1) 0 := by
  have : Unique ι := b.toBasis.unique
  rw [parallelepiped_unique, segment_eq_uIcc]
  exact (orthonormalBasis_one_dim b).imp (by simp [·]) (by simp [·])

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Module.Basis

/-- The parallelepiped spanned by a basis, as a compact set with nonempty interior. -/
def parallelepiped (b : Basis ι ℝ E) : PositiveCompacts E where
  carrier := _root_.parallelepiped ℝ b
  isCompact' := isCompact_parallelepiped b
  interior_nonempty' := by
    use b.equivFunL.symm fun _ ↦ 1 / 2
    rw [mem_interior]
    refine ⟨b.equivFunL ⁻¹' univ.pi fun _ ↦ Ioo 0 1, ?_, ?_, by norm_num⟩
    · intro x hx
      simpa [parallelepiped_basis_eq] using fun i ↦ mem_Icc_of_Ioo (mem_univ_pi.mp hx i)
    · exact (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo).preimage b.equivFunL.continuous

@[simp]
theorem coe_parallelepiped (b : Basis ι ℝ E) :
    (b.parallelepiped : Set E) = _root_.parallelepiped ℝ b := rfl

@[simp]
theorem parallelepiped_reindex (b : Basis ι ℝ E) (e : ι ≃ ι') :
    (b.reindex e).parallelepiped = b.parallelepiped :=
  PositiveCompacts.ext <| by simp

theorem parallelepiped_map (b : Basis ι ℝ E) (e : E ≃ₗ[ℝ] F) :
    (b.map e).parallelepiped = b.parallelepiped.map e
    (haveI := b.finiteDimensional_of_finite
    LinearMap.continuous_of_finiteDimensional e.toLinearMap)
    (haveI := (b.map e).finiteDimensional_of_finite
    LinearMap.isOpenMap_of_finiteDimensional _ e.surjective) :=
  PositiveCompacts.ext (image_parallelepiped e.toLinearMap _).symm

theorem prod_parallelepiped (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
    (v.prod w).parallelepiped = v.parallelepiped ×ˢ w.parallelepiped :=
  PositiveCompacts.ext <|
    congr(_root_.parallelepiped ℝ $(funext (v.prod_apply w))).trans (parallelepiped_prod _ _)

variable [MeasurableSpace E] [BorelSpace E]

/-- The Lebesgue measure associated to a basis, giving measure `1` to the parallelepiped spanned
by the basis. -/
@[no_expose] def addHaar (b : Basis ι ℝ E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped

lemma addHaar_def (b : Basis ι ℝ E) : addHaar b = Measure.addHaarMeasure b.parallelepiped := (rfl)

instance _root_.isAddHaarMeasure_basis_addHaar (b : Basis ι ℝ E) : IsAddHaarMeasure b.addHaar :=
  Measure.isAddHaarMeasure_addHaarMeasure _

instance (b : Basis ι ℝ E) : SigmaFinite b.addHaar :=
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  sigmaFinite_addHaarMeasure

/-- Let `μ` be a σ-finite left invariant measure on `E`. Then `μ` is equal to the Haar measure
defined by `b` iff the parallelepiped defined by `b` has measure `1` for `μ`. -/
theorem addHaar_eq_iff [SecondCountableTopology E] (b : Basis ι ℝ E) (μ : Measure E)
    [SigmaFinite μ] [IsAddLeftInvariant μ] :
    b.addHaar = μ ↔ μ b.parallelepiped = 1 :=
  addHaarMeasure_eq_iff b.parallelepiped μ

@[simp]
theorem addHaar_reindex (b : Basis ι ℝ E) (e : ι ≃ ι') :
    (b.reindex e).addHaar = b.addHaar := by
  rw [Basis.addHaar, b.parallelepiped_reindex e, ← Basis.addHaar]

theorem addHaar_self (b : Basis ι ℝ E) : b.addHaar (_root_.parallelepiped ℝ b) = 1 :=
  addHaarMeasure_self

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopologyEither E F]

theorem prod_addHaar (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
    (v.prod w).addHaar = v.addHaar.prod w.addHaar := by
  have : FiniteDimensional ℝ E := v.finiteDimensional_of_finite
  have : FiniteDimensional ℝ F := w.finiteDimensional_of_finite
  simp [(v.prod w).addHaar_eq_iff, Basis.prod_parallelepiped, Basis.addHaar_self]

end Module.Basis

end Fintype

/-- A finite-dimensional inner product space has a canonical measure, the Lebesgue measure giving
volume `1` to the parallelepiped spanned by any orthonormal basis. We define the measure using
some arbitrary choice of orthonormal basis. The fact that it works with any orthonormal basis
is proved in `orthonormalBasis.volume_parallelepiped`.

This instance creates:

- a potential non-defeq diamond with the natural instance for `MeasureSpace (ULift E)`,
  which does not exist in Mathlib at the moment;

- a diamond with the existing instance `MeasureTheory.Measure.instMeasureSpacePUnit`.

However, we've decided not to refactor until one of these diamonds starts creating issues, see
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Hausdorff.20measure.20normalisation
-/
instance (priority := 100) measureSpaceOfInnerProductSpace [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    MeasureSpace E where volume := (stdOrthonormalBasis ℝ E).toBasis.addHaar

instance [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : IsAddHaarMeasure (volume : Measure E) :=
  isAddHaarMeasure_basis_addHaar _

/- This instance should not be necessary, but Lean has difficulties to find it in product
situations if we do not declare it explicitly. -/
instance Real.measureSpace : MeasureSpace ℝ := by infer_instance
