/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Totally real and totally complex number fields

This file defines the type of totally real and totally complex number fields.

## Main Definitions and Results

* `NumberField.IsTotallyReal`: a number field `K` is totally real if all of its infinite places
  are real. In other words, the image of every ring homomorphism `K → ℂ` is a subset of `ℝ`.
* `NumberField.IsTotallyComplex`: a number field `K` is totally complex if all of its infinite
  places are complex.
* `NumberField.maximalRealSubfield`: the maximal real subfield of `K`. It is totally real,
  see `NumberField.isTotallyReal_maximalRealSubfield`, and contains all the other totally real
  subfields of `K`, see `NumberField.IsTotallyReal.le_maximalRealSubfield`

## Tags

number field, infinite places, totally real, totally complex
-/

namespace NumberField

open InfinitePlace Module

section TotallyRealField

/-

## Totally real number fields

-/

/-- A number field `K` is totally real if all of its infinite places
are real. In other words, the image of every ring homomorphism `K → ℂ`
is a subset of `ℝ`. -/
@[mk_iff] class IsTotallyReal (K : Type*) [Field K] [NumberField K] where
  isReal : ∀ v : InfinitePlace K, v.IsReal

variable {F : Type*} [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K]

theorem nrComplexPlaces_eq_zero_iff :
    nrComplexPlaces K = 0 ↔ IsTotallyReal K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyReal_iff]

theorem IsTotallyReal.complexEmbedding_isReal [IsTotallyReal K] (φ : K →+* ℂ) :
    ComplexEmbedding.IsReal φ :=
  isReal_mk_iff.mp <| isReal (InfinitePlace.mk φ)

theorem IsTotallyReal.ofRingEquiv [IsTotallyReal F] (f : F ≃+* K) : IsTotallyReal K where
  isReal _ := (isReal_comap_iff f).mp <| IsTotallyReal.isReal _

variable (F K) in
theorem IsTotallyReal.of_algebra [IsTotallyReal K] [Algebra F K] : IsTotallyReal F where
  isReal w := by
    obtain ⟨W, rfl⟩ : ∃ W : InfinitePlace K, W.comap (algebraMap F K) = w := comap_surjective w
    exact IsReal.comap _ (IsTotallyReal.isReal W)

instance [IsTotallyReal K] (F : IntermediateField ℚ K) : IsTotallyReal F :=
  IsTotallyReal.of_algebra F K

instance [IsTotallyReal K] (F : Subfield K) : IsTotallyReal F :=
  IsTotallyReal.of_algebra F K

variable (K)

@[simp]
theorem IsTotallyReal.nrComplexPlaces_eq_zero [h : IsTotallyReal K] :
    nrComplexPlaces K = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr h

protected theorem IsTotallyReal.finrank [h : IsTotallyReal K] :
    finrank ℚ K = nrRealPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, nrComplexPlaces_eq_zero_iff.mpr h, mul_zero, add_zero]

instance : IsTotallyReal ℚ where
  isReal v := by
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact Rat.isReal_infinitePlace

section maximalRealSubfield

open ComplexEmbedding

/--
The maximal real subfield of `K`. It is totally real,
see `NumberField.isTotallyReal_maximalRealSubfield`, and contains all the other totally real
subfields of `K`, see `NumberField.IsTotallyReal.le_maximalRealSubfield`.
-/
def maximalRealSubfield : Subfield K where
  carrier := {x | ∀ φ : K →+* ℂ, star (φ x) = φ x}
  mul_mem' hx hy _ := by rw [map_mul, star_mul, hx, hy, mul_comm]
  one_mem' := by simp
  add_mem' hx hy _ := by rw [map_add, star_add, hx, hy]
  zero_mem' := by simp
  neg_mem' := by simp
  inv_mem' := by simp

instance isTotallyReal_maximalRealSubfield :
    IsTotallyReal (maximalRealSubfield K) where
  isReal w := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [RingHom.star_apply, ← lift_algebraMap_apply K w.embedding]
    exact x.prop _

variable {K}

theorem IsTotallyReal.le_maximalRealSubfield (E : Subfield K) [IsTotallyReal E] :
    E ≤ maximalRealSubfield K := by
  intro x hx φ
  rw [show φ x = (φ.comp E.subtype) ⟨x, hx⟩ by simp, RCLike.star_def, ← conjugate_coe_eq]
  refine RingHom.congr_fun ?_ _
  exact ComplexEmbedding.isReal_iff.mp  <| isReal_mk_iff.mp <| isReal _

theorem isTotallyReal_iff_le_maximalRealSubfield {E : Subfield K} :
    IsTotallyReal E ↔ E ≤ maximalRealSubfield K :=
  ⟨fun h ↦ h.le_maximalRealSubfield, fun h ↦ IsTotallyReal.ofRingEquiv
    (RingEquiv.ofBijective _ (Subfield.inclusion h).rangeRestrictField_bijective).symm⟩

instance isTotallyReal_sup {E F : Subfield K} [IsTotallyReal E] [IsTotallyReal F] :
    IsTotallyReal (E ⊔ F : Subfield K) := by
  simp_all [isTotallyReal_iff_le_maximalRealSubfield]

instance isTotallyReal_iSup {ι : Type*} {k : ι → Subfield K} [∀ i, IsTotallyReal (k i)] :
    IsTotallyReal (⨆ i, k i : Subfield K) := by
  simp_all [isTotallyReal_iff_le_maximalRealSubfield]

end maximalRealSubfield

end TotallyRealField

section TotallyComplexField

/-
## Totally complex number fields
-/

open InfinitePlace

/--
A number field `K` is totally complex if all of its infinite places are complex.
-/
@[mk_iff] class IsTotallyComplex (K : Type*) [Field K] [NumberField K] where
  isComplex : ∀ v : InfinitePlace K, v.IsComplex

variable {F : Type*} [Field F] {K : Type*} [Field K] [NumberField K] [Algebra F K]

theorem nrRealPlaces_eq_zero_iff :
    nrRealPlaces K = 0 ↔ IsTotallyComplex K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyComplex_iff]

theorem IsTotallyComplex.complexEmbedding_not_isReal [IsTotallyComplex K] (φ : K →+* ℂ) :
    ¬ ComplexEmbedding.IsReal φ :=
  isReal_mk_iff.not.mp <| not_isReal_iff_isComplex.mpr <| isComplex (InfinitePlace.mk φ)

variable (K)

@[simp]
theorem IsTotallyComplex.nrRealPlaces_eq_zero [h : IsTotallyComplex K] :
    nrRealPlaces K = 0 :=
  nrRealPlaces_eq_zero_iff.mpr h

protected theorem IsTotallyComplex.finrank [h : IsTotallyComplex K] :
    finrank ℚ K = 2 * nrComplexPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, nrRealPlaces_eq_zero_iff.mpr h, zero_add]

end TotallyComplexField

end NumberField
