/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Xavier Roblot
-/
module

public import Mathlib.FieldTheory.PrimeField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Totally real and totally complex number fields

This file defines the type of totally real and totally complex number fields.

## Main Definitions and Results

* `NumberField.IsTotallyReal`: a field `K` is totally real if all of its infinite places
  are real. In other words, the image of every ring homomorphism `K → ℂ` is a subset of `ℝ`.
* `NumberField.IsTotallyComplex`: a field `K` is totally complex if all of its infinite
  places are complex.
* `NumberField.maximalRealSubfield`: the maximal real subfield of `K`. It is totally real,
  see `NumberField.isTotallyReal_maximalRealSubfield`, and contains all the other totally real
  subfields of `K`, see `NumberField.IsTotallyReal.le_maximalRealSubfield`

## Tags

number field, infinite places, totally real, totally complex
-/

@[expose] public section

namespace NumberField

open InfinitePlace Module

section TotallyRealField

/-

## Totally real number fields

-/

/-- A field `K` is totally real if all of its infinite places are real. In other words,
the image of every ring homomorphism `K → ℂ` is a subset of `ℝ`. -/
@[mk_iff] class IsTotallyReal (K : Type*) [Field K] where
  isReal : ∀ v : InfinitePlace K, v.IsReal

variable {F : Type*} [Field F] {K : Type*} [Field K]

theorem nrComplexPlaces_eq_zero_iff [NumberField K] :
    nrComplexPlaces K = 0 ↔ IsTotallyReal K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyReal_iff]

theorem IsTotallyReal.complexEmbedding_isReal [IsTotallyReal K] (φ : K →+* ℂ) :
    ComplexEmbedding.IsReal φ :=
  isReal_mk_iff.mp <| isReal (InfinitePlace.mk φ)

@[simp]
theorem IsTotallyReal.mult_eq [IsTotallyReal K] (w : InfinitePlace K) : mult w = 1 :=
  mult_isReal ⟨w, isReal w⟩

theorem IsTotallyReal.ofRingEquiv [IsTotallyReal F] (f : F ≃+* K) : IsTotallyReal K where
  isReal _ := (isReal_comap_iff f).mp <| IsTotallyReal.isReal _

variable (F K) in
theorem IsTotallyReal.of_algebra [IsTotallyReal K] [Algebra F K] [Algebra.IsAlgebraic F K] :
    IsTotallyReal F where
  isReal w := by
    obtain ⟨W, rfl⟩ : ∃ W : InfinitePlace K, W.comap (algebraMap F K) = w := comap_surjective w
    exact IsReal.comap _ (IsTotallyReal.isReal W)

theorem isTotallyReal_iff_ofRingEquiv (f : F ≃+* K) : IsTotallyReal F ↔ IsTotallyReal K :=
  ⟨fun _ ↦ .ofRingEquiv f, fun _ ↦ .ofRingEquiv f.symm⟩

@[simp]
theorem isTotallyReal_top_iff : IsTotallyReal (⊤ : Subfield K) ↔ IsTotallyReal K :=
  isTotallyReal_iff_ofRingEquiv Subfield.topEquiv

@[deprecated (since := "2025-05-19")] alias IsTotally.of_algebra := IsTotallyReal.of_algebra

instance [IsTotallyReal K] [CharZero K] (F : IntermediateField ℚ K) [Algebra.IsAlgebraic F K] :
    IsTotallyReal F :=
  IsTotallyReal.of_algebra F K

instance [IsTotallyReal K] (F : Subfield K) [Algebra.IsAlgebraic F K] : IsTotallyReal F :=
  IsTotallyReal.of_algebra F K

variable (K)

@[simp]
theorem IsTotallyReal.nrComplexPlaces_eq_zero [NumberField K] [h : IsTotallyReal K] :
    nrComplexPlaces K = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr h

protected theorem IsTotallyReal.finrank [NumberField K] [h : IsTotallyReal K] :
    finrank ℚ K = nrRealPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, nrComplexPlaces_eq_zero_iff.mpr h, mul_zero, add_zero]

instance : IsTotallyReal ℚ where
  isReal v := by
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact Rat.isReal_infinitePlace

instance [IsTotallyReal K] :
    IsTotallyReal (⊤ : Subfield K) := isTotallyReal_top_iff.mpr ‹_›

instance _root_.IntermediateField.isTotallyReal_bot [CharZero K] :
    IsTotallyReal (⊥ : IntermediateField ℚ K) :=
  IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv ℚ K).symm.toRingEquiv

instance _root_.Subfield.isTotallyReal_bot [CharZero K] :
    IsTotallyReal (⊥ : Subfield K) := by
  rw [Subfield.bot_eq_of_charZero]
  exact IsTotallyReal.ofRingEquiv (algebraMap ℚ K).rangeRestrictFieldEquiv

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

variable {K}

theorem mem_maximalRealSubfield_iff (x : K) :
    x ∈ maximalRealSubfield K ↔ ∀ φ : K →+* ℂ, star (φ x) = φ x := .rfl

theorem IsTotallyReal.le_maximalRealSubfield (E : Subfield K) [IsTotallyReal E] :
    E ≤ maximalRealSubfield K := by
  intro x hx φ
  rw [show φ x = (φ.comp E.subtype) ⟨x, hx⟩ by simp, RCLike.star_def, ← conjugate_coe_eq]
  refine RingHom.congr_fun ?_ _
  exact ComplexEmbedding.isReal_iff.mp <| isReal_mk_iff.mp <| isReal _

@[simp]
theorem IsTotallyReal.maximalRealSubfield_eq_top [IsTotallyReal K] :
    maximalRealSubfield K = ⊤ :=
  top_unique <| NumberField.IsTotallyReal.le_maximalRealSubfield _

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

local instance (k : Subfield K) : Algebra.IsAlgebraic k K :=
  Algebra.IsAlgebraic.tower_top k (K := ℚ) (A := K)

instance isTotallyReal_maximalRealSubfield :
    IsTotallyReal (maximalRealSubfield K) where
  isReal w := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [RingHom.star_apply, ← lift_algebraMap_apply K w.embedding]
    exact x.prop _

theorem isTotallyReal_iff_le_maximalRealSubfield {E : Subfield K} :
    IsTotallyReal E ↔ E ≤ maximalRealSubfield K := by
  refine ⟨fun h ↦ h.le_maximalRealSubfield, fun h ↦ ?_⟩
  let _ : Algebra E (maximalRealSubfield K) := RingHom.toAlgebra <| Subfield.inclusion h
  have : IsScalarTower E (maximalRealSubfield K) K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic E (maximalRealSubfield K) :=
      Algebra.IsAlgebraic.tower_bot E (maximalRealSubfield K) K
  exact IsTotallyReal.of_algebra _ (maximalRealSubfield K)

instance isTotallyReal_sup {E F : Subfield K} [hE : IsTotallyReal E] [hF : IsTotallyReal F] :
    IsTotallyReal (E ⊔ F : Subfield K) := by
  rw [isTotallyReal_iff_le_maximalRealSubfield, sup_le_iff,
    ← isTotallyReal_iff_le_maximalRealSubfield, ← isTotallyReal_iff_le_maximalRealSubfield]
  exact ⟨hE, hF⟩

instance isTotallyReal_iSup {ι : Type*} {k : ι → Subfield K} [∀ i, IsTotallyReal (k i)] :
    IsTotallyReal (⨆ i, k i : Subfield K) := by
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    infer_instance
  · rw [isTotallyReal_iff_le_maximalRealSubfield, iSup_le_iff]
    exact fun i ↦ IsTotallyReal.le_maximalRealSubfield (k i)

theorem maximalRealSubfield_eq_top_iff_isTotallyReal :
    maximalRealSubfield K = ⊤ ↔ IsTotallyReal K where
  mp h := by rw [← isTotallyReal_top_iff, isTotallyReal_iff_le_maximalRealSubfield, h]
  mpr _ := IsTotallyReal.maximalRealSubfield_eq_top

end maximalRealSubfield

end TotallyRealField

section TotallyComplexField

/-
## Totally complex number fields
-/

open InfinitePlace

/--
A field `K` is totally complex if all of its infinite places are complex.
-/
@[mk_iff] class IsTotallyComplex (K : Type*) [Field K] where
  isComplex : ∀ v : InfinitePlace K, v.IsComplex

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]

theorem nrRealPlaces_eq_zero_iff [NumberField K] :
    nrRealPlaces K = 0 ↔ IsTotallyComplex K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyComplex_iff]

theorem IsTotallyComplex.complexEmbedding_not_isReal [IsTotallyComplex K] (φ : K →+* ℂ) :
    ¬ ComplexEmbedding.IsReal φ :=
  isReal_mk_iff.not.mp <| not_isReal_iff_isComplex.mpr <| isComplex (InfinitePlace.mk φ)

@[simp]
theorem IsTotallyComplex.mult_eq [IsTotallyComplex K] (w : InfinitePlace K) : mult w = 2 :=
  mult_isComplex ⟨w, isComplex w⟩

variable (K)

@[simp]
theorem IsTotallyComplex.nrRealPlaces_eq_zero [NumberField K] [h : IsTotallyComplex K] :
    nrRealPlaces K = 0 :=
  nrRealPlaces_eq_zero_iff.mpr h

protected theorem IsTotallyComplex.finrank [NumberField K] [h : IsTotallyComplex K] :
    finrank ℚ K = 2 * nrComplexPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, nrRealPlaces_eq_zero_iff.mpr h, zero_add]

end TotallyComplexField

end NumberField
