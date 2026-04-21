/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!

# Fractional ideals of number fields

Prove some results on the fractional ideals of number fields.

## Main definitions and results

* `NumberField.basisOfFractionalIdeal`: A `ℚ`-basis of `K` that spans `I` over `ℤ` where `I` is
  a fractional ideal of a number field `K`.
* `NumberField.det_basisOfFractionalIdeal_eq_absNorm`: for `I` a fractional ideal of a number
  field `K`, the absolute value of the determinant of the base change from `integralBasis` to
  `basisOfFractionalIdeal I` is equal to the norm of `I`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

open scoped nonZeroDivisors

section Basis

open Module

instance (I : FractionalIdeal (𝓞 K)⁰ K) : Module.Free ℤ I := by
  refine Free.of_equiv (LinearEquiv.restrictScalars ℤ (I.equivNum ?_)).symm
  exact nonZeroDivisors.coe_ne_zero I.den

instance (I : FractionalIdeal (𝓞 K)⁰ K) : Module.Finite ℤ I := by
  refine Module.Finite.of_surjective
    (LinearEquiv.restrictScalars ℤ (I.equivNum ?_)).symm.toLinearMap (LinearEquiv.surjective _)
  exact nonZeroDivisors.coe_ne_zero I.den

instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsLocalizedModule ℤ⁰ ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars ℤ) where
  map_units x := by
    rw [← (Algebra.lmul _ _).commutes, Algebra.lmul_isUnit_iff, isUnit_iff_ne_zero, eq_intCast,
      Int.cast_ne_zero]
    exact nonZeroDivisors.coe_ne_zero x
  surj x := by
    obtain ⟨⟨a, _, d, hd, rfl⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) x
    refine ⟨⟨⟨Ideal.absNorm I.1.num * (algebraMap _ K a), I.1.num_le ?_⟩, d * Ideal.absNorm I.1.num,
      ?_⟩, ?_⟩
    · refine (IsLocalization.mem_coeSubmodule _ _).mpr ⟨Ideal.absNorm I.1.num * a, ?_, ?_⟩
      · exact Ideal.mul_mem_right _ _ I.1.num.absNorm_mem
      · rw [map_mul, map_natCast]
    · refine Submonoid.mul_mem _ hd (mem_nonZeroDivisors_of_ne_zero ?_)
      rw [Nat.cast_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff]
      exact FractionalIdeal.num_eq_zero_iff.not.mpr <| Units.ne_zero I
    · simp_rw [LinearMap.coe_restrictScalars, Submodule.coe_subtype] at h ⊢
      rw [← h]
      simp only [Submonoid.mk_smul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, algebraMap_int_eq,
        eq_intCast, map_intCast]
      ring
  exists_of_eq h :=
    ⟨1, by rwa [one_smul, one_smul, ← (Submodule.injective_subtype I.1.coeToSubmodule).eq_iff]⟩

/-- A `ℤ`-basis of a fractional ideal. -/
noncomputable def fractionalIdealBasis (I : FractionalIdeal (𝓞 K)⁰ K) :
    Basis (Free.ChooseBasisIndex ℤ I) ℤ I := Free.chooseBasis ℤ I

/-- A `ℚ`-basis of `K` that spans `I` over `ℤ`, see `mem_span_basisOfFractionalIdeal` below. -/
noncomputable def basisOfFractionalIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ I) ℚ K :=
  (fractionalIdealBasis K I.1).ofIsLocalizedModule ℚ ℤ⁰
    ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars ℤ)

theorem basisOfFractionalIdeal_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    basisOfFractionalIdeal K I i = fractionalIdealBasis K I.1 i :=
  (fractionalIdealBasis K I.1).ofIsLocalizedModule_apply ℚ ℤ⁰ _ i

theorem mem_span_basisOfFractionalIdeal {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K} :
    x ∈ Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) ↔ x ∈ (I : Set K) := by
  rw [basisOfFractionalIdeal, (fractionalIdealBasis K I.1).ofIsLocalizedModule_span ℚ ℤ⁰ _]
  simp

open Module in
theorem fractionalIdeal_rank (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    finrank ℤ I = finrank ℤ (𝓞 K) := by
  rw [finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
    finrank_eq_card_basis (basisOfFractionalIdeal K I)]

end Basis

section Norm

open Module

/-- The absolute value of the determinant of the base change from `integralBasis` to
`basisOfFractionalIdeal I` is equal to the norm of `I`. -/
theorem det_basisOfFractionalIdeal_eq_absNorm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (e : (Free.ChooseBasisIndex ℤ (𝓞 K)) ≃ (Free.ChooseBasisIndex ℤ I)) :
    |(integralBasis K).det ((basisOfFractionalIdeal K I).reindex e.symm)| =
      FractionalIdeal.absNorm I.1 := by
  rw [← FractionalIdeal.abs_det_basis_change (RingOfIntegers.basis K) I.1
    ((fractionalIdealBasis K I.1).reindex e.symm)]
  congr
  ext
  simpa using basisOfFractionalIdeal_apply K I _

end Norm

end NumberField
