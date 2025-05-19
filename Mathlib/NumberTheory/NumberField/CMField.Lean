/-
Copyright (c) 2025 X. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# CM-extension of number fields

A CM-extension `K/F` of number fields is an extension where `K` is totally complex, `F` is
totally real and `K` is a quadratic extension of `F`. In this situation, the totally real
subfield `F` is (isomorphic to) the maximal real subfield of `K`.

## Main definitions

## Implementation note

Most result are proved under the general hypothesis: `K/F` quadratic extension of number fields
with `F` totally real and `K` totally complex and then, if relevant, we deduce the special case
`F = maximalRealSubfield K`.

-/

open NumberField InfinitePlace ComplexEmbedding Algebra

namespace NumberField

namespace CMExtension

variable (F K : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
  [IsTotallyComplex K] [Algebra F K] [IsQuadraticExtension F K]

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace F) := by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero K, IsTotallyReal.nrComplexPlaces_eq_zero F, zero_add,
    add_zero, ← IsTotallyReal.finrank, ← Nat.mul_left_cancel_iff zero_lt_two,
    ← IsTotallyComplex.finrank, ← Module.finrank_mul_finrank ℚ F K, mul_comm,
    IsQuadraticExtension.finrank_eq_two F K]

theorem units_rank_eq_units_rank :
    Units.rank K = Units.rank F := by
  rw [Units.rank, Units.rank, card_infinitePlace_eq_card_infinitePlace F K]

theorem exists_isConj (φ : K →+* ℂ) :
    ∃ σ : K ≃ₐ[F] K, IsConj φ σ :=
  exists_isConj_of_not_isUnramified <|
    not_isUnramified_iff.mpr ⟨IsTotallyComplex.isComplex _, IsTotallyReal.isReal _⟩

omit [IsTotallyReal F] in
/--
All the conjugations of a `CM`-extension are the same.
-/
theorem isConj_eq_isConj {φ ψ : K →+* ℂ} {σ τ : K ≃ₐ[F] K} (hφ : IsConj φ σ) (hψ : IsConj ψ τ) :
    σ = τ := by
  have : Fintype.card (K ≃ₐ[F] K) = 2 :=
    (IsQuadraticExtension.finrank_eq_two F K) ▸ IsGalois.card_aut_eq_finrank F K
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff' 1] at this
  exact ExistsUnique.unique this (IsTotallyComplex.isConj_ne_one hφ)
    (IsTotallyComplex.isConj_ne_one hψ)

/--
The complex conjugation of a `CM`-extension.
-/
noncomputable def complexConj : K ≃ₐ[F] K :=
  (exists_isConj F K (Classical.choice (inferInstance : Nonempty _))).choose

end CMExtension

end NumberField
