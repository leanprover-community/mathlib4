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

* `NumberField.CMExtension.complexConj`: the complex conjugation of a CM-extension.

* `NumberField.CMExtension.isConj_complexConj`: the complex conjugation is the conjugation
  of any complex embedding of a `CM`-extension.

* `NumberField.IsCMField`: A predicate that says that if a number field is CM, then it is a totally
  complex quadratic extension of its totally real subfield

## Implementation note

Most result are proved under the general hypothesis: `K/F` quadratic extension of number fields
with `F` totally real and `K` totally complex and then, if relevant, we deduce the special case
`F = maximalRealSubfield K`. Results of the first kind live in the `NumberField.CMExtension`
namespace whereas results of the second kind live in the `NumberField.IsCMField` namespace.

-/

open NumberField ComplexEmbedding InfinitePlace Algebra

open scoped ComplexConjugate

namespace NumberField

namespace CMExtension

variable (F K : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
  [IsTotallyComplex K] [Algebra F K] [IsQuadraticExtension F K]

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace K) := by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero K, IsTotallyReal.nrComplexPlaces_eq_zero F, zero_add,
    add_zero, ← IsTotallyReal.finrank, ← Nat.mul_left_cancel_iff zero_lt_two,
    ← IsTotallyComplex.finrank, ← Module.finrank_mul_finrank ℚ F K, mul_comm,
    IsQuadraticExtension.finrank_eq_two F K]

theorem units_rank_eq_units_rank :
    Units.rank F = Units.rank K := by
  rw [Units.rank, Units.rank, card_infinitePlace_eq_card_infinitePlace F K]

variable {K}

theorem exists_isConj (φ : K →+* ℂ) :
    ∃ σ : K ≃ₐ[F] K, IsConj φ σ :=
  exists_isConj_of_isRamified <|
    isRamified_iff.mpr ⟨IsTotallyComplex.isComplex _, IsTotallyReal.isReal _⟩

omit [IsTotallyReal F] in
/--
All the conjugations of a `CM`-extension are the same.
-/
theorem isConj_eq_isConj {φ ψ : K →+* ℂ} {σ τ : K ≃ₐ[F] K} (hφ : IsConj φ σ) (hψ : IsConj ψ τ) :
    σ = τ := by
  have : Fintype.card (K ≃ₐ[F] K) = 2 :=
    (IsQuadraticExtension.finrank_eq_two F K) ▸ IsGalois.card_aut_eq_finrank F K
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff' 1] at this
  exact ExistsUnique.unique this
    ((isConj_ne_one_iff hφ).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ)
    ((isConj_ne_one_iff hψ).mpr <| IsTotallyComplex.complexEmbedding_not_isReal ψ)

variable (K) in
/--
The complex conjugation of a `CM`-extension.
-/
noncomputable def complexConj : K ≃ₐ[F] K :=
  (exists_isConj F (Classical.choice (inferInstance : Nonempty _))).choose

/--
The complex conjugation is the conjugation of any complex embedding of a `CM`-extension.
-/
theorem isConj_complexConj (φ : K →+* ℂ) :
    IsConj φ (complexConj F K) := by
  obtain ⟨σ, hσ⟩ := exists_isConj F φ
  have := (exists_isConj F (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))).choose_spec
  rwa [isConj_eq_isConj F hσ this] at hσ

variable (K) in
theorem complexConj_ne_one :
    complexConj F K ≠ (1 : K ≃ₐ[F] K) :=
  (isConj_ne_one_iff
    (exists_isConj F (Classical.choice (inferInstance : Nonempty _))).choose_spec).mpr <|
      IsTotallyComplex.complexEmbedding_not_isReal _

@[simp]
theorem complexEmbedding_complexConj (φ : K →+* ℂ) (x : K) :
    φ (complexConj F K x) = conj (φ x) := by
  rw [IsConj.eq (isConj_complexConj F φ), RCLike.star_def]

@[simp]
theorem complexConj_apply_apply (x : K) :
    complexConj F K (complexConj F K x) = x := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  exact isConj_apply_apply (isConj_complexConj F φ) x

variable (K) in
/--
The complex conjugation is an automorphism of degree `2`.
-/
theorem orderOf_complexConj :
    orderOf (complexConj F K : K ≃ₐ[F] K) = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by ext; simp, complexConj_ne_one F K⟩

variable (K) in
/--
The complex conjugation generates the Galois group of `K/F`.
-/
theorem zpowers_complexConj_eq_top :
    Subgroup.zpowers (complexConj F K) = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_zpowers, orderOf_complexConj, Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
    IsQuadraticExtension.finrank_eq_two]

end CMExtension

section maximalRealSubfield

/--
A number field `K` is `CM` if `K` is a totally complex quadratic extension of its maximal
real subfield.
-/
class IsCMField (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] : Prop where
  is_quadratic : IsQuadraticExtension (maximalRealSubfield K) K

namespace IsCMField

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] [IsCMField K]

instance isQuadraticExtension : IsQuadraticExtension (maximalRealSubfield K) K :=
  IsCMField.is_quadratic

noncomputable instance starRing : StarRing K where
  star := CMExtension.complexConj (maximalRealSubfield K) K
  star_involutive := fun _ ↦ CMExtension.complexConj_apply_apply _ _
  star_mul := fun _ _ ↦ by rw [map_mul, mul_comm]
  star_add := fun _ _ ↦ by rw [map_add]

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace (maximalRealSubfield K)) = Fintype.card (InfinitePlace K) :=
  CMExtension.card_infinitePlace_eq_card_infinitePlace _ _

theorem units_rank_eq_units_rank :
    Units.rank (maximalRealSubfield K) = Units.rank K :=
  CMExtension.units_rank_eq_units_rank _ _

end IsCMField

end maximalRealSubfield

end NumberField
