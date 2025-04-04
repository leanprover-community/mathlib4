/-
Copyright (c) 2025 X. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# CM extension of number fields

A CM-extension of number fields is a totally complex number field that is a quadratic extension of
a totally real number field.

## Main definitions

* `IsCM`: a predicate on two number fields `F` and `K` stating that `K/F` is a CM-extension.

-/

open NumberField InfinitePlace ComplexEmbedding

/--
real and the extension `K/F` is of degree `2`.
-/
class IsCM (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Prop
  extends IsTotallyReal F, IsTotallyComplex K where
  finrank_eq_two' : Module.finrank F K = 2

namespace IsCM

section first_results

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem isTotallyComplex [IsCM F K] :
    IsTotallyComplex K := toIsTotallyComplex F

theorem isTotallyReal [IsCM F K] :
    IsTotallyReal F := toIsTotallyReal K

theorem finrank_eq_two [IsCM F K] :
    Module.finrank F K = 2 := finrank_eq_two'

variable [IsCM F K]

instance : IsGalois F K :=
{ to_isSeparable := Algebra.IsSeparable.of_integral _ _
  to_normal := normal_of_rank_eq_two _ _ (finrank_eq_two  F K) }

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace F) := by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_zero_iff.mpr (isTotallyComplex F K), zero_add,
    nrComplexPlaces_eq_zero_iff.mpr (isTotallyReal F K), add_zero, ← IsTotallyReal.finrank,
    ← Nat.mul_left_cancel_iff zero_lt_two, ← IsTotallyComplex.finrank,
    ← Module.finrank_mul_finrank ℚ F K, finrank_eq_two F K, mul_comm]

theorem units_rank_eq_units_rank :
    Units.rank K = Units.rank F := by
  rw [Units.rank, Units.rank, card_infinitePlace_eq_card_infinitePlace F K]

end first_results

noncomputable section complexConj

variable (F : Type*) {K : Type*} [Field F] [Field K] [NumberField K] [Algebra F K]

open scoped ComplexConjugate

variable {F} in
theorem isConj_ne_one [IsTotallyComplex K] {φ : K →+* ℂ} {σ : K ≃ₐ[F] K} (hφ : IsConj φ σ) :
    σ ≠ 1 := by
  by_contra h
  rw [h, isConj_one_iff, ← isReal_mk_iff] at hφ
  exact not_isComplex_iff_isReal.mpr hφ (IsTotallyComplex.isComplex _)

variable [NumberField F]

/--
All complex embeddings of a Galois extension of a totally complex field over a totally real field
admit a conjugation.
-/
theorem exists_isConj [IsTotallyReal F] [IsTotallyComplex K] [IsGalois F K] (φ : K →+* ℂ) :
    ∃ σ : K ≃ₐ[F] K, IsConj φ σ :=
  exists_isConj_of_not_isUnramified <|
    not_isUnramified_iff.mpr ⟨IsTotallyComplex.isComplex _, IsTotallyReal.isReal _⟩

variable [IsCM F K]

variable {F} in
/--
All the conjugations of a `CM`-extension are the same.
-/
theorem isConj_eq_isConj {φ ψ : K →+* ℂ} {σ τ : K ≃ₐ[F] K}
    (hφ : IsConj φ σ) (hψ : IsConj ψ τ) : σ = τ := by
  have : Fintype.card (K ≃ₐ[F] K) = 2 := (finrank_eq_two F K) ▸ IsGalois.card_aut_eq_finrank F K
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff' 1] at this
  exact ExistsUnique.unique this (isConj_ne_one hφ) (isConj_ne_one hψ)

/--
The complex conjugation of a `CM`-extension.
-/
def complexConj : K ≃ₐ[F] K :=
  (exists_isConj F (Classical.choice (inferInstance : Nonempty _))).choose

/--
The complex conjugation is the conjugation of any complex embedding.
-/
theorem isConj_complexConj (φ : K →+* ℂ) :
    IsConj φ (complexConj F) := by
  obtain ⟨σ, hσ⟩ := exists_isConj F φ
  have := (exists_isConj F (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))).choose_spec
  rwa [isConj_eq_isConj hσ this] at hσ

variable (K) in
theorem complexConj_ne_one :
    complexConj F ≠ (1 : K ≃ₐ[F] K) :=
  isConj_ne_one (exists_isConj F (Classical.choice (inferInstance : Nonempty _))).choose_spec

@[simp]
theorem complexEmbedding_complexConj (φ : K →+* ℂ) (x : K) :
    φ (complexConj F x) = conj (φ x) := by
  rw [IsConj.eq (isConj_complexConj F φ), RCLike.star_def]

@[simp]
theorem complexConj_apply_apply (x : K) :
    complexConj F (complexConj F x) = x := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  exact isConj_apply_apply (isConj_complexConj F φ) x

variable (K) in
/--
The complex conjugation is an automorphism of degree `2`.
-/
theorem orderOf_complexConj :
    orderOf (complexConj F : K ≃ₐ[F] K) = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by ext; simp, complexConj_ne_one F K⟩

variable (K) in
/--
The complex conjugation generates the Galois group of `K/F`.
-/
theorem zpowers_complexConj_eq_top :
    Subgroup.zpowers (complexConj F : K ≃ₐ[F] K) = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_zpowers, orderOf_complexConj, Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
    finrank_eq_two]

end complexConj

end IsCM
