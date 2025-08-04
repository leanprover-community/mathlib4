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

* `NumberField.CMExtension.equivMaximalRealSubfield`: Any field `F` such that `K/F` is a
  CM-extension is isomorphic to the maximal real subfield of `K`.

* `NumberField.IsCM.ofIsCMExtension`: Assume that there exists `F` such that `K/F` is a
  CM-extension. Then `K` is CM.

* `NumberField.IsCMField.of_isMulCommutative`: A totally complex abelian extension of `ℚ` is CM.

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
  have : Nat.card (K ≃ₐ[F] K) = 2 :=
    (IsQuadraticExtension.finrank_eq_two F K) ▸ IsGalois.card_aut_eq_finrank F K
  rw [Nat.card_eq_two_iff' 1] at this
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
  rw [Nat.card_zpowers, orderOf_complexConj, IsGalois.card_aut_eq_finrank,
    IsQuadraticExtension.finrank_eq_two]

theorem eq_maximalRealSubfield (E : Subfield K) [IsTotallyReal E] [IsQuadraticExtension E K] :
    E = maximalRealSubfield K := by
  refine le_antisymm (IsTotallyReal.le_maximalRealSubfield E) ?_
  by_contra! h
  have h' : E ⊔ (maximalRealSubfield K) = ⊤ := by
    let L : IntermediateField E K := (E ⊔ (maximalRealSubfield K)).toIntermediateField
      (fun x ↦ (le_sup_left (a := E)) x.prop)
    have := ((IntermediateField.isSimpleOrder_of_finrank_prime E K
      (IsQuadraticExtension.finrank_eq_two E K ▸ Nat.prime_two)).eq_bot_or_eq_top L).resolve_left ?_
    · simpa [L] using congr_arg IntermediateField.toSubfield this
    · contrapose! h
      rw [← SetLike.coe_set_eq, Subfield.coe_toIntermediateField] at h
      rw [← sup_eq_left, ← SetLike.coe_set_eq, h, IntermediateField.coe_bot]
      aesop
  have : IsTotallyReal K := (h' ▸ isTotallyReal_sup).ofRingEquiv Subring.topEquiv
  obtain w : InfinitePlace K := Classical.choice (inferInstance : Nonempty _)
  exact (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) (IsTotallyReal.isReal w)

variable (K)

/--
Any field `F` such that `K/F` is a CM-extension is isomorphic to the maximal real subfield of `K`.
-/
noncomputable def equivMaximalRealSubfield :
    F ≃+* maximalRealSubfield K :=
  (algebraMap F K).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (by
    have := IsTotallyReal.ofRingEquiv (algebraMap F K).rangeRestrictFieldEquiv
    have : IsQuadraticExtension (algebraMap F K).fieldRange K :=
    { finrank_eq_two' :=
        (IsQuadraticExtension.finrank_eq_two F K) ▸ Algebra.finrank_eq_of_equiv_equiv
          (algebraMap F K).rangeRestrictFieldEquiv.symm (RingEquiv.refl K) (by ext; simp; rfl) }
    exact eq_maximalRealSubfield (algebraMap F K).fieldRange))

@[simp]
theorem equivMaximalRealSubfield_apply (x : F) :
    equivMaximalRealSubfield F K x = algebraMap F K x := rfl

@[simp]
theorem algebraMap_equivMaximalRealSubfield_symm_apply (x : maximalRealSubfield K) :
    algebraMap F K ((CMExtension.equivMaximalRealSubfield F K).symm x) =
      algebraMap (maximalRealSubfield K) K x := by
  simpa using (equivMaximalRealSubfield_apply F K ((equivMaximalRealSubfield F K).symm x)).symm

end CMExtension

section maximalRealSubfield

/--
A number field `K` is `CM` if `K` is a totally complex quadratic extension of its maximal
real subfield.
-/
class IsCMField (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] : Prop where
  is_quadratic : IsQuadraticExtension (maximalRealSubfield K) K

namespace IsCMField

variable (F K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem ofCMExtension [Field F] [NumberField F] [IsTotallyReal F] [Algebra F K]
    [IsQuadraticExtension F K] :
    IsCMField K where
  is_quadratic := ⟨(IsQuadraticExtension.finrank_eq_two F K) ▸ finrank_eq_of_equiv_equiv
      (CMExtension.equivMaximalRealSubfield F K).symm (RingEquiv.refl K) (by ext; simp)⟩

open IntermediateField in
/--
A totally complex field that has a unique complex conjugation is CM.
-/
theorem of_forall_isConj {σ : K ≃ₐ[ℚ] K} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) :
    IsCMField K := by
  have : IsTotallyReal (fixedField (Subgroup.zpowers σ)) := ⟨fun w ↦ by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
    let τ := subgroupEquivAlgEquiv _ ⟨σ, Subgroup.mem_zpowers σ⟩
    have hτ : IsConj W.embedding τ := hσ _
    simpa [← isReal_mk_iff, ← InfinitePlace.comap_mk, mk_embedding] using hτ.isReal_comp⟩
  have : IsQuadraticExtension (fixedField (Subgroup.zpowers σ)) K := ⟨by
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have hσ' : σ ≠ 1 :=
      (isConj_ne_one_iff (hσ φ)).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_isConj_two_of_ne_one (hσ φ) hσ']⟩
  exact ofCMExtension (fixedField (Subgroup.zpowers σ)) K

/--
A totally complex abelian extension of `ℚ` is CM.
-/
instance of_isMulCommutative [IsGalois ℚ K] [IsMulCommutative (K ≃ₐ[ℚ] K)] :
    IsCMField K := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  obtain ⟨σ, hσ₁⟩ : ∃ σ : K ≃ₐ[ℚ] K, ComplexEmbedding.IsConj φ σ :=
    exists_isConj_of_isRamified <|
      isRamified_iff.mpr ⟨IsTotallyComplex.isComplex _, IsTotallyReal.isReal _⟩
  have hσ₂ : ∀ (φ : K →+* ℂ), ComplexEmbedding.IsConj φ σ := by
    intro ψ
    obtain ⟨ν, rfl⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ (by ext; simp)
    rw [show σ = ν.symm⁻¹ * σ * ν.symm by simp]
    exact hσ₁.comp _
  exact of_forall_isConj K hσ₂

variable [IsCMField K]

instance isQuadraticExtension : IsQuadraticExtension (maximalRealSubfield K) K :=
  IsCMField.is_quadratic

noncomputable instance starRing : StarRing K where
  star := CMExtension.complexConj (maximalRealSubfield K) K
  star_involutive _ := CMExtension.complexConj_apply_apply _ _
  star_mul _ _ := by rw [map_mul, mul_comm]
  star_add _ _ := by rw [map_add]

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace (maximalRealSubfield K)) = Fintype.card (InfinitePlace K) :=
  CMExtension.card_infinitePlace_eq_card_infinitePlace _ _

theorem units_rank_eq_units_rank :
    Units.rank (maximalRealSubfield K) = Units.rank K :=
  CMExtension.units_rank_eq_units_rank _ _

end IsCMField

end maximalRealSubfield

end NumberField
