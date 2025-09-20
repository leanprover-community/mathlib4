/-
Copyright (c) 2025 X. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# CM-extension of number fields

A CM-extension `K/F` of number fields is an extension where `K` is totally complex, `F` is
totally real and `K` is a quadratic extension of `F`. In this situation, the totally real
subfield `F` is (isomorphic to) the maximal real subfield `K⁺` of `K`.

## Main definitions

* `NumberField.IsCMField`: A predicate that says that if a number field is CM, then it is a totally
  complex quadratic extension of its totally real subfield

* `NumberField.CMExtension.equivMaximalRealSubfield`: Any field `F` such that `K/F` is a
  CM-extension is isomorphic to the maximal real subfield `K⁺` of `K`.

* `NumberField.IsCM.ofIsCMExtension`: Assume that there exists `F` such that `K/F` is a
  CM-extension. Then `K` is CM.

* `NumberField.IsCMField.of_isMulCommutative`: A totally complex abelian extension of `ℚ` is CM.

## Implementation note

Most results are proved for the case of a CM field, that is `K` is totally complex quadratic
extension of its totally real. These results live in the `NumberField.IsCMField` namespace. Some
results deal with the general case `K/F`, where `K` is totally complex, `F` is totally real and
`K` is a quadratic extension of `F`, and live in the `NumberField.CMExtension` namespace. Note that
results for the general case can be deduced for the CM case by using the isomorphism
`equivMaximalRealSubfield` between `F` and `K⁺` mentioned above.

-/

open NumberField ComplexEmbedding InfinitePlace Algebra

open scoped ComplexConjugate

namespace NumberField

section maximalRealSubfield

/--
A number field `K` is `CM` if `K` is a totally complex quadratic extension of its maximal
real subfield `K⁺`.
-/
class IsCMField (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] : Prop where
  -- TODO rename isQuadraticExtension
  is_quadratic : IsQuadraticExtension (maximalRealSubfield K) K
-- attribute [instance] IsCMField.isQuadraticExtension

namespace IsCMField

open ComplexEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

instance isQuadraticExtension : IsQuadraticExtension K⁺ K :=
  IsCMField.is_quadratic

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace K⁺) = Fintype.card (InfinitePlace K) := by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero K, IsTotallyReal.nrComplexPlaces_eq_zero, zero_add,
    add_zero, ← IsTotallyReal.finrank, ← Nat.mul_left_cancel_iff zero_lt_two,
    ← IsTotallyComplex.finrank, ← Module.finrank_mul_finrank ℚ K⁺ K, mul_comm,
    IsQuadraticExtension.finrank_eq_two _ K]

theorem units_rank_eq_units_rank :
    Units.rank K⁺ = Units.rank K := by
  rw [Units.rank, Units.rank, card_infinitePlace_eq_card_infinitePlace K]

theorem exists_isConj (φ : K →+* ℂ) :
    ∃ σ : K ≃ₐ[K⁺] K, IsConj φ σ :=
  exists_isConj_of_isRamified <|
    isRamified_iff.mpr ⟨IsTotallyComplex.isComplex _, IsTotallyReal.isReal _⟩

/--
All the conjugations of a CM-field over its maximal real subfield are the same.
-/
theorem isConj_eq_isConj {φ ψ : K →+* ℂ} {σ τ : K ≃ₐ[K⁺] K}
    (hφ : IsConj φ σ) (hψ : IsConj ψ τ) : σ = τ := by
  have : Nat.card (K ≃ₐ[K⁺] K) = 2 :=
    (IsQuadraticExtension.finrank_eq_two K⁺ K) ▸ IsGalois.card_aut_eq_finrank K⁺ K
  rw [Nat.card_eq_two_iff' 1] at this
  exact ExistsUnique.unique this
    ((isConj_ne_one_iff hφ).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ)
    ((isConj_ne_one_iff hψ).mpr <| IsTotallyComplex.complexEmbedding_not_isReal ψ)

/--
The complex conjugation of the CM-field `K`.
-/
noncomputable def complexConj : K ≃ₐ[K⁺] K :=
  (exists_isConj K (Classical.choice (inferInstance : Nonempty _))).choose

/--
The complex conjugation is the conjugation of any complex embedding of a CM-field.
-/
theorem isConj_complexConj (φ : K →+* ℂ) : IsConj φ (complexConj K) := by
  obtain ⟨σ, hσ⟩ := exists_isConj _ φ
  have := (exists_isConj K (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))).choose_spec
  rwa [isConj_eq_isConj K hσ this] at hσ

@[simp]
theorem complexEmbedding_complexConj (φ : K →+* ℂ) (x : K) :
    φ (complexConj K x) = conj (φ x) := by
  rw [IsConj.eq (isConj_complexConj K φ), RCLike.star_def]

@[simp]
theorem complexConj_apply_apply (x : K) :
    complexConj K (complexConj K x) = x := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  exact isConj_apply_apply (isConj_complexConj K φ) x

theorem complexConj_ne_one :
    complexConj K ≠ (1 : K ≃ₐ[K⁺] K) :=
  (isConj_ne_one_iff
    (exists_isConj K (Classical.choice (inferInstance : Nonempty _))).choose_spec).mpr <|
      IsTotallyComplex.complexEmbedding_not_isReal _

@[simp]
theorem complexConj_apply_eq_self (x : K⁺) : complexConj K x = x := AlgEquiv.commutes _ x

/--
The complex conjugation is an automorphism of degree `2`.
-/
theorem orderOf_complexConj :
    orderOf (complexConj K) = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by ext; simp, complexConj_ne_one K⟩

/--
The complex conjugation generates the Galois group of `K/K⁺`.
-/
theorem zpowers_complexConj_eq_top :
    Subgroup.zpowers (complexConj K) = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_zpowers, orderOf_complexConj, IsGalois.card_aut_eq_finrank,
    IsQuadraticExtension.finrank_eq_two]

/--
An element of `K` is fixed by the complex conjugation iff it lies in `K⁺`.
-/
@[simp]
theorem complexConj_eq_self_iff (x : K) :
    complexConj K x = x ↔ x ∈ K⁺ := by
  convert (IntermediateField.mem_fixedField_iff (⊤ : Subgroup (K ≃ₐ[K⁺] K)) x).symm using 1
  · rw [← zpowers_complexConj_eq_top, Subgroup.forall_mem_zpowers]
    exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := (complexConj K))).symm
  · rw [IsGalois.fixedField_top, IntermediateField.mem_bot]
    aesop

protected theorem RingOfIntegers.complexConj_eq_self_iff (x : 𝓞 K) :
    complexConj K x = x ↔ ∃ y : 𝓞 K⁺, algebraMap (𝓞 K⁺) K y = x := by
  rw [complexConj_eq_self_iff]
  refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · have : IsIntegral ℤ (⟨x, h⟩ : K⁺) :=
      (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K⁺ K)).mp x.isIntegral_coe
    refine ⟨⟨⟨x, h⟩, this⟩, ?_⟩
    rw [IsScalarTower.algebraMap_apply (𝓞 K⁺) K⁺, RingOfIntegers.map_mk]
    -- REVIEW
    rfl
  · rw [← hy, IsScalarTower.algebraMap_apply (𝓞 K⁺) K⁺]
    exact SetLike.coe_mem _

protected theorem Units.complexConj_eq_self_iff (u : (𝓞 K)ˣ) :
    complexConj K u = u ↔ ∃ v : (𝓞 K⁺)ˣ, algebraMap (𝓞 K⁺) K v = u := by
  rw [RingOfIntegers.complexConj_eq_self_iff, Units.coe_coe]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨v, hv⟩ ↦ ⟨v, by rw [hv]⟩⟩
  have : IsUnit y := by
    apply IsUnit.of_map (algebraMap (𝓞 K⁺) (𝓞 K))
    -- REVIEW
    rw [show algebraMap (𝓞 K⁺) (𝓞 K) y = u by exact RingOfIntegers.ext hy]
    exact u.isUnit
  exact ⟨this.unit, by simp [hy]⟩

noncomputable instance starRing : StarRing K where
  star := complexConj K
  star_involutive _ := complexConj_apply_apply _ _
  star_mul _ _ := by rw [map_mul, mul_comm]
  star_add _ _ := by rw [map_add]

section units

open Units

/--
The subgroup of `(𝓞 K)ˣ` generated by the units of `K⁺`. These units are exactly the units fixed
by the complex conjugation, see `IsCMField.unitsComplexConj_eq_self_iff`.
-/
def realUnits : Subgroup (𝓞 K)ˣ := (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom).range

omit [IsTotallyComplex K] [IsCMField K] in
theorem mem_realUnits_iff (u : (𝓞 K)ˣ) :
    u ∈ realUnits K ↔ ∃ v : (𝓞 K⁺)ˣ, algebraMap (𝓞 K⁺) (𝓞 K) v = u := by
  simp [realUnits, MonoidHom.mem_range, RingHom.toMonoidHom_eq_coe, Units.ext_iff]

theorem unitsComplexConj_eq_self_iff (u : (𝓞 K)ˣ) :
    complexConj K u = u ↔ u ∈ realUnits K := by
  simp_rw [Units.complexConj_eq_self_iff, mem_realUnits_iff, RingOfIntegers.ext_iff,
    IsScalarTower.algebraMap_apply (𝓞 K⁺) (𝓞 K) K]

/--
The image of a root of unity by the complex conjugation is its inverse.
This is the version of `Complex.conj_rootsOfUnity` for CM-fields.
-/
@[simp]
theorem unitsComplexConj_torsion (ζ : torsion K) :
    complexConj K (ζ.val : K) = (ζ.val : K)⁻¹ := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ.injective
  rw [complexEmbedding_complexConj, ← Units.complexEmbedding_apply,
    Complex.conj_rootsOfUnity (n := torsionOrder K), Units.val_inv_eq_inv_val,
    Units.complexEmbedding_apply, map_inv₀]
  exact map_complexEmbedding_torsion K φ ▸ Subgroup.apply_coe_mem_map _ _ _

end units

end IsCMField

end maximalRealSubfield

namespace CMExtension

variable (F K : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
  [IsTotallyComplex K] [Algebra F K] [IsQuadraticExtension F K]

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
    exact eq_maximalRealSubfield K (algebraMap F K).fieldRange))

@[simp]
theorem equivMaximalRealSubfield_apply (x : F) :
    equivMaximalRealSubfield F K x = algebraMap F K x := rfl

@[simp]
theorem algebraMap_equivMaximalRealSubfield_symm_apply (x : maximalRealSubfield K) :
    algebraMap F K ((CMExtension.equivMaximalRealSubfield F K).symm x) =
      algebraMap (maximalRealSubfield K) K x := by
  simpa using (equivMaximalRealSubfield_apply F K ((equivMaximalRealSubfield F K).symm x)).symm

include F in
/--
If `K/F` is a CM-extension then `K` is a CM-field.
-/
theorem _root_.NumberField.IsCMField.ofCMExtension :
    IsCMField K where
  is_quadratic := ⟨(IsQuadraticExtension.finrank_eq_two F K) ▸ finrank_eq_of_equiv_equiv
      (CMExtension.equivMaximalRealSubfield F K).symm (RingEquiv.refl K) (by ext; simp)⟩

open IntermediateField in
/--
A totally complex field that has a unique complex conjugation is CM.
-/
theorem _root_.NumberField.IsCMField.of_forall_isConj {σ : K ≃ₐ[ℚ] K}
    (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
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
  exact IsCMField.ofCMExtension (fixedField (Subgroup.zpowers σ)) K

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
    obtain ⟨ν, rfl⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ (by ext; simp)
    rw [show σ = ν.symm⁻¹ * σ * ν.symm by simp]
    exact hσ₁.comp _
  exact IsCMField.of_forall_isConj K hσ₂

end CMExtension

end NumberField
