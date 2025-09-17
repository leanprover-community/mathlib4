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

variable (K)
/--
The complex conjugation of a `CM`-extension.
-/
noncomputable def complexConj : K ≃ₐ[F] K :=
  (exists_isConj F (Classical.choice (inferInstance : Nonempty _))).choose

/--
A variant of the complex conjugation defined as an `AlgEquiv` on the ring of integers.
-/
noncomputable abbrev ringOfIntegersComplexConj : (𝓞 K) ≃ₐ[𝓞 F] (𝓞 K) :=
  RingOfIntegers.mapAlgEquiv (complexConj F K)

variable {K}

@[simp]
theorem coe_ringOfIntegersComplexConj (x : 𝓞 K) :
    (ringOfIntegersComplexConj F K x : K) = complexConj F K (x : K) := rfl

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

@[simp]
theorem ringOfIntegersComplexConj_apply_apply (x : 𝓞 K) :
    ringOfIntegersComplexConj F K (ringOfIntegersComplexConj F K x) = x := by
  simp [RingOfIntegers.ext_iff]

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
    Subgroup.zpowers (complexConj F K : K ≃ₐ[F] K) = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_zpowers, orderOf_complexConj, IsGalois.card_aut_eq_finrank,
    IsQuadraticExtension.finrank_eq_two]

/--
An element of `K` is fixed by the complex conjugation iff it comes from `F`.
-/
theorem complexConj_eq_self_iff (x : K) :
    complexConj F K x = x ↔ x ∈ (algebraMap F K).range := by
  convert (IntermediateField.mem_fixedField_iff (⊤ : Subgroup (K ≃ₐ[F] K)) x).symm using 1
  · rw [← zpowers_complexConj_eq_top, Subgroup.forall_mem_zpowers]
    exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy
      (g := (complexConj F K : K ≃ₐ[F] K)) (a := x)).symm
  · rw [IsGalois.fixedField_top, IntermediateField.mem_bot, RingHom.mem_range, Set.mem_range]

/--
An element of `𝓞 K` is fixed by the complex conjugation iff it comes from `𝓞 F`.
-/
theorem ringOfIntegersComplexConj_eq_self_iff (x : 𝓞 K) :
    ringOfIntegersComplexConj F K x = x ↔ x ∈ (algebraMap (𝓞 F) (𝓞 K)).range := by
  rw [← RingOfIntegers.eq_iff, coe_ringOfIntegersComplexConj, complexConj_eq_self_iff,
    RingOfIntegers.coe_eq_algebraMap, RingHom.mem_range, RingHom.mem_range]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨⟨a, ?_⟩, RingOfIntegers.eq_iff.mp ha⟩, ?_⟩
  · exact (isIntegral_algebraMap_iff
      (FaithfulSMul.algebraMap_injective F K)).mp (ha ▸ RingOfIntegers.isIntegral_coe x)
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
noncomputable section units

open NumberField.Units

/--
The complex conjugation as a `RingEquiv` on the group of units.
-/
abbrev unitsComplexConj : (𝓞 K)ˣ ≃* (𝓞 K)ˣ :=
  Units.mapEquiv (ringOfIntegersComplexConj F K).toMulEquiv

@[simp]
theorem coe_unitsComplexConj (x : (𝓞 K)ˣ) :
    (unitsComplexConj F x : 𝓞 K) = ringOfIntegersComplexConj F K (x : 𝓞 K) := rfl

theorem unitsComplexEmbedding_complexConj (φ : K →+* ℂ) (u : (𝓞 K)ˣ) :
    Units.complexEmbedding φ (unitsComplexConj F u) = (Units.map (starRingEnd ℂ))
      (Units.complexEmbedding φ u) := by
  simp [Units.ext_iff]

/--
The image of a root of unity by the complex conjugation is its inverse.
This is the version of `Complex.conj_rootsOfUnity` for CM-fields.
-/
@[simp]
theorem unitsComplexConj_torsion (ζ : torsion K) :
    unitsComplexConj F (ζ : (𝓞 K)ˣ) = ζ⁻¹ := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  rw [← (Units.complexEmbedding_injective φ).eq_iff, unitsComplexEmbedding_complexConj,
    Units.ext_iff, Units.coe_map, MonoidHom.coe_coe, Subgroup.coe_inv, MonoidHom.map_inv,
    Complex.conj_rootsOfUnity (n := torsionOrder K)]
  exact map_complexEmbedding_torsion K  _ ▸ Subgroup.apply_coe_mem_map _ (torsion K) ζ

variable (K) in
/--
The subgroup of `(𝓞 K)ˣ` generated by the units coming from `F`. These units are exactly the units
fixed by the complex conjugation, see `unitsComplexConj_eq_self_iff`.
-/
abbrev realUnits : Subgroup (𝓞 K)ˣ := (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom).range

theorem unitsComplexConj_eq_self_iff (u : (𝓞 K)ˣ) :
    unitsComplexConj F u = u ↔ u ∈ realUnits F K := by
  rw [← Units.val_inj, coe_unitsComplexConj, ringOfIntegersComplexConj_eq_self_iff, realUnits,
    RingHom.mem_range, RingHom.toMonoidHom_eq_coe, MonoidHom.mem_range]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨((hx ▸ u.isUnit).of_map).unit, by simpa [Units.ext_iff] using hx⟩, ?_⟩
  rintro ⟨x, rfl⟩
  exact ⟨x, rfl⟩

end units

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

noncomputable instance ringOfIntegersStarRing : StarRing (𝓞 K) where
  star := CMExtension.ringOfIntegersComplexConj (maximalRealSubfield K) K
  star_involutive := fun _ ↦ CMExtension.ringOfIntegersComplexConj_apply_apply _ _
  star_mul := fun _ _ ↦ by rw [map_mul, mul_comm]
  star_add := fun _ _ ↦ by rw [map_add]

alias complexConj := star

theorem card_infinitePlace_eq_card_infinitePlace :
    Fintype.card (InfinitePlace (maximalRealSubfield K)) = Fintype.card (InfinitePlace K) :=
  CMExtension.card_infinitePlace_eq_card_infinitePlace _ _

theorem units_rank_eq_units_rank :
    Units.rank (maximalRealSubfield K) = Units.rank K :=
  CMExtension.units_rank_eq_units_rank _ _

/--
An element of `K` is fixed by the complex conjugation iff it comes from its maximal real subfield.
-/
theorem complexConj_eq_self_iff (x : K) :
    complexConj x = x ↔ x ∈ (algebraMap (maximalRealSubfield K) K).range :=
  CMExtension.complexConj_eq_self_iff _ x

/--
An element of `𝓞 K` is fixed by the complex conjugation iff it comes from its maximal real subfield.
-/
theorem ringOfIntegersComplexConj_eq_self_iff (x : 𝓞 K) :
    complexConj x = x ↔ x ∈ (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)).range :=
  CMExtension.ringOfIntegersComplexConj_eq_self_iff _ x

/--
The subgroup of `(𝓞 K)ˣ` generated by the units coming from its maximal real subfield. These
units are exactly the units fixed by the complex conjugation,
see `IsCMField.unitsComplexConj_eq_self_iff`.
-/
def realUnits : Subgroup (𝓞 K)ˣ := CMExtension.realUnits (maximalRealSubfield K) K

theorem unitsComplexConj_eq_self_iff (u : (𝓞 K)ˣ) :
    complexConj u = u ↔ u ∈ realUnits K :=
  CMExtension.unitsComplexConj_eq_self_iff (maximalRealSubfield K) u

end IsCMField

end maximalRealSubfield

end NumberField
