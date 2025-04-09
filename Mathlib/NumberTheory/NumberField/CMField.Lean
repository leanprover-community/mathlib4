/-
Copyright (c) 2025 X. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# CM-extension of number fields

A CM-extension of number fields is a totally complex number field that is a quadratic extension of
a totally real number field.

## Main definitions

* `maximalRealSubfield`: the maximal real subfield of a number field.

* `IsCMExtension`: a Prop on two number fields `F` and `K` stating that `K/F` is a CM-extension.

* `IsCM`: a Prop on a number field `K` stating that `K/maximalRealSubfield ℚ K` is
  a CM-extension


## Main results

* `NumberField.IsCM.ofIsCMExtension`: Let `K` be a number field and assume that there exists `F`
  such that `K/F` is a CM-extension. Then `K` is CM.

## Implementation notes

Let `K` be a field such that `IsCM K`. Then `K` is a CM-extension over its real maximal subfield.
However, we keep `IsCMExtension` for flexibility since it gives us the possibility to consider `K`
as a CM-extension over some other field.

-/

open NumberField InfinitePlace ComplexEmbedding

namespace NumberField

section MaximalRealSubfield

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/--
The intermediate field of an extension `K/F` that is fixed by all the conjugations.
It contains all the totally real subfields of `K/F`, see `IsTotallyReal.le_maximalRealSubfield`,
and is totally real if the extension is Galois and `F` is totally real, see
`isTotallyReal_maximalRealSubfield`.
-/
def maximalRealSubfield : IntermediateField F K :=
  .fixedField (Subgroup.closure {σ : K ≃ₐ[F] K | ∃ φ : K →+* ℂ, IsConj φ σ})

instance isTotallyReal_maximalRealSubfield [NumberField F] [NumberField K] [IsTotallyReal F]
    [IsGalois F K] :
    IsTotallyReal (maximalRealSubfield F K) where
  isReal w := by
    letI := w.embedding.toAlgebra
    let φ : K →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := (maximalRealSubfield F K))).toRingHom
    have hφ : w.embedding = φ.comp (algebraMap _ K) := by
      unfold φ
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, RingHom.algebraMap_toAlgebra]
    obtain h | h := isReal_or_isComplex (.mk φ)
    · rw [← mk_embedding w, hφ, ← comap_mk]
      exact IsReal.comap _ h
    · obtain ⟨σ, hσ⟩ : ∃ σ : K ≃ₐ[F] K, IsConj φ σ :=
        exists_isConj_of_not_isUnramified <| not_isUnramified_iff.mpr ⟨h, IsTotallyReal.isReal _⟩
      refine InfinitePlace.isReal_iff.mpr ?_
      rw [hφ, isReal_embedding_comp_algebraMap_iff_isConj_mem hσ, maximalRealSubfield,
        IntermediateField.fixingSubgroup_fixedField]
      exact Subgroup.subset_closure ⟨_, hσ⟩

variable {F K} in
theorem IsTotallyReal.le_maximalRealSubfield [NumberField F] [NumberField K]
    {E : IntermediateField F K} (h : IsTotallyReal E) : E ≤ maximalRealSubfield F K := by
  rw [maximalRealSubfield, IntermediateField.le_iff_le, Subgroup.closure_le]
  intro σ ⟨φ, hσ⟩
  rw [SetLike.mem_coe, ← isReal_embedding_comp_algebraMap_iff_isConj_mem hσ, ← isReal_mk_iff]
  exact (isTotallyReal_iff _).mp h _

/--
The `maximalRealSubfield F K` is equal to `K` iff all the conjugations are trivial.
-/
theorem maximalRealSubfield_eq_top_iff :
     maximalRealSubfield F K = ⊤ ↔ ∀ φ : K →+* ℂ, ∀ σ : K ≃ₐ[F] K, IsConj φ σ → σ = 1 := by
  simp_rw [IntermediateField.ext_iff, IntermediateField.mem_top, iff_true, maximalRealSubfield,
    IntermediateField.mem_fixedField_iff]
  refine ⟨fun h φ σ hσ ↦ ?_, fun h x f hf ↦ ?_⟩
  · ext x
    exact h x σ <| Subgroup.subset_closure ⟨φ, hσ⟩
  · induction hf using Subgroup.closure_induction with
    | mem σ hσ =>
        obtain ⟨φ, hφ⟩ := hσ
        exact AlgEquiv.congr_fun (h φ σ hφ ) x
    | one => rw [AlgEquiv.one_apply]
    | mul f g _ _ hf hg => rw [AlgEquiv.mul_apply, hg, hf]
    | inv f _ hf => rwa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, eq_comm]

theorem two_le_finrank_maximalRealSubfield [FiniteDimensional F K] {φ : K →+* ℂ} {σ : K ≃ₐ[F] K}
    (hφ : ¬ComplexEmbedding.IsReal φ) (hσ : IsConj φ σ) :
    2 ≤ Module.finrank (maximalRealSubfield F K) K := by
  classical
  rw [maximalRealSubfield, IntermediateField.finrank_fixedField_eq_card, Nat.succ_le_iff,
    Fintype.one_lt_card_iff]
  refine ⟨1, ⟨σ, Subgroup.subset_closure ⟨φ, hσ⟩⟩, ?_⟩
  by_contra h
  simp only [Subtype.ext_iff_val, OneMemClass.coe_one] at h
  rw [← h, isConj_one_iff] at hσ
  exact hφ hσ

end MaximalRealSubfield

/--
An extension `K/F` of number fields is a `CM`-extension if `K` is totally complex, `F` is totally
real and the extension `K/F` is of degree `2`.
-/
class IsCMExtension (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Prop
  extends IsTotallyReal F, IsTotallyComplex K where
  finrank_eq_two' : Module.finrank F K = 2

/--
A field `K` is `CM` if it is a `CM`-extension over its maximal real subfield of `K`.
-/
class IsCM (K : Type*) [Field K] [NumberField K] : Prop where
  CMExtension : IsCMExtension (maximalRealSubfield ℚ K) K

namespace IsCMExtension

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem isTotallyComplex [IsCMExtension F K] :
    IsTotallyComplex K := toIsTotallyComplex F

theorem isTotallyReal [IsCMExtension F K] :
    IsTotallyReal F := toIsTotallyReal K

theorem finrank_eq_two [IsCMExtension F K] :
    Module.finrank F K = 2 := finrank_eq_two'

section FirstResults

variable [IsCMExtension F K]

instance : IsGalois F K :=
{ to_isSeparable := Algebra.IsSeparable.of_integral _ _
  to_normal := normal_of_finrank_eq_two _ _ (finrank_eq_two F K) }

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

variable {F K} in
theorem ofRingEquiv {E : Type*} [Field E] [NumberField E] [Algebra E K] {f : E ≃+* F}
    (hf : (algebraMap F K).comp f = algebraMap E K) :
    IsCMExtension E K where
  isReal := fun v ↦ (IsTotallyReal.ofRingEquiv f.symm).isReal v
  finrank_eq_two' := by
    rw [← IsCMExtension.finrank_eq_two (F := F) (K := K)]
    exact congr_arg Cardinal.toNat <|
      Algebra.rank_eq_of_equiv_equiv f (RingEquiv.refl K) (by simp [hf])

end FirstResults

noncomputable section ComplexConj

variable (F : Type*) {K : Type*} [Field F] [Field K] [NumberField K] [Algebra F K]

variable [NumberField F]

/--
All complex embeddings of a Galois extension of a totally complex field over a totally real field
admit a conjugation.
-/
theorem exists_isConj [IsTotallyReal F] [IsTotallyComplex K] [IsGalois F K] (φ : K →+* ℂ) :
    ∃ σ : K ≃ₐ[F] K, IsConj φ σ :=
  exists_isConj_of_not_isUnramified <|
    not_isUnramified_iff.mpr ⟨IsTotallyComplex.isComplex _, IsTotallyReal.isReal _⟩

end ComplexConj

noncomputable section MaximalRealSubfield

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [IsTotallyReal F] [IsTotallyComplex K]

theorem eq_maximalRealSubfield (E : IntermediateField ℚ K) [h : IsCMExtension E K] :
    E = maximalRealSubfield ℚ K := by
  refine IntermediateField.eq_of_le_of_finrank_le' ?_ ?_
  · exact IsTotallyReal.le_maximalRealSubfield h.toIsTotallyReal
  · rw [h.finrank_eq_two]
    obtain φ := (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))
    obtain ⟨σ, hσ⟩ := exists_isConj E φ
    refine two_le_finrank_maximalRealSubfield ℚ K (σ := σ.restrictScalars ℚ) ?_ hσ
    exact isComplex_mk_iff.mp <| IsTotallyComplex.isComplex _

variable (F K) in
/--
Any field `F` such that `K/F` is a CM-extension is isomorphic as a ring to the maximal
real subfield of `K/ℚ`.
-/
def maximalRealSubfieldEquiv [h : IsCMExtension F K] :
    maximalRealSubfield ℚ K ≃+* F := by
  let E := AlgHom.fieldRange (algebraMap F K).toRatAlgHom
  have hE : IsCMExtension E K := by
      refine ofRingEquiv (F := F) (f := (algebraMap F K).rangeRestrictFieldEquiv.symm) ?_
      exact RingHom.ext fun x ↦ (algebraMap F K).rangeRestrictFieldEquiv_apply_symm_apply x
  exact ((algebraMap F K).rangeRestrictFieldEquiv.trans <|
    (IntermediateField.equivOfEq hE.eq_maximalRealSubfield).toRingEquiv).symm

omit [IsTotallyReal F] in
@[simp]
theorem algebraMap_maximalRealSubfieldEquiv [h : IsCMExtension F K] (x : maximalRealSubfield ℚ K) :
   algebraMap F K (maximalRealSubfieldEquiv F K x) = x := by
  unfold maximalRealSubfieldEquiv
  rw [RingEquiv.symm_trans_apply, AlgEquiv.toRingEquiv_eq_coe,
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
  rfl

omit [IsTotallyReal F] in
theorem _root_.NumberField.IsCM.ofIsCMExtension [h : IsCMExtension F K] :
    IsCM K where
  CMExtension := ofRingEquiv (f := maximalRealSubfieldEquiv F K) (by ext; simp)

end MaximalRealSubfield

end IsCMExtension

end NumberField
