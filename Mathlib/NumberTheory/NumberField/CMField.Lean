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

* `IsCM`: a Prop on a number field `K` stating that there exists a subfield `F` such that `K/F` is
  a CM-extension

## Implementation notes

Let `K` be a field such that `IsCM K`. Then `K` is a CM-extension over its real maximal subfield.
However, we keep `IsCMExtension` for flexibility since it gives us the possibility to consider `K`
as a CM-extension over some other field.

-/

open NumberField InfinitePlace ComplexEmbedding

namespace NumberField

section maximalRealSubfield

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

theorem IsTotallyReal.le_maximalRealSubfield [NumberField F] [NumberField K]
    {E : IntermediateField F K} (h : IsTotallyReal E) : E ≤ maximalRealSubfield F K := by
  rw [maximalRealSubfield, IntermediateField.le_iff_le, Subgroup.closure_le]
  intro σ ⟨φ, hσ⟩
  rw [SetLike.mem_coe, ← isReal_embedding_comp_algebraMap_iff_isConj_mem hσ, ← isReal_mk_iff]
  exact (isTotallyReal_iff _).mp h _

end maximalRealSubfield

/--
An extension `K/F` of number fields is a `CM`-extension if `K` is totally complex, `F` is totally
real and the extension `K/F` is of degree `2`.
-/
class IsCMExtension (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] : Prop
  extends IsTotallyReal F, IsTotallyComplex K where
  finrank_eq_two' : Module.finrank F K = 2

/--
A field `K` is `CM` if it admits a subfield `F` such that `IsCMExtension F K`.
In this case, one can take `F` to be the maximal real subfield of `K`.
-/
class IsCM (K : Type*) [Field K] [NumberField K] : Prop where
  exists_CMExtension :
    ∃ (F : Type*) (_ : Field F) (_ : NumberField F) (_ : Algebra F K), IsCMExtension F K

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

end FirstResults

end IsCMExtension

end NumberField
