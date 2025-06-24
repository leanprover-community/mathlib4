/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Unramified.Finite

/-!
# Unramified algebras over fields

## Main results

Let `K` be a field, `A` be a `K`-algebra and `L` be a field extension of `K`.

- `Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing`:
    If `A` is `K`-unramified and `K` is alg-closed, then `K = A`.
- `Algebra.FormallyUnramified.isReduced_of_field`:
    If `A` is `K`-unramified then `A` is reduced.
- `Algebra.FormallyUnramified.iff_isSeparable`:
    `L` is unramified over `K` iff `L` is separable over `K`.

## References

- [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*][iversen]

-/

universe u

variable (K A L : Type*) [Field K] [Field L] [CommRing A] [Algebra K A] [Algebra K L]

open Algebra Polynomial

open scoped TensorProduct

namespace Algebra.FormallyUnramified

theorem of_isSeparable [Algebra.IsSeparable K L] : FormallyUnramified K L := by
  rw [iff_comp_injective]
  intros B _ _ I hI f₁ f₂ e
  ext x
  have : f₁ x - f₂ x ∈ I := by
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun e x
  have := Polynomial.eval_add_of_sq_eq_zero ((minpoly K x).map (algebraMap K B)) (f₂ x)
    (f₁ x - f₂ x) (show (f₁ x - f₂ x) ^ 2 ∈ ⊥ from hI ▸ Ideal.pow_mem_pow this 2)
  simp only [add_sub_cancel, eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero,
    derivative_map, zero_add] at this
  rwa [eq_comm, ((isUnit_iff_ne_zero.mpr
    ((Algebra.IsSeparable.isSeparable K x).aeval_derivative_ne_zero
      (minpoly.aeval K x))).map f₂).mul_right_eq_zero, sub_eq_zero] at this

variable [FormallyUnramified K A] [EssFiniteType K A]
variable [FormallyUnramified K L] [EssFiniteType K L]

theorem bijective_of_isAlgClosed_of_isLocalRing
    [IsAlgClosed K] [IsLocalRing A] :
    Function.Bijective (algebraMap K A) := by
  have := finite_of_free (R := K) (S := A)
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  have hA : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥]
    · exact IsArtinianRing.isNilpotent_jacobson_bot
    · exact bot_ne_top
  let e : K ≃ₐ[K] A ⧸ IsLocalRing.maximalIdeal A := {
    __ := Algebra.ofId K (A ⧸ IsLocalRing.maximalIdeal A)
    __ := Equiv.ofBijective _ IsAlgClosed.algebraMap_bijective_of_isIntegral }
  let e' : A ⊗[K] (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[A] A :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans (Algebra.TensorProduct.rid K A A)
  let f : A ⧸ IsLocalRing.maximalIdeal A →ₗ[A] A := e'.toLinearMap.comp (sec K A _)
  have hf : (Algebra.ofId _ _).toLinearMap ∘ₗ f = LinearMap.id := by
    dsimp [f]
    rw [← LinearMap.comp_assoc, ← comp_sec K A]
    congr 1
    apply LinearMap.restrictScalars_injective K
    apply _root_.TensorProduct.ext'
    intros r s
    obtain ⟨s, rfl⟩ := e.surjective s
    suffices s • (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) r = r • e s by
      simpa [ofId, e']
    simp [Algebra.smul_def, e, ofId, mul_comm]
  have hf₁ : f 1 • (1 : A ⧸ IsLocalRing.maximalIdeal A) = 1 := by
    rw [← algebraMap_eq_smul_one]
    exact LinearMap.congr_fun hf 1
  have hf₂ : 1 - f 1 ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← Ideal.Quotient.algebraMap_eq,
     algebraMap_eq_smul_one, hf₁, sub_self]
  have hf₃ : IsIdempotentElem (1 - f 1) := by
    apply IsIdempotentElem.one_sub
    rw [IsIdempotentElem, ← smul_eq_mul, ← map_smul, hf₁]
  have hf₄ : f 1 = 1 := by
    obtain ⟨n, hn⟩ := hA
    have : (1 - f 1) ^ n = 0 := by
      rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hn]
      exact Ideal.pow_mem_pow hf₂ n
    rw [eq_comm, ← sub_eq_zero, ← hf₃.pow_succ_eq n, pow_succ, this, zero_mul]
  refine Equiv.bijective ⟨algebraMap K A, ⇑e.symm ∘ ⇑(algebraMap A _), fun x ↦ by simp, fun x ↦ ?_⟩
  have : ⇑(algebraMap K A) = ⇑f ∘ ⇑e := by
    ext k
    conv_rhs => rw [← mul_one k, ← smul_eq_mul, Function.comp_apply, map_smul,
      LinearMap.map_smul_of_tower, map_one, hf₄, ← algebraMap_eq_smul_one]
  rw [this]
  simp only [Function.comp_apply, AlgEquiv.apply_symm_apply, algebraMap_eq_smul_one,
    map_smul, hf₄, smul_eq_mul, mul_one]

theorem isField_of_isAlgClosed_of_isLocalRing
    [IsAlgClosed K] [IsLocalRing A] : IsField A := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := (bijective_of_isAlgClosed_of_isLocalRing K A).surjective x
  show _ = 0
  rw [← (algebraMap K A).map_zero]
  by_contra hx'
  exact hx ((isUnit_iff_ne_zero.mpr
    (fun e ↦ hx' ((algebraMap K A).congr_arg e))).map (algebraMap K A))

@[deprecated (since := "2024-11-12")]
alias bijective_of_isAlgClosed_of_localRing := bijective_of_isAlgClosed_of_isLocalRing

@[deprecated (since := "2024-11-12")]
alias isField_of_isAlgClosed_of_localRing := isField_of_isAlgClosed_of_isLocalRing

include K in
theorem isReduced_of_field :
    IsReduced A := by
  constructor
  intro x hx
  let f := (Algebra.TensorProduct.includeRight (R := K) (A := AlgebraicClosure K) (B := A))
  have : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor A (Algebra.ofId K (AlgebraicClosure K)).toLinearMap).comp
        (Algebra.TensorProduct.lid K A).symm.toLinearMap := by
      ext x; simp [f]
    rw [this]
    suffices Function.Injective
        (LinearMap.rTensor A (Algebra.ofId K (AlgebraicClosure K)).toLinearMap) by
      exact this.comp (Algebra.TensorProduct.lid K A).symm.injective
    apply Module.Flat.rTensor_preserves_injective_linearMap
    exact (algebraMap K _).injective
  apply this
  rw [map_zero]
  apply eq_zero_of_localization
  intro M hM
  have hy := (hx.map f).map (algebraMap _ (Localization.AtPrime M))
  generalize algebraMap _ (Localization.AtPrime M) (f x) = y at *
  have := EssFiniteType.of_isLocalization (Localization.AtPrime M) M.primeCompl
  have := of_isLocalization (Rₘ := Localization.AtPrime M) M.primeCompl
  have := EssFiniteType.comp (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
    (Localization.AtPrime M)
  have := comp (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
    (Localization.AtPrime M)
  letI := (isField_of_isAlgClosed_of_isLocalRing (AlgebraicClosure K)
    (A := Localization.AtPrime M)).toField
  exact hy.eq_zero

theorem range_eq_top_of_isPurelyInseparable
    [IsPurelyInseparable K L] : (algebraMap K L).range = ⊤ := by
  classical
  have : Nontrivial (L ⊗[K] L) := by
    rw [← not_subsingleton_iff_nontrivial, ← rank_zero_iff (R := K), rank_tensorProduct',
      mul_eq_zero, or_self, rank_zero_iff, not_subsingleton_iff_nontrivial]
    infer_instance
  rw [← top_le_iff]
  intro x _
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem K (ringExpChar K) x
  have : ExpChar (L ⊗[K] L) (ringExpChar K) := by
    refine expChar_of_injective_ringHom (algebraMap K _).injective (ringExpChar K)
  have : (1 ⊗ₜ x - x ⊗ₜ 1 : L ⊗[K] L) ^ (ringExpChar K) ^ n = 0 := by
    rw [sub_pow_expChar_pow, TensorProduct.tmul_pow, one_pow, TensorProduct.tmul_pow, one_pow]
    obtain ⟨r, hr⟩ := hn
    rw [← hr, algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]
  have H : (1 ⊗ₜ x : L ⊗[K] L) = x ⊗ₜ 1 := by
    have inst : IsReduced (L ⊗[K] L) := isReduced_of_field L _
    exact sub_eq_zero.mp (IsNilpotent.eq_zero ⟨_, this⟩)
  by_cases h' : LinearIndependent K ![1, x]
  · have h := h'.linearIndepOn_id
    let S := h.extend (Set.subset_univ _)
    let a : S := ⟨1, h.subset_extend _ (by simp)⟩
    have ha : Basis.extend h a = 1 := by simp [a]
    let b : S := ⟨x, h.subset_extend _ (by simp)⟩
    have hb : Basis.extend h b = x := by simp [b]
    by_cases e : a = b
    · obtain rfl : 1 = x := congr_arg Subtype.val e
      exact ⟨1, map_one _⟩
    have := DFunLike.congr_fun
      (DFunLike.congr_arg ((Basis.extend h).tensorProduct (Basis.extend h)).repr H) (a, b)
    simp only [Basis.tensorProduct_repr_tmul_apply, ← ha, ← hb, Basis.repr_self, smul_eq_mul,
      Finsupp.single_apply, e, Ne.symm e, ↓reduceIte, mul_one, mul_zero, one_ne_zero] at this
  · rw [LinearIndependent.pair_iff] at h'
    simp only [not_forall, not_and, exists_prop] at h'
    obtain ⟨a, b, e, hab⟩ := h'
    have : IsUnit b := by
      rw [isUnit_iff_ne_zero]
      rintro rfl
      rw [zero_smul, ← algebraMap_eq_smul_one, add_zero,
        (injective_iff_map_eq_zero' _).mp (algebraMap K L).injective] at e
      cases hab e rfl
    use (-this.unit⁻¹ * a)
    rw [map_mul, ← Algebra.smul_def, algebraMap_eq_smul_one, eq_neg_iff_add_eq_zero.mpr e,
      smul_neg, neg_smul, neg_neg, smul_smul, this.val_inv_mul, one_smul]

theorem isSeparable : Algebra.IsSeparable K L := by
  have := finite_of_free (R := K) (S := L)
  rw [← separableClosure.eq_top_iff]
  have := of_comp K (separableClosure K L) L
  have := EssFiniteType.of_comp K (separableClosure K L) L
  ext
  show _ ↔ _ ∈ (⊤ : Subring _)
  rw [← range_eq_top_of_isPurelyInseparable (separableClosure K L) L]
  simp

theorem iff_isSeparable (L : Type u) [Field L] [Algebra K L] [EssFiniteType K L] :
    FormallyUnramified K L ↔ Algebra.IsSeparable K L :=
  ⟨fun _ ↦ isSeparable K L, fun _ ↦ of_isSeparable K L⟩

end Algebra.FormallyUnramified
