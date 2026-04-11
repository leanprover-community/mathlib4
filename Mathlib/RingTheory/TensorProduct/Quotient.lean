/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Interaction between quotients and tensor products for algebras

This file proves algebra analogs of the isomorphisms in
`Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`.

## Main results

- `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`:
  `B ⧸ (I.map <| algebraMap A B) ≃ₐ[B] B ⊗[A] (A ⧸ I)`
-/

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

section

variable {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

set_option backward.privateInPublic true in
private noncomputable def quotIdealMapEquivTensorQuotAux :
      (B ⧸ (I.map <| algebraMap A B)) ≃ₗ[B] B ⊗[A] (A ⧸ I) :=
  AddEquiv.toLinearEquiv (TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)).symm <| by
    intro c x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

private lemma quotIdealMapEquivTensorQuotAux_mk (b : B) :
    (quotIdealMapEquivTensorQuotAux B I) b = b ⊗ₜ[A] 1 :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `B ⊗[A] (A ⧸ I)` is isomorphic as a `B`-algebra to `B ⧸ I B`. -/
noncomputable def quotIdealMapEquivTensorQuot :
    (B ⧸ (I.map <| algebraMap A B)) ≃ₐ[B] B ⊗[A] (A ⧸ I) :=
  AlgEquiv.ofLinearEquiv (quotIdealMapEquivTensorQuotAux B I) rfl
    (fun x y ↦ by
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp_rw [← map_mul, quotIdealMapEquivTensorQuotAux_mk]
      simp)

@[simp]
lemma quotIdealMapEquivTensorQuot_mk (b : B) :
    quotIdealMapEquivTensorQuot B I b = b ⊗ₜ[A] 1 :=
  rfl

@[simp]
lemma quotIdealMapEquivTensorQuot_symm_tmul (b : B) (a : A) :
    (quotIdealMapEquivTensorQuot B I).symm (b ⊗ₜ[A] a) = Submodule.Quotient.mk (a • b) :=
  rfl

/-- `(A ⧸ I) ⊗[A] B` is isomorphic as an `A ⧸ I`-algebra to `B ⧸ I B`. -/
noncomputable def quotIdealMapEquivQuotTensor :
    (B ⧸ (I.map (algebraMap A B))) ≃ₐ[A ⧸ I] (A ⧸ I) ⊗[A] B :=
  AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  { __ := (quotIdealMapEquivTensorQuot B I).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (A ⧸ I)).toRingEquiv
    commutes' x := by
      suffices Algebra.TensorProduct.comm A B (A ⧸ I) (quotIdealMapEquivTensorQuot B I
        (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B x))) =
          (algebraMap A (TensorProduct A (A ⧸ I) B)) x by simpa
      rw [quotIdealMapEquivTensorQuot_mk, tmul_one_eq_one_tmul]
      simp }

@[simp]
lemma quotIdealMapEquivQuotTensor_mk (b : B) :
    quotIdealMapEquivQuotTensor B I b = 1 ⊗ₜ[A] b :=
  rfl

end

section

variable {R : Type*} (S T A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- The tensor product of an `S`-algebra `A` over `R` with the quotient of `T` by an ideal `I`
is isomorphic (as an `S`-algebra) to the quotient of `A ⊗[R] T` by the extended ideal. -/
noncomputable def tensorQuotientEquiv (I : Ideal T) :
    A ⊗[R] (T ⧸ I) ≃ₐ[S] (A ⊗[R] T) ⧸ I.map (includeRight (A := A) (R := R)) :=
  letI g : (A ⊗[R] T ⧸ LinearMap.range (AlgebraTensorModule.lTensor S A
      (I.subtype.restrictScalars R))) ≃ₗ[S]
      A ⊗[R] T ⧸ (I.map (includeRight (A := A) (R := R))).restrictScalars S :=
    Submodule.quotEquivOfEq _ _ (AlgebraTensorModule.range_lTensor_idealMap _ _ _)
  .ofLinearEquiv (AlgebraTensorModule.tensorQuotientEquiv (R := R) S T A I ≪≫ₗ g) rfl <| by
    refine LinearMap.map_mul_of_map_mul_tmul fun a₁ a₂ b₁ b₂ ↦ ?_
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective b₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective b₂
    rw [← map_mul]
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, g,
      AlgebraTensorModule.tensorQuotientEquiv_apply_tmul, ← Ideal.Quotient.mk_eq_mk,
      ← Algebra.TensorProduct.tmul_mul_tmul]
    rfl

@[simp]
lemma tensorQuotientEquiv_apply_tmul (I : Ideal T) (a : A) (t : T) :
    tensorQuotientEquiv (R := R) S T A I (a ⊗ₜ t) = a ⊗ₜ[R] t :=
  rfl

@[simp]
lemma tensorQuotientEquiv_symm_apply_tmul (I : Ideal T) (a : A) (t : T) :
    (tensorQuotientEquiv (R := R) S T A I).symm (a ⊗ₜ[R] t) = a ⊗ₜ[R] (Ideal.Quotient.mk I t) :=
  rfl

/-- The tensor product over `R` of the quotient of an `S`-algebra `A` by an ideal `I` with `T`
is isomorphic (as an `S`-algebra) to the quotient of `A ⊗[R] T` by the extended ideal. -/
noncomputable def quotientTensorEquiv (I : Ideal A) :
    (A ⧸ I) ⊗[R] T ≃ₐ[S] (A ⊗[R] T) ⧸ I.map (algebraMap A (A ⊗[R] T)) where
  __ := (TensorProduct.comm R (A ⧸ I) T).toRingEquiv.trans <|
    (tensorQuotientEquiv (R := R) R A T I).toRingEquiv.trans <|
    Ideal.quotientEquiv _ _ (TensorProduct.comm R T A).toRingEquiv <| (I.map_map _ _).symm
  commutes' _ := rfl

@[simp]
lemma quotientTensorEquiv_apply_tmul (I : Ideal A) (a : A) (t : T) :
    quotientTensorEquiv (R := R) S T A I (a ⊗ₜ t) = a ⊗ₜ[R] t :=
  rfl

@[simp]
lemma quotientTensorEquiv_symm_apply_tmul (I : Ideal A) (a : A) (t : T) :
    (quotientTensorEquiv (R := R) S T A I).symm (a ⊗ₜ[R] t) = Ideal.Quotient.mk _ a ⊗ₜ[R] t :=
  rfl

end

end Algebra.TensorProduct

lemma Ideal.subtype_rTensor_range {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).range = I • (⊤ : Submodule R M) := by
  rw [← Submodule.ker_mkQ (I • (⊤ : Submodule R M)), LinearMap.range_comp,
    ← Submodule.map_symm_eq_iff, ← Submodule.comap_equiv_eq_map_symm, ← LinearMap.ker_comp,
    ← TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor, LinearEquiv.ker_comp]
  exact LinearMap.exact_iff.mp (rTensor_exact M (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)
