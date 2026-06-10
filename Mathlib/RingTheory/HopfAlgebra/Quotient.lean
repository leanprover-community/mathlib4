/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf algebra structure on quotients by Hopf ideals

A *Hopf ideal* of an `R`-Hopf algebra `A` is a biideal stable under the antipode. The quotient
by a Hopf ideal inherits a Hopf algebra structure.

## Main definitions

* `Ideal.IsHopfIdeal R I` : `I` is a coideal (as an `R`-submodule) stable under the antipode.

## Main results

* `HopfAlgebra.ofSurjective` : the Hopf algebra axioms transfer along a surjective bialgebra
  homomorphism intertwining the antipodes.
* `HopfAlgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[I.IsHopfIdeal R]`.
-/

public section

open Bialgebra Coalgebra HopfAlgebra LinearMap TensorProduct WithConv

namespace HopfAlgebra

section ofSurjective

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [HopfAlgebraStruct R B]

/-- Transfer the Hopf algebra axioms along a surjective bialgebra homomorphism `f`
intertwining the antipodes: in convolution-algebra terms, `S_B ⋆ id` and `id ⋆ S_B` pull back
along the coalgebra morphism `f` to the pushforwards of `S_A ⋆ id` and `id ⋆ S_A` along the
algebra morphism `f`, hence to the convolution unit; precomposition by a surjection is
injective. -/
abbrev ofSurjective (f : A →ₐc[R] B) (hf : Function.Surjective f)
    (hS : antipode R ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ antipode R) : HopfAlgebra R B where
  mul_antipode_rTensor_comul := by
    have hf' : Function.Surjective f.toLinearMap := hf
    rw [← LinearMap.cancel_right hf']
    calc (mul' R B ∘ₗ (antipode R).rTensor B ∘ₗ comul) ∘ₗ f.toLinearMap
        = (toConv (antipode R) * toConv .id : WithConv (B →ₗ[R] B)).ofConv ∘ₗ
            f.toCoalgHom.toLinearMap := rfl
      _ = (toConv (antipode R ∘ₗ f.toLinearMap) * toConv f.toLinearMap).ofConv := by
          rw [convMul_comp_coalgHom_distrib]; rfl
      _ = (toConv (f.toLinearMap ∘ₗ antipode R) * toConv f.toLinearMap).ofConv := by
          rw [hS]
      _ = (AlgHomClass.toAlgHom f).toLinearMap ∘ₗ
            (toConv (antipode R) * toConv .id : WithConv (A →ₗ[R] A)).ofConv := by
          rw [algHom_comp_convMul_distrib]; rfl
      _ = f.toLinearMap ∘ₗ (mul' R A ∘ₗ (antipode R).rTensor A ∘ₗ comul) := rfl
      _ = f.toLinearMap ∘ₗ (Algebra.linearMap R A ∘ₗ counit) := by
          rw [mul_antipode_rTensor_comul]
      _ = (Algebra.linearMap R B ∘ₗ counit) ∘ₗ f.toLinearMap := by
          ext a
          simp only [comp_apply, ← LinearMap.congr_fun f.counit_comp a]
          exact AlgHomClass.commutes f _
  mul_antipode_lTensor_comul := by
    have hf' : Function.Surjective f.toLinearMap := hf
    rw [← LinearMap.cancel_right hf']
    calc (mul' R B ∘ₗ (antipode R).lTensor B ∘ₗ comul) ∘ₗ f.toLinearMap
        = (toConv .id * toConv (antipode R) : WithConv (B →ₗ[R] B)).ofConv ∘ₗ
            f.toCoalgHom.toLinearMap := rfl
      _ = (toConv f.toLinearMap * toConv (antipode R ∘ₗ f.toLinearMap)).ofConv := by
          rw [convMul_comp_coalgHom_distrib]; rfl
      _ = (toConv f.toLinearMap * toConv (f.toLinearMap ∘ₗ antipode R)).ofConv := by
          rw [hS]
      _ = (AlgHomClass.toAlgHom f).toLinearMap ∘ₗ
            (toConv .id * toConv (antipode R) : WithConv (A →ₗ[R] A)).ofConv := by
          rw [algHom_comp_convMul_distrib]; rfl
      _ = f.toLinearMap ∘ₗ (mul' R A ∘ₗ (antipode R).lTensor A ∘ₗ comul) := rfl
      _ = f.toLinearMap ∘ₗ (Algebra.linearMap R A ∘ₗ counit) := by
          rw [mul_antipode_lTensor_comul]
      _ = (Algebra.linearMap R B ∘ₗ counit) ∘ₗ f.toLinearMap := by
          ext a
          simp only [comp_apply, ← LinearMap.congr_fun f.counit_comp a]
          exact AlgHomClass.commutes f _

end ofSurjective

end HopfAlgebra

variable {R A : Type*} [CommRing R] [Ring A]

section HopfAlgebraStruct

variable [HopfAlgebraStruct R A]

variable (R) in
/-- An ideal whose underlying `R`-submodule is a coideal and which is stable under the
antipode (`S(I) ⊆ I`). Together with `I.IsTwoSided`, this makes `I` a *Hopf ideal*. -/
@[mk_iff]
class Ideal.IsHopfIdeal (I : Ideal A) : Prop extends (I.restrictScalars R).IsCoideal where
  antipode_mem : ∀ ⦃x : A⦄, x ∈ I → antipode R x ∈ I

end HopfAlgebraStruct

namespace HopfAlgebra.Quotient

section HopfAlgebraStruct

variable [HopfAlgebraStruct R A] (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]

instance : HopfAlgebraStruct R (A ⧸ I) where
  antipode := Submodule.mapQ (I.restrictScalars R) (I.restrictScalars R)
    (antipode R) (Ideal.IsHopfIdeal.antipode_mem (R := R))

@[simp]
lemma antipode_mk (a : A) :
    antipode R (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (antipode R a) := rfl

lemma antipode_comp_mkₐ :
    antipode R ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap =
      (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ antipode R := by ext; simp

end HopfAlgebraStruct

variable [HopfAlgebra R A] (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]

instance : HopfAlgebra R (A ⧸ I) :=
  .ofSurjective (Bialgebra.Quotient.mkBialgHom I) Ideal.Quotient.mk_surjective
    (antipode_comp_mkₐ I)

end HopfAlgebra.Quotient
