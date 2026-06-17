/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Convolution

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

open Bialgebra Bialgebra.Quotient Coalgebra HopfAlgebra Ideal.Quotient LinearMap
  TensorProduct WithConv

namespace HopfAlgebra

section ofSurjective

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [HopfAlgebraStruct R B]

/-- Post-composition by an algebra homomorphism preserves the convolution unit. -/
lemma _root_.LinearMap.algHom_comp_convOne (g : A →ₐ[R] B) :
    g.toLinearMap ∘ₗ (1 : WithConv (A →ₗ[R] A)).ofConv = (1 : WithConv (A →ₗ[R] B)).ofConv := by
  ext a; simp

/-- Pre-composition by a coalgebra homomorphism preserves the convolution unit. -/
lemma _root_.LinearMap.convOne_comp_coalgHom (g : A →ₗc[R] B) :
    (1 : WithConv (B →ₗ[R] B)).ofConv ∘ₗ g.toLinearMap = (1 : WithConv (A →ₗ[R] B)).ofConv := by
  ext a; simp

/-- Transfer the Hopf algebra axioms along a surjective bialgebra homomorphism intertwining
the antipodes. -/
noncomputable abbrev ofSurjective (f : A →ₐc[R] B) (hf : Function.Surjective f)
    (hS : antipode R ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ antipode R) : HopfAlgebra R B := by
  refine .ofConvInverse (antipode R) (ofConv_injective ?_) (ofConv_injective ?_) <;>
    rw [← LinearMap.cancel_right (show Function.Surjective f.toLinearMap from hf)]
  · calc (toConv (antipode R) * toConv .id : WithConv (B →ₗ[R] B)).ofConv ∘ₗ
          f.toCoalgHom.toLinearMap
        = (toConv (f.toLinearMap ∘ₗ antipode R) * toConv f.toLinearMap).ofConv := by
          rw [convMul_comp_coalgHom_distrib, hS]; rfl
      _ = (AlgHomClass.toAlgHom f).toLinearMap ∘ₗ
            (toConv (antipode R) * toConv .id : WithConv (A →ₗ[R] A)).ofConv := by
          rw [algHom_comp_convMul_distrib]; rfl
      _ = (1 : WithConv (B →ₗ[R] B)).ofConv ∘ₗ f.toLinearMap := by
          rw [antipode_mul_id, algHom_comp_convOne, ← convOne_comp_coalgHom f.toCoalgHom]
  · calc (toConv .id * toConv (antipode R) : WithConv (B →ₗ[R] B)).ofConv ∘ₗ
          f.toCoalgHom.toLinearMap
        = (toConv f.toLinearMap * toConv (f.toLinearMap ∘ₗ antipode R)).ofConv := by
          rw [convMul_comp_coalgHom_distrib, hS]; rfl
      _ = (AlgHomClass.toAlgHom f).toLinearMap ∘ₗ
            (toConv .id * toConv (antipode R) : WithConv (A →ₗ[R] A)).ofConv := by
          rw [algHom_comp_convMul_distrib]; rfl
      _ = (1 : WithConv (B →ₗ[R] B)).ofConv ∘ₗ f.toLinearMap := by
          rw [id_mul_antipode, algHom_comp_convOne, ← convOne_comp_coalgHom f.toCoalgHom]

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

noncomputable instance : HopfAlgebra R (A ⧸ I) :=
  .ofSurjective (mkBialgHom I) mk_surjective (antipode_comp_mkₐ I)

end HopfAlgebra.Quotient
