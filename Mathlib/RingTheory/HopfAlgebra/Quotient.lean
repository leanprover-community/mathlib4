/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf algebra structure on quotients

The quotient of an `R`-Hopf algebra `A` by a two-sided ideal `I` inherits the Hopf
structure exactly when `I` is a *Hopf ideal*: a bialgebra ideal stable under the antipode.
The same descent condition can be stated on a generating relation `r`.

## Main definitions

* `IsHopfRel R r` — Hopf descent condition on a generating relation.
* `IsHopfIdeal R I` — Hopf descent condition on a two-sided ideal of `A`.

## Main results

* `HopfAlgebra R (A ⧸ I)` instance from `[IsHopfIdeal R I]`.

## TODO

* `HopfAlgebra R (RingQuot r)` instance from `[IsHopfRel R r]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap TensorProduct

/-! ### Hopf relation predicate (`RingQuot` carrier) -/

section RingQuot

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

variable (R) in
/-- A relation `r` on an `R`-Hopf algebra `A` is a *Hopf relation* if it is a bialgebra
relation and the antipode identifies related elements after projection to `RingQuot r`. -/
class IsHopfRel (r : A → A → Prop) : Prop extends IsBialgebraRel R r where
  antipode_map_eq : ∀ ⦃x y : A⦄, r x y →
    (RingQuot.mkAlgHom R r).toLinearMap (HopfAlgebra.antipode R x) =
      (RingQuot.mkAlgHom R r).toLinearMap (HopfAlgebra.antipode R y)

end RingQuot

/-! ### Hopf algebra structure on the quotient by a Hopf ideal -/

section Ideal

variable {R A : Type*} [CommRing R] [Ring A] [HopfAlgebra R A]

variable (R) in
/-- A two-sided ideal `I` of an `R`-Hopf algebra `A` is a *Hopf ideal* if it is a bialgebra ideal
and is stable under the antipode. -/
class IsHopfIdeal (I : Ideal A) : Prop extends IsBialgebraIdeal R I where
  antipode_mem : ∀ ⦃x : A⦄, x ∈ I → HopfAlgebra.antipode R x ∈ I

namespace IsHopfIdeal

variable (I : Ideal A) [IsHopfIdeal R I]

variable (R) in
/-- The antipode on `A ⧸ I`, lifted from the antipode on `A`. -/
noncomputable def quotientAntipode : (A ⧸ I) →ₗ[R] (A ⧸ I) :=
  (I.restrictScalars R).liftQ
    ((Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ HopfAlgebra.antipode R)
    (fun a ha => by
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact IsHopfIdeal.antipode_mem (R := R) ha)

@[simp]
lemma quotientAntipode_mk (a : A) :
    quotientAntipode R I (Ideal.Quotient.mk I a : A ⧸ I) =
      Ideal.Quotient.mk I (HopfAlgebra.antipode R a) :=
  rfl

noncomputable instance : HopfAlgebraStruct R (A ⧸ I) where
  antipode := quotientAntipode R I

lemma antipode_comp_mkₐ :
    (HopfAlgebraStruct.antipode (A := A ⧸ I) R).comp (Ideal.Quotient.mkₐ R I).toLinearMap =
      (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ HopfAlgebra.antipode R :=
  LinearMap.ext fun _ => rfl

lemma mul'_comp_map_mkₐ :
    mul' R (A ⧸ I) ∘ₗ TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap =
      (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ mul' R A :=
  TensorProduct.ext (by ext; simp [mul'_apply])

private lemma comul_apply_mkₐ (a : A) :
    comul (R := R) (A := A ⧸ I) (Ideal.Quotient.mkₐ R I a) =
      TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap (comul a) :=
  LinearMap.congr_fun (IsBialgebraIdeal.comul_comp_mkₐ (R := R) I) a

private lemma counit_apply_mkₐ (a : A) :
    counit (R := R) (A := A ⧸ I) (Ideal.Quotient.mkₐ R I a) = counit a :=
  LinearMap.congr_fun (IsBialgebraIdeal.counit_comp_mkₐ (R := R) I) a

lemma antipode_rTensor_comp_map_mkₐ :
    (HopfAlgebraStruct.antipode (A := A ⧸ I) R).rTensor (A ⧸ I) ∘ₗ
      TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap =
    TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ
        (HopfAlgebra.antipode R).rTensor A := by
  rw [rTensor, rTensor, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    antipode_comp_mkₐ, id_comp, comp_id]

lemma antipode_lTensor_comp_map_mkₐ :
    (HopfAlgebraStruct.antipode (A := A ⧸ I) R).lTensor (A ⧸ I) ∘ₗ
      TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap =
    TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ
        (HopfAlgebra.antipode R).lTensor A := by
  rw [lTensor, lTensor, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    antipode_comp_mkₐ, id_comp, comp_id]

/-- The Hopf algebra structure on `A ⧸ I` when `I` is a Hopf ideal. -/
noncomputable instance : HopfAlgebra R (A ⧸ I) where
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective (R₁ := R) I x
    have hpush := LinearMap.congr_fun (antipode_rTensor_comp_map_mkₐ (R := R) I) (comul a)
    have hmul := LinearMap.congr_fun (mul'_comp_map_mkₐ I)
      ((HopfAlgebra.antipode R).rTensor A (comul a))
    simp only [coe_comp, Function.comp_apply] at *
    rw [comul_apply_mkₐ, hpush, hmul, HopfAlgebra.mul_antipode_rTensor_comul_apply,
      counit_apply_mkₐ]
    simp
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective (R₁ := R) I x
    have hpush := LinearMap.congr_fun (antipode_lTensor_comp_map_mkₐ (R := R) I) (comul a)
    have hmul := LinearMap.congr_fun (mul'_comp_map_mkₐ I)
      ((HopfAlgebra.antipode R).lTensor A (comul a))
    simp only [coe_comp, Function.comp_apply] at *
    rw [comul_apply_mkₐ, hpush, hmul, HopfAlgebra.mul_antipode_lTensor_comul_apply,
      counit_apply_mkₐ]
    simp

end IsHopfIdeal

end Ideal
