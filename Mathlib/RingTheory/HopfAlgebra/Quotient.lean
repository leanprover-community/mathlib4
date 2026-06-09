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
of `A` by a two-sided Hopf ideal inherits a Hopf algebra structure: the antipode descends
through the module quotient, with no need to pass through the opposite algebra.

## Main definitions

* `Ideal.IsHopfIdeal R I` — `I` is a coideal (as an `R`-submodule) stable under the antipode.

## Main results

* `HopfAlgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[I.IsHopfIdeal R]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [HopfAlgebra R A]

variable (R) in
/-- An ideal of an `R`-Hopf algebra is a *Hopf ideal* if its underlying `R`-submodule is a
coideal and it is stable under the antipode. -/
class Ideal.IsHopfIdeal (I : Ideal A) : Prop extends IsCoideal (I.restrictScalars R) where
  antipode_mem : ∀ ⦃x : A⦄, x ∈ I → HopfAlgebra.antipode R x ∈ I

namespace HopfAlgebra.Quotient

variable (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]

noncomputable instance : HopfAlgebraStruct R (A ⧸ I) where
  antipode := (Submodule.Quotient.restrictScalarsEquiv R I).toLinearMap ∘ₗ
    Submodule.mapQ (I.restrictScalars R) (I.restrictScalars R) (HopfAlgebra.antipode R)
      (fun _ hx => Ideal.IsHopfIdeal.antipode_mem (R := R) hx) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R I).symm.toLinearMap

@[simp]
lemma antipode_mk (a : A) :
    HopfAlgebra.antipode R (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I (HopfAlgebra.antipode R a) :=
  rfl

@[simp]
lemma antipode_comp_mkₐ :
    (HopfAlgebra.antipode R).comp (Ideal.Quotient.mkₐ R I).toLinearMap =
      (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ HopfAlgebra.antipode R := by ext; simp

noncomputable instance : HopfAlgebra R (A ⧸ I) where
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    convert! congr(Ideal.Quotient.mk I $(mul_antipode_rTensor_comul_apply (R := R) a)) using 1
    simp only [coe_comp, Function.comp_apply, Bialgebra.Quotient.comul_mk,
      rTensor_map, antipode_comp_mkₐ, ← map_rTensor]
    exact (LinearMap.congr_fun (AlgHom.comp_mul' (Ideal.Quotient.mkₐ R I)) _).symm
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    convert! congr(Ideal.Quotient.mk I $(mul_antipode_lTensor_comul_apply (R := R) a)) using 1
    simp only [coe_comp, Function.comp_apply, Bialgebra.Quotient.comul_mk,
      lTensor_map, antipode_comp_mkₐ, ← map_lTensor]
    exact (LinearMap.congr_fun (AlgHom.comp_mul' (Ideal.Quotient.mkₐ R I)) _).symm

end HopfAlgebra.Quotient
