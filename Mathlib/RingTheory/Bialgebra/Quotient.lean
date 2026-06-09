/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on quotients

If `I` is a two-sided ideal of an `R`-bialgebra `A` whose underlying `R`-submodule is a
coideal, then the quotient `A ⧸ I` inherits a bialgebra structure.

## Main definitions

* `Bialgebra.Quotient.counitAlgHom` : the counit on `A ⧸ I`, as an `R`-algebra homomorphism.
* `Bialgebra.Quotient.comulAlgHom` : comultiplication on `A ⧸ I` as an `R`-algebra homomorphism.

## Main results

* `Bialgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[(I.restrictScalars R).IsCoideal]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
variable (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]

namespace Bialgebra.Quotient

/-- The counit on `A ⧸ I`, as an `R`-algebra homomorphism. -/
def counitAlgHom : (A ⧸ I) →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A) fun _ ha =>
    Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars R) ha

/-- The comultiplication on `A ⧸ I`, as an `R`-algebra homomorphism. -/
def comulAlgHom : (A ⧸ I) →ₐ[R] (A ⧸ I) ⊗[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R A)) fun a ha => by
    change map ((Submodule.Quotient.restrictScalarsEquiv R I).toLinearMap ∘ₗ
        (I.restrictScalars R).mkQ)
      ((Submodule.Quotient.restrictScalarsEquiv R I).toLinearMap ∘ₗ
        (I.restrictScalars R).mkQ) (comul a) = 0
    rw [TensorProduct.map_comp, comp_apply,
      Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars R) ha, _root_.map_zero]

lemma counit_comp_mkₐ : (counitAlgHom I).toLinearMap.comp (Ideal.Quotient.mkₐ R I).toLinearMap =
    (counit : A →ₗ[R] R) :=
  congrArg AlgHom.toLinearMap (Ideal.Quotient.liftₐ_comp I _ _)

lemma comul_comp_mkₐ :
    (comulAlgHom (R := R) I).toLinearMap.comp (Ideal.Quotient.mkₐ R I).toLinearMap =
      (map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap).comp
        comul :=
  congrArg AlgHom.toLinearMap (Ideal.Quotient.liftₐ_comp I _ _)

/-- The bialgebra structure on `A ⧸ I` when `I` is a biideal. -/
instance : Bialgebra R (A ⧸ I) := by
  refine Bialgebra.ofAlgHom (comulAlgHom I) (counitAlgHom I) ?_ ?_ ?_ <;>
    refine Ideal.Quotient.algHom_ext R (AlgHom.toLinearMap_injective ?_)
  · simp [coassoc_simps, comul_comp_mkₐ]
  · simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comul_comp_mkₐ, counit_comp_mkₐ]
    rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comul_comp_mkₐ, counit_comp_mkₐ]
    rw [CoassocSimps.map_counit_comp_comul_right]; rfl

@[simp] lemma counit_mk (a : A) :
    (counit : (A ⧸ I) →ₗ[R] R) (Ideal.Quotient.mk I a) = counit a :=
  LinearMap.congr_fun (counit_comp_mkₐ I) a

@[simp] lemma comul_mk (a : A) :
    (comul : (A ⧸ I) →ₗ[R] _) (Ideal.Quotient.mk I a) =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap (comul a) :=
  LinearMap.congr_fun (comul_comp_mkₐ I) a

end Bialgebra.Quotient
