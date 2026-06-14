/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
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
* `Bialgebra.Quotient.mkBialgHom` : `Ideal.Quotient.mkₐ` as a bialgebra homomorphism.

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
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A)
    (Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars R))

/-- The comultiplication on `A ⧸ I`, as an `R`-algebra homomorphism. -/
def comulAlgHom : (A ⧸ I) →ₐ[R] (A ⧸ I) ⊗[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R A))
    (Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars R))

lemma counit_comp_mkₐ :
    (counitAlgHom I).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap = counit := rfl

lemma comul_comp_mkₐ :
    (comulAlgHom (R := R) I).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ comul := rfl

/-- The bialgebra structure on `A ⧸ I` when `I` is a biideal. -/
instance : Bialgebra R (A ⧸ I) := by
  refine .ofAlgHom (comulAlgHom I) (counitAlgHom I) ?_ ?_ ?_ <;>
    refine Ideal.Quotient.algHom_ext R (AlgHom.toLinearMap_injective ?_) <;>
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comul_comp_mkₐ, counit_comp_mkₐ]
  · simp [coassoc_simps]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

@[simp] lemma counit_mk (a : A) :
    counit (R := R) (Ideal.Quotient.mk I a) = counit a := rfl

@[simp] lemma comul_mk (a : A) :
    comul (R := R) (Ideal.Quotient.mk I a) =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap (comul a) :=
  rfl

/-- `Ideal.Quotient.mkₐ` as a bialgebra homomorphism. -/
def mkBialgHom : A →ₐc[R] A ⧸ I := .ofAlgHom (Ideal.Quotient.mkₐ R I) rfl rfl

@[simp] lemma mkBialgHom_apply (a : A) :
    mkBialgHom (R := R) I a = Ideal.Quotient.mk I a := rfl

end Bialgebra.Quotient
