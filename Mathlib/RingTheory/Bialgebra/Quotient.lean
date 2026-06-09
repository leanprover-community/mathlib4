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
# Bialgebra structure on quotients by biideals

A *biideal* of an `R`-bialgebra `A` is a two-sided ideal whose underlying `R`-submodule is a
coideal. We express this with the existing mixins `I.IsTwoSided` and
`IsCoideal (I.restrictScalars R)` rather than a new class, and show that the quotient `A ⧸ I`
inherits a bialgebra structure.

We work over a `CommRing`/`Ring` rather than semirings since quotients by ideals require
additive inverses.

## Main results

* `Bialgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[IsCoideal (I.restrictScalars R)]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
variable (I : Ideal A) [I.IsTwoSided] [IsCoideal (I.restrictScalars R)]

namespace Bialgebra.Quotient

/-- The counit on `A ⧸ I`, as an `R`-algebra homomorphism. -/
noncomputable def counitAlgHom : (A ⧸ I) →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A) fun _ ha =>
    IsCoideal.counit_eq_zero (I := I.restrictScalars R) ha

/-- The comultiplication on `A ⧸ I`, as an `R`-algebra homomorphism. -/
noncomputable def comulAlgHom : (A ⧸ I) →ₐ[R] (A ⧸ I) ⊗[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R A)) fun a ha => by
    have key : (Ideal.Quotient.mkₐ R I).toLinearMap =
        (Submodule.Quotient.restrictScalarsEquiv R I).toLinearMap ∘ₗ
          (I.restrictScalars R).mkQ := rfl
    have h0 : map (I.restrictScalars R).mkQ (I.restrictScalars R).mkQ (comul a) = 0 :=
      IsCoideal.comul_eq_zero ha
    change map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap
      (comul a) = 0
    rw [key, TensorProduct.map_comp, LinearMap.comp_apply, h0, _root_.map_zero]

lemma counit_comp_mkₐ : (counitAlgHom I).toLinearMap.comp (Ideal.Quotient.mkₐ R I).toLinearMap =
    (counit : A →ₗ[R] R) := by ext a; simp [counitAlgHom]

lemma comul_comp_mkₐ :
    (comulAlgHom (R := R) I).toLinearMap.comp (Ideal.Quotient.mkₐ R I).toLinearMap =
      (map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap).comp
        comul := by
  ext a; simp [comulAlgHom]; rfl

/-- The bialgebra structure on `A ⧸ I` when `I` is a biideal. -/
noncomputable instance : Bialgebra R (A ⧸ I) := by
  refine Bialgebra.ofAlgHom (comulAlgHom I) (counitAlgHom I) ?_ ?_ ?_ <;>
    refine Ideal.Quotient.algHom_ext R (AlgHom.toLinearMap_injective ?_)
  · simp [coassoc_simps, comul_comp_mkₐ]
  all_goals simp only [coassoc_simps, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map, comul_comp_mkₐ, counit_comp_mkₐ]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

@[simp] lemma counit_mk (a : A) :
    (counit : (A ⧸ I) →ₗ[R] R) (Ideal.Quotient.mk I a) = counit a :=
  LinearMap.congr_fun (counit_comp_mkₐ I) a

@[simp] lemma comul_mk (a : A) :
    (comul : (A ⧸ I) →ₗ[R] _) (Ideal.Quotient.mk I a) =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap (comul a) :=
  LinearMap.congr_fun (comul_comp_mkₐ I) a

end Bialgebra.Quotient
