/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.RingQuot
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on quotients

The quotient of an `R`-bialgebra `A` by a two-sided ideal `I` inherits the bialgebra
structure exactly when `I` is a *bialgebra ideal*: the counit vanishes on `I` and the
comultiplication descends through `A ⧸ I ⊗[R] A ⧸ I`. The same descent condition can
be stated on a generating relation `r`, yielding a bialgebra structure on `RingQuot r`.

## Main definitions

* `IsBialgebraRel R r` — descent condition on a generating relation.
* `IsBialgebraIdeal R I` — descent condition on a two-sided ideal of `A`.

## Main results

* `Bialgebra R (RingQuot r)` instance from `[IsBialgebraRel R r]`.
* `Bialgebra R (A ⧸ I)` instance from `[IsBialgebraIdeal R I]`.
* `IsBialgebraIdeal R I` produces `Coalgebra.IsCoideal (I.restrictScalars R)`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap RingQuot TensorProduct
open scoped RingTheory.LinearMap

/-! ### Bialgebra structure on `RingQuot r` -/

section RingQuot

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (R) in
/-- A relation `r` on an `R`-bialgebra `A` is a *bialgebra relation* if the counit identifies
related elements and the comultiplication agrees on related elements after projection to
`RingQuot r ⊗[R] RingQuot r`. -/
@[mk_iff]
class IsBialgebraRel (r : A → A → Prop) : Prop where
  counit_rel : ∀ ⦃x y : A⦄, r x y → (counit x : R) = counit y
  comul_rel : ∀ ⦃x y : A⦄, r x y →
    (((mkAlgHom R r).toLinearMap ⊗ₘ (mkAlgHom R r).toLinearMap) ∘ₗ comul) x =
      (((mkAlgHom R r).toLinearMap ⊗ₘ (mkAlgHom R r).toLinearMap) ∘ₗ comul) y

namespace Bialgebra.Quotient

variable (r : A → A → Prop) [IsBialgebraRel R r]

/-- The counit on `RingQuot r`, packaged as an algebra homomorphism. -/
noncomputable def counitAlgHomRingQuot : RingQuot r →ₐ[R] R :=
  liftAlgHom R ⟨counitAlgHom R A,
    fun _ _ h => IsBialgebraRel.counit_rel (R := R) h⟩

/-- The comultiplication on `RingQuot r`, packaged as an algebra homomorphism. -/
noncomputable def comulAlgHomRingQuot : RingQuot r →ₐ[R] RingQuot r ⊗[R] RingQuot r :=
  liftAlgHom R ⟨
    (Algebra.TensorProduct.map (mkAlgHom R r) (mkAlgHom R r)).comp
      (comulAlgHom R A),
    fun _ _ h => by
      simpa only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        AlgebraTensorModule.map_eq, toLinearMap_comulAlgHom, coe_comp,
        Function.comp_apply] using IsBialgebraRel.comul_rel h⟩

@[simp]
lemma counitAlgHomRingQuot_mkAlgHom (a : A) :
    counitAlgHomRingQuot r (mkAlgHom R r a) = counitAlgHom R A a := by
  simp [counitAlgHomRingQuot]

@[simp]
lemma comulAlgHomRingQuot_mkAlgHom (a : A) :
    comulAlgHomRingQuot r (mkAlgHom R r a) =
      Algebra.TensorProduct.map (mkAlgHom R r) (mkAlgHom R r)
        (comulAlgHom R A a) := by
  simp [comulAlgHomRingQuot]

lemma counit_comp_mkAlgHom :
    (counitAlgHomRingQuot r).toLinearMap.comp (mkAlgHom R r).toLinearMap =
      (counit : A →ₗ[R] R) := by
  ext a; simp

lemma comul_comp_mkAlgHom :
    ((comulAlgHomRingQuot r).toLinearMap :
        RingQuot r →ₗ[R] RingQuot r ⊗[R] RingQuot r).comp
        (mkAlgHom R r).toLinearMap =
      (map (mkAlgHom R r).toLinearMap (mkAlgHom R r).toLinearMap).comp comul := by
  ext a
  simp only [coe_comp, AlgHom.toLinearMap_apply, Function.comp_apply,
    comulAlgHomRingQuot_mkAlgHom]
  rw [show ((Algebra.TensorProduct.map (mkAlgHom R r) (mkAlgHom R r))
        ((comulAlgHom R A) a) : RingQuot r ⊗[R] RingQuot r) =
      ((Algebra.TensorProduct.map (mkAlgHom R r) (mkAlgHom R r)).toLinearMap
        ((comulAlgHom R A).toLinearMap a)) from rfl,
    toLinearMap_comulAlgHom, Algebra.TensorProduct.toLinearMap_map]
  simp [AlgebraTensorModule.map_eq]

/-- The bialgebra structure on `RingQuot r` when `r` is a bialgebra relation. -/
noncomputable instance : Bialgebra R (RingQuot r) :=
  Bialgebra.ofAlgHom (comulAlgHomRingQuot r) (counitAlgHomRingQuot r)
    (by
      refine ringQuot_ext' _ _ _ ?_
      apply AlgHom.toLinearMap_injective
      simp [coassoc_simps, comul_comp_mkAlgHom])
    (by
      refine ringQuot_ext' _ _ _ ?_
      apply AlgHom.toLinearMap_injective
      simp only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        AlgHom.toLinearMap_id, AlgebraTensorModule.map_eq, AlgEquiv.toAlgHom_toLinearMap,
        AlgEquiv.toLinearEquiv_symm, Algebra.TensorProduct.lid_toLinearEquiv, ← rTensor_def]
      rw [comp_assoc, comul_comp_mkAlgHom, ← comp_assoc, rTensor_comp_map,
        counit_comp_mkAlgHom, ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul,
        lTensor_comp_mk]
      rfl)
    (by
      refine ringQuot_ext' _ _ _ ?_
      apply AlgHom.toLinearMap_injective
      simp only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        AlgHom.toLinearMap_id, AlgebraTensorModule.map_eq, AlgEquiv.toAlgHom_toLinearMap,
        AlgEquiv.toLinearEquiv_symm, Algebra.TensorProduct.rid_toLinearEquiv,
        AlgebraTensorModule.rid_eq_rid, ← lTensor_def]
      rw [comp_assoc, comul_comp_mkAlgHom, ← comp_assoc, lTensor_comp_map,
        counit_comp_mkAlgHom, ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul,
        rTensor_comp_flip_mk]
      rfl)

end Bialgebra.Quotient

end RingQuot

/-! ### Bialgebra structure on the quotient by a bialgebra ideal -/

section Ideal

variable {R A : Type*} [CommRing R] [Ring A] [Bialgebra R A]

variable (R) in
/-- A two-sided ideal `I` of an `R`-bialgebra `A` is a *bialgebra ideal* if the counit vanishes
on `I` and the comultiplication descends through the module quotient `A ⧸ I`. -/
@[mk_iff]
class IsBialgebraIdeal (I : Ideal A) : Prop extends I.IsTwoSided where
  counit_eq_zero : ∀ ⦃x : A⦄, x ∈ I → counit x = (0 : R)
  comul_eq_zero : ∀ ⦃x : A⦄, x ∈ I →
    ((I.restrictScalars R).mkQ ⊗ₘ (I.restrictScalars R).mkQ) (comul x) = 0

namespace IsBialgebraIdeal

variable (I : Ideal A) [IsBialgebraIdeal R I]

/-- The underlying coideal of a bialgebra ideal. -/
theorem isCoideal : IsCoideal (I.restrictScalars R) where
  counit_eq_zero := IsBialgebraIdeal.counit_eq_zero
  comul_eq_zero := IsBialgebraIdeal.comul_eq_zero

/-- The counit on `A ⧸ I`, packaged as an algebra homomorphism. -/
noncomputable def counitAlgHom : (A ⧸ I) →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A)
    fun _ ha => IsBialgebraIdeal.counit_eq_zero ha

/-- The comultiplication on `A ⧸ I`, packaged as an algebra homomorphism. -/
noncomputable def comulAlgHom : (A ⧸ I) →ₐ[R] (A ⧸ I) ⊗[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R A))
    fun _ ha => by
      simpa only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        AlgebraTensorModule.map_eq, toLinearMap_comulAlgHom, coe_comp,
        Function.comp_apply] using IsBialgebraIdeal.comul_eq_zero ha

lemma counit_comp_mkₐ :
    (counitAlgHom I).toLinearMap.comp (Ideal.Quotient.mkₐ R I).toLinearMap =
      (counit : A →ₗ[R] R) := rfl

lemma comul_comp_mkₐ :
    ((comulAlgHom I).toLinearMap : (A ⧸ I) →ₗ[R] (A ⧸ I) ⊗[R] (A ⧸ I)).comp
        (Ideal.Quotient.mkₐ R I).toLinearMap =
      (map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap).comp comul := rfl

/-- The bialgebra structure on `A ⧸ I` when `I` is a bialgebra ideal. -/
noncomputable instance : Bialgebra R (A ⧸ I) :=
  Bialgebra.ofAlgHom (comulAlgHom I) (counitAlgHom I)
    (by
      refine Ideal.Quotient.algHom_ext _ ?_
      apply AlgHom.toLinearMap_injective
      simp [coassoc_simps, comul_comp_mkₐ])
    (by
      refine Ideal.Quotient.algHom_ext _ ?_
      apply AlgHom.toLinearMap_injective
      simp only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        AlgHom.toLinearMap_id, AlgebraTensorModule.map_eq, AlgEquiv.toAlgHom_toLinearMap,
        AlgEquiv.toLinearEquiv_symm, Algebra.TensorProduct.lid_toLinearEquiv, ← rTensor_def]
      rw [comp_assoc, comul_comp_mkₐ, ← comp_assoc, rTensor_comp_map, counit_comp_mkₐ,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
      rfl)
    (by
      refine Ideal.Quotient.algHom_ext _ ?_
      apply AlgHom.toLinearMap_injective
      simp only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        AlgHom.toLinearMap_id, AlgebraTensorModule.map_eq, AlgEquiv.toAlgHom_toLinearMap,
        AlgEquiv.toLinearEquiv_symm, Algebra.TensorProduct.rid_toLinearEquiv,
        AlgebraTensorModule.rid_eq_rid, ← lTensor_def]
      rw [comp_assoc, comul_comp_mkₐ, ← comp_assoc, lTensor_comp_map, counit_comp_mkₐ,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
      rfl)

end IsBialgebraIdeal

end Ideal
