/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.RingQuot
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.Quotient
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on `RingQuot`

A relation `r : A → A → Prop` on an `R`-bialgebra `A` is a *bialgebra relation* when
the counit identifies related elements and the comultiplication agrees on related elements
after projection to `RingQuot r ⊗[R] RingQuot r`. The quotient `RingQuot r` then inherits
a bialgebra structure.

## Main definitions

* `IsBialgebraRel R r` — descent condition on a generating relation.

## Main results

* `Bialgebra R (RingQuot r)` instance from `[IsBialgebraRel R r]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap RingQuot TensorProduct

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (R) in
/-- A relation `r` on an `R`-bialgebra `A` is a *bialgebra relation* if the counit identifies
related elements and the comultiplication agrees on related elements after projection to
`RingQuot r ⊗[R] RingQuot r`. -/
@[mk_iff]
class IsBialgebraRel (r : A → A → Prop) : Prop where
  counit_rel : ∀ ⦃x y : A⦄, r x y → (counit x : R) = counit y
  comul_rel : ∀ ⦃x y : A⦄, r x y →
    Algebra.TensorProduct.map (mkAlgHom R r) (mkAlgHom R r) (comul x) =
      Algebra.TensorProduct.map (mkAlgHom R r) (mkAlgHom R r) (comul y)

namespace Bialgebra.Quotient

variable (r : A → A → Prop) [IsBialgebraRel R r]

/-- The counit on `RingQuot r`, as an `R`-algebra homomorphism. -/
noncomputable def counitAlgHom : RingQuot r →ₐ[R] R :=
  liftAlgHom R ⟨Bialgebra.counitAlgHom R A, IsBialgebraRel.counit_rel⟩

/-- The comultiplication on `RingQuot r`, as an `R`-algebra homomorphism. -/
noncomputable def comulAlgHom : RingQuot r →ₐ[R] RingQuot r ⊗[R] RingQuot r :=
  liftAlgHom R ⟨
    (Algebra.TensorProduct.map (mkAlgHom R r) (mkAlgHom R r)).comp (Bialgebra.comulAlgHom R A),
    IsBialgebraRel.comul_rel⟩

lemma counit_comp_mkAlgHom : (counitAlgHom r).toLinearMap.comp (mkAlgHom R r).toLinearMap =
    (counit : A →ₗ[R] R) := by ext a; simp [counitAlgHom]

lemma comul_comp_mkAlgHom : (comulAlgHom r).toLinearMap.comp (mkAlgHom R r).toLinearMap =
    (map (mkAlgHom R r).toLinearMap (mkAlgHom R r).toLinearMap).comp comul := by
  ext a
  simp only [comulAlgHom, coe_comp, AlgHom.toLinearMap_apply, Function.comp_apply,
    liftAlgHom_mkAlgHom_apply, AlgHom.coe_comp]
  rfl

/-- The bialgebra structure on `RingQuot r` when `r` is a bialgebra relation. -/
noncomputable instance : Bialgebra R (RingQuot r) :=
  Bialgebra.ofAlgHom (comulAlgHom r) (counitAlgHom r)
    (by
      refine ringQuot_ext' _ _ _ (AlgHom.toLinearMap_injective ?_)
      simp [coassoc_simps, comul_comp_mkAlgHom])
    (by
      refine ringQuot_ext' _ _ _ (AlgHom.toLinearMap_injective ?_)
      simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        AlgebraTensorModule.map_eq, comul_comp_mkAlgHom, counit_comp_mkAlgHom]
      rw [CoassocSimps.map_counit_comp_comul_left]; rfl)
    (by
      refine ringQuot_ext' _ _ _ (AlgHom.toLinearMap_injective ?_)
      simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        AlgebraTensorModule.map_eq, comul_comp_mkAlgHom, counit_comp_mkAlgHom]
      rw [CoassocSimps.map_counit_comp_comul_right]; rfl)

@[simp] lemma counit_mkAlgHom (a : A) :
    (counit : RingQuot r →ₗ[R] R) (mkAlgHom R r a) = counit a :=
  LinearMap.congr_fun (counit_comp_mkAlgHom r) a

@[simp] lemma comul_mkAlgHom (a : A) :
    (comul : RingQuot r →ₗ[R] _) (mkAlgHom R r a) =
      map (mkAlgHom R r).toLinearMap (mkAlgHom R r).toLinearMap (comul a) :=
  LinearMap.congr_fun (comul_comp_mkAlgHom r) a

end Bialgebra.Quotient
