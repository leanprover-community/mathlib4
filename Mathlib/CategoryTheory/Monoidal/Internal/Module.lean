/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.internal.Module
! leanprover-community/mathlib commit 74403a3b2551b0970855e14ef5e8fd0d6af1bfc2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Monoidal.Basic
import Mathbin.Algebra.Category.Algebra.Basic
import Mathbin.CategoryTheory.Monoidal.Mon_

/-!
# `Mon_ (Module R) ≌ Algebra R`

The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.

Moreover, this equivalence is compatible with the forgetful functors to `Module R`.
-/


universe v u

open CategoryTheory

open LinearMap

open scoped TensorProduct

attribute [local ext] TensorProduct.ext

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace MonModuleEquivalenceAlgebra

@[simps]
instance (A : Mon_ (ModuleCat.{u} R)) : Ring A.pt :=
  {
    (by infer_instance : AddCommGroup
        A.pt) with
    one := A.one (1 : R)
    mul := fun x y => A.mul (x ⊗ₜ y)
    one_mul := fun x => by convert LinearMap.congr_fun A.one_mul ((1 : R) ⊗ₜ x); simp
    mul_one := fun x => by convert LinearMap.congr_fun A.mul_one (x ⊗ₜ (1 : R)); simp
    mul_assoc := fun x y z => by convert LinearMap.congr_fun A.mul_assoc (x ⊗ₜ y ⊗ₜ z)
    left_distrib := fun x y z =>
      by
      convert A.mul.map_add (x ⊗ₜ y) (x ⊗ₜ z)
      rw [← TensorProduct.tmul_add]
      rfl
    right_distrib := fun x y z =>
      by
      convert A.mul.map_add (x ⊗ₜ z) (y ⊗ₜ z)
      rw [← TensorProduct.add_tmul]
      rfl }

instance (A : Mon_ (ModuleCat.{u} R)) : Algebra R A.pt :=
  { A.one with
    map_zero' := A.one.map_zero
    map_one' := rfl
    map_mul' := fun x y =>
      by
      have h := LinearMap.congr_fun A.one_mul.symm (x ⊗ₜ A.one y)
      rwa [monoidal_category.left_unitor_hom_apply, ← A.one.map_smul] at h 
    commutes' := fun r a => by
      dsimp
      have h₁ := LinearMap.congr_fun A.one_mul (r ⊗ₜ a)
      have h₂ := LinearMap.congr_fun A.mul_one (a ⊗ₜ r)
      exact h₁.trans h₂.symm
    smul_def' := fun r a => (LinearMap.congr_fun A.one_mul (r ⊗ₜ a)).symm }

@[simp]
theorem algebraMap (A : Mon_ (ModuleCat.{u} R)) (r : R) : algebraMap R A.pt r = A.one r :=
  rfl
#align Module.Mon_Module_equivalence_Algebra.algebra_map ModuleCat.MonModuleEquivalenceAlgebra.algebraMap

/-- Converting a monoid object in `Module R` to a bundled algebra.
-/
@[simps]
def functor : Mon_ (ModuleCat.{u} R) ⥤ AlgebraCat R
    where
  obj A := AlgebraCat.of R A.pt
  map A B f :=
    { f.Hom.toAddMonoidHom with
      toFun := f.Hom
      map_one' := LinearMap.congr_fun f.OneHom (1 : R)
      map_mul' := fun x y => LinearMap.congr_fun f.MulHom (x ⊗ₜ y)
      commutes' := fun r => LinearMap.congr_fun f.OneHom r }
#align Module.Mon_Module_equivalence_Algebra.functor ModuleCat.MonModuleEquivalenceAlgebra.functor

/-- Converting a bundled algebra to a monoid object in `Module R`.
-/
@[simps]
def inverseObj (A : AlgebraCat.{u} R) : Mon_ (ModuleCat.{u} R)
    where
  pt := ModuleCat.of R A
  one := Algebra.linearMap R A
  mul := LinearMap.mul' R A
  one_mul' := by
    ext x
    dsimp only [AlgebraCat.id_apply, TensorProduct.mk_apply, Algebra.linearMap_apply,
      LinearMap.compr₂_apply, Function.comp_apply, RingHom.map_one,
      ModuleCat.MonoidalCategory.hom_apply, AlgebraCat.coe_comp,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
    rw [LinearMap.mul'_apply, monoidal_category.left_unitor_hom_apply, ← Algebra.smul_def]
  mul_one' := by
    ext x
    dsimp only [AlgebraCat.id_apply, TensorProduct.mk_apply, Algebra.linearMap_apply,
      LinearMap.compr₂_apply, Function.comp_apply, ModuleCat.MonoidalCategory.hom_apply,
      AlgebraCat.coe_comp]
    rw [LinearMap.mul'_apply, ModuleCat.MonoidalCategory.rightUnitor_hom_apply, ← Algebra.commutes,
      ← Algebra.smul_def]
  mul_assoc' := by
    ext x y z
    dsimp only [AlgebraCat.id_apply, TensorProduct.mk_apply, LinearMap.compr₂_apply,
      Function.comp_apply, ModuleCat.MonoidalCategory.hom_apply, AlgebraCat.coe_comp,
      monoidal_category.associator_hom_apply]
    simp only [LinearMap.mul'_apply, mul_assoc]
#align Module.Mon_Module_equivalence_Algebra.inverse_obj ModuleCat.MonModuleEquivalenceAlgebra.inverseObj

/-- Converting a bundled algebra to a monoid object in `Module R`.
-/
@[simps]
def inverse : AlgebraCat.{u} R ⥤ Mon_ (ModuleCat.{u} R)
    where
  obj := inverseObj
  map A B f :=
    { Hom := f.toLinearMap
      one_hom' := LinearMap.ext f.commutes
      mul_hom' := TensorProduct.ext <| LinearMap.ext₂ <| map_mul f }
#align Module.Mon_Module_equivalence_Algebra.inverse ModuleCat.MonModuleEquivalenceAlgebra.inverse

end MonModuleEquivalenceAlgebra

open MonModuleEquivalenceAlgebra

/-- The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.
-/
def monModuleEquivalenceAlgebra : Mon_ (ModuleCat.{u} R) ≌ AlgebraCat R
    where
  Functor := Functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { Hom :=
            { Hom :=
                { toFun := id
                  map_add' := fun x y => rfl
                  map_smul' := fun r a => rfl }
              mul_hom' := by ext; dsimp at *; rfl }
          inv :=
            { Hom :=
                { toFun := id
                  map_add' := fun x y => rfl
                  map_smul' := fun r a => rfl }
              mul_hom' := by ext; dsimp at *; rfl } })
      (by tidy)
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { Hom :=
            { toFun := id
              map_zero' := rfl
              map_add' := fun x y => rfl
              map_one' := (algebraMap R A).map_one
              map_mul' := fun x y => @LinearMap.mul'_apply R _ _ _ _ _ _ x y
              commutes' := fun r => rfl }
          inv :=
            { toFun := id
              map_zero' := rfl
              map_add' := fun x y => rfl
              map_one' := (algebraMap R A).map_one.symm
              map_mul' := fun x y => (@LinearMap.mul'_apply R _ _ _ _ _ _ x y).symm
              commutes' := fun r => rfl } })
      (by intros; rfl)
#align Module.Mon_Module_equivalence_Algebra ModuleCat.monModuleEquivalenceAlgebra

/-- The equivalence `Mon_ (Module R) ≌ Algebra R`
is naturally compatible with the forgetful functors to `Module R`.
-/
def monModuleEquivalenceAlgebraForget :
    MonModuleEquivalenceAlgebra.functor ⋙ forget₂ (AlgebraCat.{u} R) (ModuleCat.{u} R) ≅
      Mon_.forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun A =>
      { Hom :=
          { toFun := id
            map_add' := fun x y => rfl
            map_smul' := fun c x => rfl }
        inv :=
          { toFun := id
            map_add' := fun x y => rfl
            map_smul' := fun c x => rfl } })
    (by tidy)
#align Module.Mon_Module_equivalence_Algebra_forget ModuleCat.monModuleEquivalenceAlgebraForget

end ModuleCat

