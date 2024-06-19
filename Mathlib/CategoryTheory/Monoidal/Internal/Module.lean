/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

#align_import category_theory.monoidal.internal.Module from "leanprover-community/mathlib"@"74403a3b2551b0970855e14ef5e8fd0d6af1bfc2"

/-!
# `Mon_ (ModuleCat R) ≌ AlgebraCat R`

The category of internal monoid objects in `ModuleCat R`
is equivalent to the category of "native" bundled `R`-algebras.

Moreover, this equivalence is compatible with the forgetful functors to `ModuleCat R`.
-/

suppress_compilation

set_option linter.uppercaseLean3 false

universe v u

open CategoryTheory

open LinearMap

open scoped TensorProduct

attribute [local ext] TensorProduct.ext

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace MonModuleEquivalenceAlgebra

-- Porting note: in the following proof `have := ...; convert this` is to help Lean infer what the
-- underlying rings are.
-- Porting note: `simps(!)` doesn't work, I guess we will see what `simp` lemmas are needed and
-- add them manually
-- @[simps!]
instance Ring_of_Mon_ (A : Mon_ (ModuleCat.{u} R)) : Ring A.X :=
  { (inferInstance : AddCommGroup A.X) with
    one := A.one (1 : R)
    mul := fun x y => A.mul (x ⊗ₜ y)
    one_mul := fun x => by
      have := LinearMap.congr_fun A.one_mul ((1 : R) ⊗ₜ x)
      convert this
      rw [MonoidalCategory.leftUnitor_hom_apply, one_smul]
    mul_one := fun x => by
      have := LinearMap.congr_fun A.mul_one (x ⊗ₜ (1 : R))
      convert this
      erw [MonoidalCategory.leftUnitor_hom_apply, one_smul]
    mul_assoc := fun x y z => by
      have := LinearMap.congr_fun A.mul_assoc (x ⊗ₜ y ⊗ₜ z)
      convert this
    left_distrib := fun x y z => by
      have := A.mul.map_add (x ⊗ₜ y) (x ⊗ₜ z)
      convert this
      rw [← TensorProduct.tmul_add]
      rfl
    right_distrib := fun x y z => by
      have := A.mul.map_add (x ⊗ₜ z) (y ⊗ₜ z)
      convert this
      rw [← TensorProduct.add_tmul]
      rfl
    zero_mul := fun x => show A.mul _ = 0 by
      rw [TensorProduct.zero_tmul, map_zero]
    mul_zero := fun x => show A.mul _ = 0 by
      rw [TensorProduct.tmul_zero, map_zero] }

instance Algebra_of_Mon_ (A : Mon_ (ModuleCat.{u} R)) : Algebra R A.X :=
  { A.one with
    map_zero' := A.one.map_zero
    map_one' := rfl
    map_mul' := fun x y => by
      have h := LinearMap.congr_fun A.one_mul.symm (x ⊗ₜ A.one y)
      rwa [MonoidalCategory.leftUnitor_hom_apply, ← A.one.map_smul] at h
    commutes' := fun r a => by
      dsimp
      have h₁ := LinearMap.congr_fun A.one_mul (r ⊗ₜ a)
      have h₂ := LinearMap.congr_fun A.mul_one (a ⊗ₜ r)
      exact h₁.trans h₂.symm
    smul_def' := fun r a => (LinearMap.congr_fun A.one_mul (r ⊗ₜ a)).symm }

@[simp]
theorem algebraMap (A : Mon_ (ModuleCat.{u} R)) (r : R) : algebraMap R A.X r = A.one r :=
  rfl
#align Module.Mon_Module_equivalence_Algebra.algebra_map ModuleCat.MonModuleEquivalenceAlgebra.algebraMap

/-- Converting a monoid object in `ModuleCat R` to a bundled algebra.
-/
@[simps!]
def functor : Mon_ (ModuleCat.{u} R) ⥤ AlgebraCat R where
  obj A := AlgebraCat.of R A.X
  map {A B} f :=
    { f.hom.toAddMonoidHom with
      toFun := f.hom
      map_one' := LinearMap.congr_fun f.one_hom (1 : R)
      map_mul' := fun x y => LinearMap.congr_fun f.mul_hom (x ⊗ₜ y)
      commutes' := fun r => LinearMap.congr_fun f.one_hom r }
#align Module.Mon_Module_equivalence_Algebra.functor ModuleCat.MonModuleEquivalenceAlgebra.functor

/-- Converting a bundled algebra to a monoid object in `ModuleCat R`.
-/
@[simps]
def inverseObj (A : AlgebraCat.{u} R) : Mon_ (ModuleCat.{u} R) where
  X := ModuleCat.of R A
  one := Algebra.linearMap R A
  mul := LinearMap.mul' R A
  one_mul := by
    -- Porting note: `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| LinearMap.ext_ring <| LinearMap.ext fun x => ?_
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [compr₂_apply, compr₂_apply, CategoryTheory.comp_apply]
    -- Porting note: this `dsimp` does nothing
    -- dsimp [AlgebraCat.id_apply, TensorProduct.mk_apply, Algebra.linearMap_apply,
    --   LinearMap.compr₂_apply, Function.comp_apply, RingHom.map_one,
    --   ModuleCat.MonoidalCategory.hom_apply, AlgebraCat.coe_comp,
    --   ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
    -- Porting note: because `dsimp` is not effective, `rw` needs to be changed to `erw`
    erw [LinearMap.mul'_apply, MonoidalCategory.leftUnitor_hom_apply, ← Algebra.smul_def]
    erw [id_apply]
  mul_one := by
    -- Porting note: `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| LinearMap.ext fun x => LinearMap.ext_ring ?_
    -- Porting note: this `dsimp` does nothing
    -- dsimp only [AlgebraCat.id_apply, TensorProduct.mk_apply, Algebra.linearMap_apply,
    --   LinearMap.compr₂_apply, Function.comp_apply, ModuleCat.MonoidalCategory.hom_apply,
    --   AlgebraCat.coe_comp]
    -- Porting note: because `dsimp` is not effective, `rw` needs to be changed to `erw`
    erw [compr₂_apply, compr₂_apply]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [CategoryTheory.comp_apply]
    erw [LinearMap.mul'_apply, ModuleCat.MonoidalCategory.rightUnitor_hom_apply, ← Algebra.commutes,
      ← Algebra.smul_def]
    erw [id_apply]
  mul_assoc := by
    set_option tactic.skipAssignedInstances false in
    -- Porting note: `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext fun x => LinearMap.ext fun y =>
      LinearMap.ext fun z => ?_
    dsimp only [AlgebraCat.id_apply, TensorProduct.mk_apply, LinearMap.compr₂_apply,
      Function.comp_apply, ModuleCat.MonoidalCategory.hom_apply, AlgebraCat.coe_comp,
      MonoidalCategory.associator_hom_apply]
    rw [compr₂_apply, compr₂_apply]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, CategoryTheory.comp_apply]
    erw [LinearMap.mul'_apply, LinearMap.mul'_apply]
    erw [id_apply]
    erw [TensorProduct.mk_apply, TensorProduct.mk_apply, mul'_apply, LinearMap.id_apply, mul'_apply]
    simp only [LinearMap.mul'_apply, mul_assoc]
#align Module.Mon_Module_equivalence_Algebra.inverse_obj ModuleCat.MonModuleEquivalenceAlgebra.inverseObj

/-- Converting a bundled algebra to a monoid object in `ModuleCat R`.
-/
@[simps]
def inverse : AlgebraCat.{u} R ⥤ Mon_ (ModuleCat.{u} R) where
  obj := inverseObj
  map f :=
    { hom := f.toLinearMap
      one_hom := LinearMap.ext f.commutes
      mul_hom := TensorProduct.ext <| LinearMap.ext₂ <| f.map_mul }
#align Module.Mon_Module_equivalence_Algebra.inverse ModuleCat.MonModuleEquivalenceAlgebra.inverse

end MonModuleEquivalenceAlgebra

open MonModuleEquivalenceAlgebra

set_option maxHeartbeats 500000 in
/-- The category of internal monoid objects in `ModuleCat R`
is equivalent to the category of "native" bundled `R`-algebras.
-/
def monModuleEquivalenceAlgebra : Mon_ (ModuleCat.{u} R) ≌ AlgebraCat R where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { hom :=
                { toFun := _root_.id
                  map_add' := fun x y => rfl
                  map_smul' := fun r a => rfl }
              mul_hom := by
                -- Porting note: `ext` did not pick up `TensorProduct.ext`
                refine TensorProduct.ext ?_
                dsimp at *
                rfl }
          inv :=
            { hom :=
                { toFun := _root_.id
                  map_add' := fun x y => rfl
                  map_smul' := fun r a => rfl }
              mul_hom := by
                -- Porting note: `ext` did not pick up `TensorProduct.ext`
                refine TensorProduct.ext ?_
                dsimp at *
                rfl } })
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { toFun := _root_.id
              map_zero' := rfl
              map_add' := fun x y => rfl
              map_one' := (algebraMap R A).map_one
              map_mul' := fun x y => @LinearMap.mul'_apply R _ _ _ _ _ _ x y
              commutes' := fun r => rfl }
          inv :=
            { toFun := _root_.id
              map_zero' := rfl
              map_add' := fun x y => rfl
              map_one' := (algebraMap R A).map_one.symm
              map_mul' := fun x y => (@LinearMap.mul'_apply R _ _ _ _ _ _ x y).symm
              commutes' := fun r => rfl } })
#align Module.Mon_Module_equivalence_Algebra ModuleCat.monModuleEquivalenceAlgebra

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] ModuleCat.MonModuleEquivalenceAlgebra.functor_map_apply

/-- The equivalence `Mon_ (ModuleCat R) ≌ AlgebraCat R`
is naturally compatible with the forgetful functors to `ModuleCat R`.
-/
def monModuleEquivalenceAlgebraForget :
    MonModuleEquivalenceAlgebra.functor ⋙ forget₂ (AlgebraCat.{u} R) (ModuleCat.{u} R) ≅
      Mon_.forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun A =>
      { hom :=
          { toFun := _root_.id
            map_add' := fun x y => rfl
            map_smul' := fun c x => rfl }
        inv :=
          { toFun := _root_.id
            map_add' := fun x y => rfl
            map_smul' := fun c x => rfl } })
#align Module.Mon_Module_equivalence_Algebra_forget ModuleCat.monModuleEquivalenceAlgebraForget

end ModuleCat
