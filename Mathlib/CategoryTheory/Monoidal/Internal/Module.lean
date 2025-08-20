/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# `Mon_ (ModuleCat R) ≌ AlgCat R`

The category of internal monoid objects in `ModuleCat R`
is equivalent to the category of "native" bundled `R`-algebras.

Moreover, this equivalence is compatible with the forgetful functors to `ModuleCat R`.
-/

suppress_compilation


universe v u

open CategoryTheory

open LinearMap Mon_Class

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
instance Ring_of_Mon_ (A : ModuleCat.{u} R) [Mon_Class A] : Ring A :=
  { (inferInstance : AddCommGroup A) with
    one := η[A] (1 : R)
    mul := fun x y => μ[A] (x ⊗ₜ y)
    one_mul := fun x => by
      convert LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (one_mul A)) ((1 : R) ⊗ₜ x)
      rw [MonoidalCategory.leftUnitor_hom_apply, one_smul]
    mul_one := fun x => by
      convert LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (mul_one A)) (x ⊗ₜ (1 : R))
      rw [MonoidalCategory.rightUnitor_hom_apply, one_smul]
    mul_assoc := fun x y z => by
      convert LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (mul_assoc A)) (x ⊗ₜ y ⊗ₜ z)
    left_distrib := fun x y z => by
      convert μ[A].hom.map_add (x ⊗ₜ y) (x ⊗ₜ z)
      rw [← TensorProduct.tmul_add]
      rfl
    right_distrib := fun x y z => by
      convert μ[A].hom.map_add (x ⊗ₜ z) (y ⊗ₜ z)
      rw [← TensorProduct.add_tmul]
      rfl
    zero_mul := fun x => show μ[A] _ = 0 by
      rw [TensorProduct.zero_tmul, map_zero]
    mul_zero := fun x => show μ[A] _ = 0 by
      rw [TensorProduct.tmul_zero, map_zero] }

instance Algebra_of_Mon_ (A : ModuleCat.{u} R) [Mon_Class A] : Algebra R A where
  algebraMap :=
  { η[A].hom with
    map_zero' := η[A].hom.map_zero
    map_one' := rfl
    map_mul' := fun x y => by
      have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (one_mul A).symm) (x ⊗ₜ η[A] y)
      rwa [MonoidalCategory.leftUnitor_hom_apply, ← η[A].hom.map_smul] at h }
  commutes' := fun r a => by
    dsimp
    have h₁ := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (one_mul A)) (r ⊗ₜ a)
    have h₂ := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (mul_one A)) (a ⊗ₜ r)
    exact h₁.trans h₂.symm
  smul_def' := fun r a =>
    (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (one_mul A)) (r ⊗ₜ a)).symm

@[simp]
theorem algebraMap (A : ModuleCat.{u} R) [Mon_Class A] (r : R) : algebraMap R A r = η[A] r :=
  rfl

/-- Converting a monoid object in `ModuleCat R` to a bundled algebra.
-/
@[simps!]
def functor : Mon_ (ModuleCat.{u} R) ⥤ AlgCat R where
  obj A := AlgCat.of R A.X
  map {_ _} f := AlgCat.ofHom
    { f.hom.hom.toAddMonoidHom with
      toFun := f.hom
      map_one' := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (IsMon_Hom.one_hom f.hom)) (1 : R)
      map_mul' := fun x y =>
        LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (IsMon_Hom.mul_hom f.hom)) (x ⊗ₜ y)
      commutes' := fun r =>
        LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (IsMon_Hom.one_hom f.hom)) r }

/-- Converting a bundled algebra to a monoid object in `ModuleCat R`.
-/
@[simps]
def inverseObj (A : AlgCat.{u} R) : Mon_Class (ModuleCat.of R A) where
  one := ofHom <| Algebra.linearMap R A
  mul := ofHom <| LinearMap.mul' R A
  one_mul := by
    ext : 1
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| LinearMap.ext_ring <| LinearMap.ext fun x => ?_
    rw [compr₂_apply, compr₂_apply, hom_comp, LinearMap.comp_apply]
    -- Porting note: this `dsimp` does nothing
    -- dsimp [AlgCat.id_apply, TensorProduct.mk_apply, Algebra.linearMap_apply,
    --    LinearMap.compr₂_apply, Function.comp_apply, RingHom.map_one,
    --    ModuleCat.MonoidalCategory.tensorHom_tmul, AlgCat.hom_comp,
    --    ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
    -- Porting note: because `dsimp` is not effective, `rw` needs to be changed to `erw`
    dsimp
    erw [LinearMap.mul'_apply, MonoidalCategory.leftUnitor_hom_apply, ← Algebra.smul_def]
    dsimp
  mul_one := by
    ext : 1
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| LinearMap.ext fun x => LinearMap.ext_ring ?_
    -- Porting note: this `dsimp` does nothing
    -- dsimp only [AlgCat.id_apply, TensorProduct.mk_apply, Algebra.linearMap_apply,
    --   LinearMap.compr₂_apply, Function.comp_apply, ModuleCat.MonoidalCategory.hom_apply,
    --   AlgCat.coe_comp]
    -- Porting note: because `dsimp` is not effective, `rw` needs to be changed to `erw`
    erw [compr₂_apply, compr₂_apply]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [LinearMap.mul'_apply, ModuleCat.MonoidalCategory.rightUnitor_hom_apply, ← Algebra.commutes,
      ← Algebra.smul_def]
    dsimp
  mul_assoc := by
    ext : 1
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext fun x => LinearMap.ext fun y =>
      LinearMap.ext fun z => ?_
    dsimp only [compr₂_apply, TensorProduct.mk_apply]
    rw [hom_comp, LinearMap.comp_apply, hom_comp, LinearMap.comp_apply, hom_comp,
        LinearMap.comp_apply]
    erw [LinearMap.mul'_apply, LinearMap.mul'_apply]
    dsimp only [id_coe, id_eq]
    erw [TensorProduct.mk_apply, TensorProduct.mk_apply, mul'_apply, LinearMap.id_apply, mul'_apply]
    simp only [_root_.mul_assoc]

attribute [local instance] inverseObj

/-- Converting a bundled algebra to a monoid object in `ModuleCat R`.
-/
@[simps]
def inverse : AlgCat.{u} R ⥤ Mon_ (ModuleCat.{u} R) where
  obj A := { X := ModuleCat.of R A, mon := inverseObj A}
  map f :=
    { hom := ofHom <| f.hom.toLinearMap
      is_mon_hom :=
        { one_hom := hom_ext <| LinearMap.ext f.hom.commutes
          mul_hom := hom_ext <| TensorProduct.ext <| LinearMap.ext₂ <| map_mul f.hom } }

end MonModuleEquivalenceAlgebra

open MonModuleEquivalenceAlgebra

/-- The category of internal monoid objects in `ModuleCat R`
is equivalent to the category of "native" bundled `R`-algebras.
-/
def monModuleEquivalenceAlgebra : Mon_ (ModuleCat.{u} R) ≌ AlgCat R where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { hom := ofHom
                { toFun := _root_.id
                  map_add' := fun _ _ => rfl
                  map_smul' := fun _ _ => rfl }
              is_mon_hom :=
                { mul_hom := by
                    ext : 1
                    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
                    refine TensorProduct.ext ?_
                    rfl } }
          inv :=
            { hom := ofHom
                { toFun := _root_.id
                  map_add' := fun _ _ => rfl
                  map_smul' := fun _ _ => rfl }
              is_mon_hom :=
                { mul_hom := by
                    ext : 1
                    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
                    refine TensorProduct.ext ?_
                    rfl } } })
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := AlgCat.ofHom
            { toFun := _root_.id
              map_zero' := rfl
              map_add' := fun _ _ => rfl
              map_one' := (algebraMap R A).map_one
              map_mul' := fun x y => @LinearMap.mul'_apply R _ _ _ _ _ _ x y
              commutes' := fun _ => rfl }
          inv := AlgCat.ofHom
            { toFun := _root_.id
              map_zero' := rfl
              map_add' := fun _ _ => rfl
              map_one' := (algebraMap R A).map_one.symm
              map_mul' := fun x y => (@LinearMap.mul'_apply R _ _ _ _ _ _ x y).symm
              commutes' := fun _ => rfl } })

/-- The equivalence `Mon_ (ModuleCat R) ≌ AlgCat R`
is naturally compatible with the forgetful functors to `ModuleCat R`.
-/
def monModuleEquivalenceAlgebraForget :
    MonModuleEquivalenceAlgebra.functor ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ≅
      Mon_.forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun A =>
      { hom := ofHom
          { toFun := _root_.id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        inv := ofHom
          { toFun := _root_.id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl } })

end ModuleCat
