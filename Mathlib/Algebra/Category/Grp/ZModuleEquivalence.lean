/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
The forgetful functor from ℤ-modules to additive commutative groups is
an equivalence of categories.

TODO:
either use this equivalence to transport the monoidal structure from `Module ℤ` to `Ab`,
or, having constructed that monoidal structure directly, show this functor is monoidal.
-/


open CategoryTheory

open CategoryTheory.Equivalence

universe u

namespace ModuleCat

/-- The forgetful functor from `ℤ` modules to `AddCommGrpCat` is full. -/
instance forget₂_addCommGroup_full : (forget₂ (ModuleCat ℤ) AddCommGrpCat.{u}).Full where
  map_surjective {A B}
    -- `AddMonoidHom.toIntLinearMap` doesn't work here because `A` and `B` are not
    -- definitionally equal to the canonical `AddCommGroup.toIntModule` module
    -- instances it expects.
    f := ⟨@ModuleCat.ofHom _ _ _ _ _ A.isModule _ B.isModule <|
            @LinearMap.mk _ _ _ _ _ _ _ _ _ A.isModule B.isModule
            { toFun := f,
              map_add' := AddMonoidHom.map_add f.hom }
            (fun n x => by
              convert AddMonoidHom.map_zsmul f.hom x n <;>
                ext <;> apply int_smul_eq_zsmul), rfl⟩

/-- The forgetful functor from `ℤ` modules to `AddCommGrpCat` is essentially surjective. -/
instance forget₂_addCommGrp_essSurj : (forget₂ (ModuleCat ℤ) AddCommGrpCat.{u}).EssSurj where
  mem_essImage A :=
    ⟨ModuleCat.of ℤ A,
      ⟨{  hom := 𝟙 A
          inv := 𝟙 A }⟩⟩

noncomputable instance forget₂AddCommGroupIsEquivalence :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat.{u}).IsEquivalence where

end ModuleCat
