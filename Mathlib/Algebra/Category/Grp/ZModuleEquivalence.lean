/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic

#align_import algebra.category.Group.Z_Module_equivalence from "leanprover-community/mathlib"@"bf1b813e20e108e8868341ca94bb3404a2506ae5"

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

/-- The forgetful functor from `ℤ` modules to `AddCommGrp` is full. -/
instance forget₂_addCommGroup_full : (forget₂ (ModuleCat ℤ) AddCommGrp.{u}).Full where
  map_surjective {A B}
    -- `AddMonoidHom.toIntLinearMap` doesn't work here because `A` and `B` are not
    -- definitionally equal to the canonical `AddCommGroup.intModule` module
    -- instances it expects.
    f := ⟨@LinearMap.mk _ _ _ _ _ _ _ _ _ A.isModule B.isModule
        { toFun := f,
          map_add' := AddMonoidHom.map_add (show A.carrier →+ B.carrier from f) }
        (fun n x => by
          convert AddMonoidHom.map_zsmul (show A.carrier →+ B.carrier from f) x n <;>
            ext <;> apply int_smul_eq_zsmul), rfl⟩
set_option linter.uppercaseLean3 false in
#align Module.forget₂_AddCommGroup_full ModuleCat.forget₂_addCommGroup_full

/-- The forgetful functor from `ℤ` modules to `AddCommGrp` is essentially surjective. -/
instance forget₂_addCommGrp_essSurj : (forget₂ (ModuleCat ℤ) AddCommGrp.{u}).EssSurj where
  mem_essImage A :=
    ⟨ModuleCat.of ℤ A,
      ⟨{  hom := 𝟙 A
          inv := 𝟙 A }⟩⟩
set_option linter.uppercaseLean3 false in
#align Module.forget₂_AddCommGroup_ess_surj ModuleCat.forget₂_addCommGrp_essSurj

noncomputable instance forget₂AddCommGroupIsEquivalence :
    (forget₂ (ModuleCat ℤ) AddCommGrp.{u}).IsEquivalence where
set_option linter.uppercaseLean3 false in
#align Module.forget₂_AddCommGroup_is_equivalence ModuleCat.forget₂AddCommGroupIsEquivalence

end ModuleCat
