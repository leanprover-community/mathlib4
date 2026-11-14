/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# The internal hom for Sheaves of Modules


-/

@[expose] public section

open CategoryTheory Category Opposite

universe w v u v₁ u₁

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SheafOfModules

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj R))

/-- The Hom sheaf for sheaves of modules. -/
@[simps]
def internalHom : SheafOfModules.{max u u₁ v₁} ((sheafCompose J (forget₂ _ _)).obj R) where
  val := PresheafOfModules.internalHom F.val G.val
  isSheaf := PresheafOfModules.internalHom_presheaf_isSheaf F.val G.val G.isSheaf

/-- Implimintation note: For `X : Cᵒᵖ`, `((internalHom F G).val.obj X).carrier` is by definition
`F.val.over X.unop ⟶ G.val.over X.unop` rather than `F.over X.unop ⟶ G.over X.unop`. -/
abbrev asInternalHom {X : C} (φ : F.over X ⟶ G.over X) :
    ((internalHom F G).val.obj (op X)).carrier := φ.val

/-- This is the functor that sends `F : SheafOfModules` to `internalHom F G`.
TODO: Once the monoidal category structure for `SheafOfModules` enters mathlib, show this is right
adjoint to `MonoidalCategory.tensorLeft F`, giving `SheafOfModules`
the structure of a closed monoidal category. -/
@[simps]
def internalHomFunctor : SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj R) ⥤
    SheafOfModules.{max u u₁ v₁} ((sheafCompose J (forget₂ _ _)).obj R) where
  obj G := internalHom F G
  map φ := { val := (PresheafOfModules.internalHomFunctor F.val).map φ.val}

/-- `internalHom` commutes with `SheafOfModules.forget`. -/
def InternalHomFunctorForget : internalHomFunctor F ⋙ forget _ ≅
    forget _ ⋙ PresheafOfModules.internalHomFunctor F.val := Iso.refl _

end

end SheafOfModules
