/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# The internal hom for presheaves of modules


-/

@[expose] public section

open CategoryTheory Category Opposite

universe w v u v₁ u₁

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  {F G : SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj R)}

@[simps]
noncomputable def internalHom (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj R)) :
    SheafOfModules ((sheafCompose J (forget₂ _ _)).obj R) where
  val := PresheafOfModules.internalHom F.val G.val
  isSheaf := PresheafOfModules.internalHom_presheaf_isSheaf F.val G.val G.isSheaf

variable (U : Cᵒᵖ)

#simp (internalHom F G).val

#simp ((internalHom F G).val.obj U).carrier

example (U : C) : F.val.over U = (F.over U).val := rfl

end SheafOfModules
