/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Pushforward of presheaves of modules

If `F : C ⥤ D`, the precomposition `F.op ⋙ _` induces a functor from presheaves
over `C` to presheaves over `D`. When `R : Dᵒᵖ ⥤ RingCat`, we define the
induced functor `pushforward₀ : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R)`
on presheaves of modules.

In case we have a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, we also construct
a functor `pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S`.

-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₂} D]

namespace PresheafOfModules

instance {R : Dᵒᵖ ⥤ RingCat.{u}} (P : PresheafOfModules.{v} R) (F : C ⥤ D) (X : Cᵒᵖ) :
    Module ((F.op ⋙ R).obj X) ((F.op ⋙ P.presheaf).obj X) :=
  inferInstanceAs (Module (R.obj (F.op.obj X)) (P.presheaf.obj (F.op.obj X)))

variable (F : C ⥤ D)

/-- The pushforward functor on presheaves of modules for a functor `F : C ⥤ D` and
`R : Dᵒᵖ ⥤ RingCat`. On the underlying presheaves of abelian groups, it is induced
by the precomposition with `F.op`. -/
def pushforward₀ (R : Dᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R) where
  obj P :=
    { presheaf := F.op ⋙ P.presheaf
      map_smul := by intros; apply P.map_smul }
  map {P Q} φ :=
    { hom := whiskerLeft F.op φ.hom
      map_smul := by intros; apply φ.map_smul }

/-- The pushforward of presheaves of modules commutes with the forget functor
to presheaves of abelian groups. -/
def pushforward₀CompToPresheaf (R : Dᵒᵖ ⥤ RingCat.{u}) :
    pushforward₀.{v} F R ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

variable {F}
variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

def pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S := by
  refine' pushforward₀ F R ⋙ _
  sorry

end PresheafOfModules
