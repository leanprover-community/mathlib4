/-
Copyright (c) 2023 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.RingMod
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.FullSubcategory

open CategoryTheory

universe v u

variable {C : Type u₁} [Category.{v₁} C] {R : Type u₂} [Category.{v₂} R]

/--
Presheaves relative to another presheaf.

Given some `F : Cᵒᵖ ⥤ R`, and some `L : Rᵒᵖ ⥤ Cat`,
we can look at functors `P : Cᵒᵖ ⥤ opGrothendieck L`
such that `P ⋙ opGrothendieck.forget L = F`.

These are presheaves valued in the Grothendieck construction for `L`,
with base part specified by `F`.

Mostly this is just abstract nonsense, that serves as a playground to test our definition of
`PresheafOfModules F` by showing that it is equivalent to `PresheafRel F ModuleCat.functor`
-/
-- We could alternatively do this with a natural isomorphism rather than an equality.
-- It would be larger and less evil, but nevertheless equivalent to this version.
def PresheafRel (F : Cᵒᵖ ⥤ R) (L : Rᵒᵖ ⥤ Cat.{v₃, u₃}) : Type (max v₁ v₂ v₃ u₁ u₂ u₃) :=
  FullSubcategory fun (presheaf : Cᵒᵖ ⥤ opGrothendieck L) => presheaf ⋙ opGrothendieck.forget L = F

instance (F : Cᵒᵖ ⥤ R) (L : Rᵒᵖ ⥤ Cat.{v₃, u₃}) :
    Category.{max v₂ v₃ u₁, max v₁ v₂ v₃ u₁ u₂ u₃} (PresheafRel F L) := by
  dsimp [PresheafRel]
  infer_instance

namespace PresheafOfModules

namespace equiv_PresheafRel

variable (F : Cᵒᵖ ⥤ RingCat.{u})

@[simps]
def functor_obj (P : PresheafOfModules F) : PresheafRel F ModuleCat.functor.{v} :=
  { obj :=
    { obj := fun X =>
      { base := F.obj X,
        fiber := P.obj X },
      map := @fun X Y f =>
      { base := F.map f,
        fiber := (ModuleCat.hom_functor_map_equiv (F.map f)).symm (P.map f), },
      map_id := fun X => by
        fapply opGrothendieck.ext
        · simp
        · apply ModuleCat.ext
          dsimp
          intro x
          simp only [map_id]
          erw [ModuleCat.coe_comp, ModuleCat.id_apply]
          simp only [Function.comp_apply, ModuleCat.hom_functor_map_equiv_symm_apply_apply,
            LinearMap.id'_apply]
          sorry
      map_comp := sorry, },
    property := rfl, }

set_option maxHeartbeats 0 in
def functor_map {P Q : PresheafOfModules F} (f : P ⟶ Q) : functor_obj F P ⟶ functor_obj F Q :=
  { app := fun X =>
    { base := 𝟙 _,
      fiber := f.app X, },
    naturality := @fun X Y g => by
      fapply opGrothendieck.ext
      · simp only [functor_obj_obj_obj_base, opGrothendieck.comp_base', functor_obj_obj_map_base,
          Category.comp_id, Category.id_comp]
      · apply ModuleCat.ext
        dsimp
        intro x
        simp only [Category.comp_id]
        erw [ModuleCat.coe_comp, ModuleCat.coe_comp]
        simp only [Function.comp_apply, ModuleCat.hom_functor_map_equiv_symm_apply_apply, map_apply]
        set_option linter.deprecated false in
        exact AddMonoidHom.congr_fun (f.hom.naturality g) x }

attribute [simps] functor_map

def functor : PresheafOfModules F ⥤ PresheafRel F ModuleCat.functor.{v} where
  obj P := functor_obj F P
  map f := functor_map F f

end equiv_PresheafRel

open equiv_PresheafRel

def PresheafOfModules.equiv_PresheafRel (F : Cᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules F ≌ PresheafRel F ModuleCat.functor.{v} where
  functor := functor F
  inverse := sorry
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end PresheafOfModules
