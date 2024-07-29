/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Closed.Cartesian

/-!
# Cartesian closure of Type

Show that `Type u₁` is cartesian closed, and `C ⥤ Type u₁` is cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is cartesian closed.
-/


namespace CategoryTheory

noncomputable section

open Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section CartesianClosed

/-- The adjunction `Limits.Types.binaryProductFunctor.obj X ⊣ coyoneda.obj (Opposite.op X)`
for any `X : Type v₁`. -/
def Types.binaryProductAdjunction (X : Type v₁) :
    Limits.Types.binaryProductFunctor.obj X ⊣ coyoneda.obj (Opposite.op X) :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }
      counit := { app := fun Z xf => xf.2 xf.1 } }

instance (X : Type v₁) : (Types.binaryProductFunctor.obj X).IsLeftAdjoint :=
  ⟨_, ⟨Types.binaryProductAdjunction X⟩⟩

instance : CartesianClosed (Type v₁) := CartesianClosed.mk _
  (fun X => Exponentiable.mk _ _
    ((Types.binaryProductAdjunction X).ofNatIsoLeft (Types.binaryProductIsoProd.app X)))

namespace Presheaf

def internalHom (F : Cᵒᵖ ⥤ Type (max v₁ v₂)) :
    (Cᵒᵖ ⥤ Type (max v₁ v₂)) ⥤ (Cᵒᵖ ⥤ Type (max v₁ v₂)) where
  obj G := (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂}).op ⋙
    (prod.functor.obj F).op ⋙ yoneda.obj G
  map f :=
    whiskerLeft ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂}).op ⋙
      (prod.functor.obj F).op) (yoneda.map f)

@[simps]
def prodFunctorAdjunctionUnit (F : Cᵒᵖ ⥤ Type (max v₁ v₂)) :
    𝟭 _ ⟶ prod.functor.obj F ⋙ internalHom F where
  app G := {
    app := fun X x ↦ Limits.prod.map (𝟙 F) ((yonedaCompUliftFunctorEquiv _ _).symm x)
    naturality := by
      intros
      simp only [yonedaCompUliftFunctorEquiv, internalHom]
      aesop
  }
  naturality := by
    intro _ _ f
    simp only [Functor.id_obj, internalHom, Functor.comp_obj, prod.functor_obj_obj, Functor.id_map,
      Functor.op_obj, whiskeringRight_obj_obj, Opposite.op_unop, yonedaCompUliftFunctorEquiv,
      yoneda_obj_obj, uliftFunctor_obj, Equiv.coe_fn_symm_mk, Functor.comp_map,
      prod.functor_obj_map]
    ext
    simp only [Functor.comp_obj, Functor.op_obj, whiskeringRight_obj_obj, prod.functor_obj_obj,
      yoneda_obj_obj, FunctorToTypes.comp, whiskerLeft_app, yoneda_map_app, prod.map_map, comp_id]
    congr
    ext
    simp only [Functor.comp_obj, yoneda_obj_obj, uliftFunctor_obj, types_comp_apply]
    exact (NatTrans.naturality_apply f _ _).symm

def prodFunctorAdjunctionCounit (F : Cᵒᵖ ⥤ Type (max v₁ v₂)) :
    internalHom F ⋙ prod.functor.obj F ⟶ 𝟭 _ where
  app G := {
    app := fun X x ↦ yonedaCompUliftFunctorEquiv _ _ {
      app := fun Y y ↦ by
        apply (G.map y.1.op)
        let x2 : ((internalHom F).obj G).obj X :=
          (Limits.prod.snd : (F ⨯ (internalHom F).obj G ⟶ _)).app X x
        apply x2.app X
        simp only [Functor.op_obj, Functor.comp_obj, whiskeringRight_obj_obj, prod.functor_obj_obj]
        let x1 : F.obj X := (Limits.prod.fst : (F ⨯ (internalHom F).obj G ⟶ _)).app X x
        sorry -- exact ⟨x1, ⟨𝟙 _⟩⟩
      naturality := sorry }
    naturality := sorry
  }
  naturality := sorry

def prodFunctorAdjunction (F : Cᵒᵖ ⥤ Type (max v₁ v₂)) : prod.functor.obj F ⊣ internalHom F :=
  Adjunction.mkOfUnitCounit sorry
    -- { unit := prodFunctorAdjunctionUnit F
    --   counit := prodFunctorAdjunctionCounit F }

end Presheaf

instance {C : Type u₁} [Category.{v₁} C] : CartesianClosed (Cᵒᵖ ⥤ Type (max v₁ u₁)) :=
  CartesianClosed.mk _ (fun F => Exponentiable.mk _ _ (Presheaf.prodFunctorAdjunction F))

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Type v₁) :=
  CartesianClosed.mk _
    (fun F => by
      letI := FunctorCategory.prodPreservesColimits F
      have := Presheaf.isLeftAdjoint_of_preservesColimits (prod.functor.obj F)
      exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (prod.functor.obj F)))

/-- This is not a good instance because of the universe levels. Below is the instance where the
target category is `Type (max u₁ v₁)`. -/
def cartesianClosedFunctorToTypes {C : Type u₁} [Category.{v₁} C] :
    CartesianClosed (C ⥤ Type (max u₁ v₁ u₂)) :=
  let e : (ULiftHom.{max u₁ v₁ u₂} (ULift.{max u₁ v₁ u₂} C)) ⥤ Type (max u₁ v₁ u₂) ≌
      C ⥤ Type (max u₁ v₁ u₂) :=
      Functor.asEquivalence ((whiskeringLeft _ _ _).obj
        (ULift.equivalence.trans ULiftHom.equiv).functor)
  cartesianClosedOfEquiv e

instance {C : Type u₁} [Category.{v₁} C] : CartesianClosed (C ⥤ Type (max v₁ u₁)) :=
  CartesianClosed.mk _
    (fun F => by
      -- letI : ∀ (X : Type (max v₁ u₁)), PreservesColimitsOfSize.{v₁} (prod.functor.obj X) := sorry
      -- letI := FunctorCategory.prodPreservesColimits'.{v₁} F
      have : (prod.functor.obj F).IsLeftAdjoint := sorry
      --- have := Presheaf.isLeftAdjoint_of_preservesColimits (prod.functor.obj F)
      exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (prod.functor.obj F)))

instance {C : Type u₁} [Category.{v₁} C] : CartesianClosed (C ⥤ Type (max u₁ v₁)) :=
  cartesianClosedFunctorToTypes

instance {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{v₁} C] :
    CartesianClosed (C ⥤ Type v₁) :=
  let e : (SmallModel C) ⥤ Type v₁ ≌ C ⥤ Type v₁ :=
    Functor.asEquivalence ((whiskeringLeft _ _ _).obj (equivSmallModel _).functor)
  cartesianClosedOfEquiv e

end CartesianClosed

end

end CategoryTheory
