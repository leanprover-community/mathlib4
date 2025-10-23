/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.Limits
import Mathlib.CategoryTheory.ObjectProperty.Local
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Presheaves of types which preserves a limit
-/

universe w w' v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

protected abbrev Small (F : C ⥤ Type w') := ∀ (X : C), _root_.Small.{w} (F.obj X)

@[simps]
noncomputable def shrink (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] :
    C ⥤ Type w where
  obj X := Shrink.{w} (F.obj X)
  map {X Y} f := equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm

attribute [local simp] FunctorToTypes.naturality in
@[simps]
noncomputable def shrinkMap {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{w} G] :
    shrink.{w} F ⟶ shrink.{w} G where
  app X := equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm

end FunctorToTypes

instance [LocallySmall.{w} C] (X : C) : FunctorToTypes.Small.{w} (yoneda.obj X) :=
  fun _ ↦ by dsimp; infer_instance

noncomputable def shrinkYoneda [LocallySmall.{w} C] :
    C ⥤ Cᵒᵖ ⥤ Type w where
  obj X := FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

namespace Presheaf

variable {J : Type w} [SmallCategory J] [LocallySmall.{w} C]
  {F : J ⥤ Cᵒᵖ} (c : Cone F)

noncomputable def colimitToShrinkYoneda :
    colimit (F.leftOp ⋙ shrinkYoneda) ⟶ shrinkYoneda.{w}.obj c.pt.unop :=
  colimit.desc _ (shrinkYoneda.{w}.mapCocone (coconeLeftOpOfCone c))

variable (P : Cᵒᵖ ⥤ Type w)

lemma nonempty_isLimit_mapCone_iff :
    Nonempty (IsLimit (P.mapCone c)) ↔
      (MorphismProperty.single (colimitToShrinkYoneda c)).isLocal P := by
  sorry

variable {c}

lemma preservesLimit_eq_isLocal_single (hc : IsLimit c) :
    Functor.preservesLimit (Type w) F =
      (MorphismProperty.single (colimitToShrinkYoneda c)).isLocal := by
  ext P
  rw [← nonempty_isLimit_mapCone_iff c P]
  exact ⟨fun _ ↦ ⟨isLimitOfPreserves P hc⟩,
    fun ⟨h⟩ ↦ preservesLimit_of_preserves_limit_cone hc h⟩

end Presheaf

end CategoryTheory
