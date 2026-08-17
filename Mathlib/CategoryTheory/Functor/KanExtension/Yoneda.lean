/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# ...

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [LocallySmall.{w} C] [LocallySmall.{w} D]

namespace Presheaf

open Limits Opposite

variable (F : C ⥤ D) [∀ (P : Cᵒᵖ ⥤ Type w), F.op.HasLeftKanExtension P]

noncomputable instance (X : C) (Y : F.op.LeftExtension (shrinkYoneda.{w}.obj X)) :
    Unique (Functor.LeftExtension.mk _ (shrinkYonedaMap.{w} F X) ⟶ Y) where
  default :=
    StructuredArrow.homMk (shrinkYonedaEquiv.symm (shrinkYonedaEquiv Y.hom :)) (by
      ext Z f
      obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
      simp [shrinkYonedaEquiv_apply, shrinkYonedaMap_app_hom_apply.{w}, shrinkYonedaEquiv_symm_app,
        ← dsimp% Y.hom.naturality_apply f.op (shrinkYonedaObjObjEquiv.symm (𝟙 X)),
        shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}])
  uniq φ := by
    ext : 1
    apply shrinkYonedaEquiv.injective
    simp [← dsimp% StructuredArrow.w φ, shrinkYonedaEquiv_apply,
      shrinkYonedaMap_app_hom_apply.{w}]

instance (X : C) :
    (shrinkYoneda.{w}.obj (F.obj X)).IsLeftKanExtension (shrinkYonedaMap.{w} F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

/-- `F ⋙ shrinkYoneda` is naturally isomorphic to `shrinkYoneda ⋙ F.op.lan`. -/
noncomputable def compShrinkYonedaIsoShrinkYonedaCompLan :
    F ⋙ shrinkYoneda.{w} ≅ shrinkYoneda.{w} ⋙ F.op.lan :=
  NatIso.ofComponents (fun X ↦ Functor.leftKanExtensionUnique _
      (shrinkYonedaMap.{w} F X) (F.op.lan.obj _)
      (F.op.lanUnit.app (shrinkYoneda.{w}.obj X))) (fun {X Y} f ↦ by
    have (P : Cᵒᵖ ⥤ Type w) : F.op.HasLeftKanExtension P := inferInstance
    apply shrinkYonedaEquiv.injective
    have eq₁ :=
      ConcreteCategory.congr_hom
        ((shrinkYoneda.{w}.obj (F.obj Y)).descOfIsLeftKanExtension_fac_app
          (shrinkYonedaMap F Y) (F.op.lan.obj (shrinkYoneda.obj Y))
            (F.op.lanUnit.app (shrinkYoneda.obj Y)) _)
              (shrinkYonedaObjObjEquiv.symm f)
    have eq₂ :=
      ConcreteCategory.congr_hom
        ((shrinkYoneda.{w}.obj (F.obj X)).descOfIsLeftKanExtension_fac_app
          (shrinkYonedaMap F X) (F.op.lan.obj (shrinkYoneda.obj X))
            (F.op.lanUnit.app (shrinkYoneda.obj X)) _)
              (shrinkYonedaObjObjEquiv.symm (𝟙 X))
    have eq₃ := ConcreteCategory.congr_hom (congr_app (F.op.lanUnit.naturality
      (shrinkYoneda.{w}.map f)) _) (shrinkYonedaObjObjEquiv.symm (𝟙 X))
    dsimp [Functor.leftKanExtensionUnique,
      Functor.leftKanExtensionUniqueOfIso] at eq₁ eq₂ eq₃ ⊢
    simp only [shrinkYonedaMap_app_hom_apply.{w},
      shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w},
      Equiv.apply_symm_apply, Category.id_comp, Functor.map_id] at eq₁ eq₂ eq₃
    simp [shrinkYonedaEquiv_apply,
      shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}, eq₁, eq₂, eq₃])

end Presheaf

end CategoryTheory
