/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.RestrictedYoneda

/-!
# ...

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Presheaf

-- to be moved
lemma comp_shrinkYonedaMap_comp_eq_yonedaMap
    {D : Type*} [Category.{v₁} D] (F : C ⥤ D) (X : C) :
    shrinkYonedaIsoYoneda.inv.app _ ≫ shrinkYonedaMap.{v₁} F X ≫
      Functor.whiskerLeft _ (shrinkYonedaIsoYoneda.hom.app _) = yonedaMap F X := by
  ext
  simp [shrinkYonedaMap_app_hom_apply.{v₁}]

-- to be moved
lemma comp_shrinkYonedaMap_comp_eq_uliftYonedaMap
    (F : C ⥤ D) (X : C) :
    uliftYonedaIsoShrinkYoneda.hom.app _ ≫ shrinkYonedaMap.{max w v₁ v₂} F X ≫
      Functor.whiskerLeft _ (uliftYonedaIsoShrinkYoneda.inv.app _) =
    uliftYonedaMap.{w} F X := by
  ext
  simp [shrinkYonedaMap_app_hom_apply.{max w v₁ v₂}, uliftYonedaMap,
    uliftYonedaIsoShrinkYoneda_inv_app_app,
    uliftYonedaIsoShrinkYoneda_hom_app_app]

open Limits Opposite

section shrinkYoneda

variable [LocallySmall.{w} C] [LocallySmall.{w} D] (F : C ⥤ D)
  [∀ (P : Cᵒᵖ ⥤ Type w), F.op.HasLeftKanExtension P]

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

/-- If `F : C ⥤ D` and `X : C`, the functor `shrinkYoneda.obj (F.obj X)` is
a left Kan extension of `shrinkYoneda.obj X` along `F.op`. -/
instance (X : C) :
    (shrinkYoneda.{w}.obj (F.obj X)).IsLeftKanExtension (shrinkYonedaMap.{w} F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

/-- `F ⋙ shrinkYoneda` is naturally isomorphic to `shrinkYoneda ⋙ F.op.lan`. -/
@[no_expose]
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

@[reassoc (attr := simp)]
lemma comp_whiskerLeft_compShrinkYonedaIsoShrinkYonedaCompLan_inv_app (X : C) :
    F.op.lanUnit.app (shrinkYoneda.{w}.obj X) ≫
      Functor.whiskerLeft F.op ((compShrinkYonedaIsoShrinkYonedaCompLan.{w} F).inv.app X) =
    shrinkYonedaMap.{w} F X := by
  simp [compShrinkYonedaIsoShrinkYonedaCompLan]

@[reassoc (attr := simp)]
lemma comp_whiskerLeft_compShrinkYonedaIsoShrinkYonedaCompLan_hom_app (X : C) :
    shrinkYonedaMap.{w} F X ≫
      Functor.whiskerLeft F.op ((compShrinkYonedaIsoShrinkYonedaCompLan.{w} F).hom.app X) =
    F.op.lanUnit.app (shrinkYoneda.{w}.obj X) := by
  simp [compShrinkYonedaIsoShrinkYonedaCompLan]

@[simp]
lemma compShrinkYonedaIsoShrinkYonedaCompLan_inv_app_app_eq_id (X : C) :
    dsimp% ((compShrinkYonedaIsoShrinkYonedaCompLan.{w} F).inv.app X).app (op (F.obj X))
        ((F.op.lanUnit.app (shrinkYoneda.{w}.obj X)).app (op X)
          (shrinkYonedaObjObjEquiv.symm (𝟙 X))) =
    shrinkYonedaObjObjEquiv.symm (𝟙 (F.obj X)) := by
  simpa only [shrinkYonedaMap_app_shrinkYonedaObjObjEquiv_symm.{w},
    Functor.map_id] using! ConcreteCategory.congr_hom (NatTrans.congr_app
    (comp_whiskerLeft_compShrinkYonedaIsoShrinkYonedaCompLan_inv_app.{w} F X) (op X))
      (shrinkYonedaObjObjEquiv.symm (𝟙 X))

noncomputable def isPointwiseLeftKanExtensionLanOp :
    (Functor.LeftExtension.mk _
      (compShrinkYonedaIsoShrinkYonedaCompLan.{w} F).hom).IsPointwiseLeftKanExtension :=
  Presheaf.isPointwiseLeftKanExtensionAlongShrinkYoneda _

instance : F.op.lan.IsLeftKanExtension (compShrinkYonedaIsoShrinkYonedaCompLan.{w} F).hom :=
  (isPointwiseLeftKanExtensionLanOp.{w} F).isLeftKanExtension

end shrinkYoneda

section yoneda

/-- If `F : C ⥤ D` and `X : C`, the functor `yoneda.obj (F.obj X)` is
a left Kan extension of `yoneda.obj X` along `F.op`. -/
instance {D : Type*} [Category.{v₁} D] (F : C ⥤ D) (X : C) :
    (yoneda.obj (F.obj X)).IsLeftKanExtension (yonedaMap F X) := by
  rw [← comp_shrinkYonedaMap_comp_eq_yonedaMap]
  infer_instance

end yoneda

section uliftYoneda

/-- If `F : C ⥤ D` and `X : C`, the functor `uliftYoneda.obj (F.obj X)` is
a left Kan extension of `uliftYoneda.obj X` along `F.op`. -/
instance (F : C ⥤ D) (X : C) : (uliftYoneda.{max w v₁}.obj (F.obj X)).IsLeftKanExtension
    (uliftYonedaMap.{w} F X) := by
  rw [← comp_shrinkYonedaMap_comp_eq_uliftYonedaMap]
  infer_instance

variable (F : C ⥤ D) [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

/-- `F ⋙ uliftYoneda` is naturally isomorphic to `uliftYoneda ⋙ F.op.lan`. -/
@[no_expose]
noncomputable def compULiftYonedaIsoULiftYonedaCompLan :
    F ⋙ uliftYoneda.{max w v₁} ≅ uliftYoneda.{max w v₂} ⋙ F.op.lan :=
  Functor.isoWhiskerLeft _ uliftYonedaIsoShrinkYoneda ≪≫
    compShrinkYonedaIsoShrinkYonedaCompLan.{max w v₁ v₂} F ≪≫
    Functor.isoWhiskerRight uliftYonedaIsoShrinkYoneda.symm _

@[simp]
lemma compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id (X : C) :
    dsimp% ((compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X).app (op (F.obj X))
          ((F.op.lanUnit.app ((uliftYoneda.{max w v₂}).obj X)).app (op X)
        (ULift.up (𝟙 X))) = ULift.up (𝟙 (F.obj X)) := by
  apply injective_of_mono ((uliftYonedaIsoShrinkYoneda.hom.app (F.obj X)).app (op (F.obj X)))
  dsimp [compULiftYonedaIsoULiftYonedaCompLan]
  simp only [← ConcreteCategory.comp_apply,
    Category.assoc, Iso.inv_hom_id_app_app, Category.comp_id,
    uliftYonedaIsoShrinkYoneda_hom_app_app,
    ← compShrinkYonedaIsoShrinkYonedaCompLan_inv_app_app_eq_id.{max w v₁ v₂} F X]
  simp [← dsimp% ConcreteCategory.congr_hom
    (F.op.lanUnit.naturality_app (op X) (uliftYonedaIsoShrinkYoneda.{max w v₂}.hom.app X))
        (ULift.up (𝟙 X) :), uliftYonedaIsoShrinkYoneda_hom_app_app]

instance : F.op.lan.IsLeftKanExtension (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom := by
  dsimp [compULiftYonedaIsoULiftYonedaCompLan]
  infer_instance

end uliftYoneda

end Presheaf

end CategoryTheory
