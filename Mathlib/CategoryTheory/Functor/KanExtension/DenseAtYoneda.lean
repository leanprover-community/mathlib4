/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense

/-!
# The Yoneda embedding is dense

Any presheaf of types is a colimit of representable presheaves.

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Limits in
instance [LocallySmall.{w} C] : (shrinkYoneda.{w} (C := C)).IsDense where
  isDenseAt P :=
    ⟨evaluationJointlyReflectsColimits _ (fun X ↦ Nonempty.some (by
      rw [Types.isColimit_iff_coconeTypesIsColimit]
      refine ⟨⟨fun y₁ y₂ hy ↦ ?_, fun x ↦ ?_⟩⟩
      · have (Y : CostructuredArrow shrinkYoneda.{w} P)
            (y : (shrinkYoneda.{w}.obj Y.left).obj X) :
          ((CostructuredArrow.proj shrinkYoneda.{w} P ⋙ shrinkYoneda.{w}) ⋙
            (evaluation _ _).obj X).ιColimitType Y y =
              Functor.ιColimitType _ (CostructuredArrow.mk
                (shrinkYonedaEquiv.symm (Y.hom.app X y)))
                  (shrinkYonedaObjObjEquiv.symm (𝟙 X.unop)) :=
          Functor.ιColimitType_eq_of_map_eq_map _ _ _ (𝟙 _)
            (CostructuredArrow.homMk (shrinkYonedaObjObjEquiv y) (by
              rw [← shrinkYonedaEquiv_symm_comp]
              rfl)) (by
              simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])
        obtain ⟨Y₁, y₁, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y₁
        obtain ⟨Y₂, y₂, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y₂
        rw [this Y₁ y₁, this Y₂ y₂, dsimp% hy]
      · exact ⟨Functor.ιColimitType _ (CostructuredArrow.mk (shrinkYonedaEquiv.symm x))
          (shrinkYonedaObjObjEquiv.symm (𝟙 X.unop)), by
          simp [shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm.{w}]⟩))⟩

instance : (uliftYoneda.{w} (C := C)).IsDense :=
  .of_iso uliftYonedaIsoShrinkYoneda.symm

instance : (yoneda (C := C)).IsDense :=
  .of_iso uliftYonedaIsoYoneda

@[no_expose]
noncomputable def denseAtShrinkYoneda [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) :
    shrinkYoneda.DenseAt P :=
  Functor.denseAt _ _

/-- `yoneda` is dense: Every `P : Cᵒᵖ ⥤ Type v` is the colimit over
`CostructuredArrow.proj yoneda X ⋙ yoneda`. -/
@[no_expose]
noncomputable def denseAtYoneda (P : Cᵒᵖ ⥤ Type v) : yoneda.DenseAt P :=
  Functor.denseAt _ _

/-- `uliftYoneda` is dense: Every `P : Cᵒᵖ ⥤ Type max w v` is the colimit over
`CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda`. -/
@[no_expose]
noncomputable def denseAtUliftYoneda (P : Cᵒᵖ ⥤ Type max w v) : uliftYoneda.DenseAt P :=
  Functor.denseAt _ _

end CategoryTheory
