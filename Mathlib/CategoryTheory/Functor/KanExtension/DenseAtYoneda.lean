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
This is stated in two ways, for each of the variants of the
Yoneda embedding (`yoneda`, `yonedaULift` and `shrinkYoneda`):
* as the density of the Yoneda emebedding `C ⥤ Cᵒᵖ ⥤ Type _`,
which corresponds to the fact that for each presheaf `P : Cᵒᵖ ⥤ Type _`,
the corresponding canonical cocones indexed by categories of structured
arrows for the Yoneda embedding are colimit.
* as the fact that for any `P : Cᵒᵖ ⥤ Type _`, there is a colimit
cocone involving representable presheaves that is indexed by
the opposite category of the category of elements of `P`.

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]

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

/-- When `C` is a locally `w`-small category, the functor `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w`
is dense at any `P : Cᵒᵖ ⥤ Type w`: the presheaf `P` identifies to the colimit
of the canonical cocone of representable presheaves indexed by the
category `CostructuredArrow shrinkYoneda P`. -/
@[no_expose]
noncomputable def denseAtShrinkYoneda [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) :
    shrinkYoneda.DenseAt P :=
  Functor.denseAt _ _

/-- When `C` is a category where morphisms are in `Type v`,
the functor `yoneda : C ⥤ Cᵒᵖ ⥤ Type v` is dense at any `P : Cᵒᵖ ⥤ Type v`:
the presheaf `P` identifies to the colimit
of the canonical cocone of representable presheaves indexed by the
category `CostructuredArrow yoneda P`. -/
@[no_expose]
noncomputable def denseAtYoneda (P : Cᵒᵖ ⥤ Type v) : yoneda.DenseAt P :=
  Functor.denseAt _ _

/-- When `C` is a category where morphisms are in `Type v`,
the functor `uliftYoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type max w v` is dense at
any `P : Cᵒᵖ ⥤ Type max w v`: the presheaf `P` identifies to the colimit
of the canonical cocone of representable presheaves indexed by the
category `CostructuredArrow uliftYoneda P`. -/
@[no_expose]
noncomputable def denseAtUliftYoneda (P : Cᵒᵖ ⥤ Type max w v) : uliftYoneda.DenseAt P :=
  Functor.denseAt _ _

namespace Functor.Elements

/-- The (colimit) cocone which expresses a presheaf `P : Cᵒᵖ ⥤ Type w` as
as colimit (indexed by `P.Elementsᵒᵖ`) of representable presheaves
(defined using `shrinkYoneda`). -/
@[implicit_reducible, simps]
noncomputable def shrinkYonedaCocone [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) :
    Cocone ((CategoryOfElements.π P).leftOp ⋙ shrinkYoneda.{w}) where
  pt := P
  ι.app x := shrinkYonedaEquiv.symm x.unop.snd
  ι.naturality x y f := by simp [← shrinkYonedaEquiv_symm_map.{w}]

/-- Any presheaf `P` is a colimit of representable presheaves
(defined using `shrinkYoneda`) indexed by the opposite category of elements in `P`. -/
noncomputable def isColimitShrinkYonedaCocone [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) :
    IsColimit (shrinkYonedaCocone.{w} P) :=
  (IsColimit.whiskerEquivalenceEquiv
    (CategoryOfElements.costructuredArrowShrinkYonedaEquivalence P).symm).2
      (IsColimit.ofIsoColimit (denseAtShrinkYoneda.{w} P) (Cocone.ext (Iso.refl _)))

/-- The (colimit) cocone which expresses a presheaf `P : Cᵒᵖ ⥤ Type v` as
as colimit (indexed by `P.Elementsᵒᵖ`) of representable presheaves
(defined using `yoneda`). -/
@[implicit_reducible, simps]
def yonedaCocone (P : Cᵒᵖ ⥤ Type v) :
    Cocone ((CategoryOfElements.π P).leftOp ⋙ yoneda) where
  pt := P
  ι.app x := yonedaEquiv.symm x.unop.snd
  ι.naturality x y f := by simp [yonedaEquiv_symm_naturality_left f.unop.1.unop]

/-- Any presheaf `P` is a colimit of representable presheaves
(defined using `yoneda`) indexed by the opposite category of elements in `P`. -/
noncomputable def isColimitYonedaCocone (P : Cᵒᵖ ⥤ Type v) :
    IsColimit (yonedaCocone P) :=
  (IsColimit.whiskerEquivalenceEquiv
    (CategoryOfElements.costructuredArrowYonedaEquivalence P).symm).2
      (IsColimit.ofIsoColimit (denseAtYoneda P) (Cocone.ext (Iso.refl _)))

/-- The (colimit) cocone which expresses a presheaf `P : Cᵒᵖ ⥤ Type max w v` as
as colimit (indexed by `P.Elementsᵒᵖ`) of representable presheaves
(defined using `uliftYoneda`). -/
@[implicit_reducible, simps]
def uliftYonedaCocone (P : Cᵒᵖ ⥤ Type max w v) :
    Cocone ((CategoryOfElements.π P).leftOp ⋙ uliftYoneda.{w}) where
  pt := P
  ι.app x := uliftYonedaEquiv.symm x.unop.snd
  ι.naturality x y f := by simp [uliftYonedaEquiv_symm_naturality_left f.unop.1.unop]

/-- Any presheaf `P` is a colimit of representable presheaves
(defined using `uliftYoneda`) indexed by the opposite category of elements in `P`. -/
noncomputable def isColimitUliftYonedaCocone (P : Cᵒᵖ ⥤ Type max w v) :
    IsColimit (uliftYonedaCocone.{w} P) :=
  (IsColimit.whiskerEquivalenceEquiv
    (CategoryOfElements.costructuredArrowULiftYonedaEquivalence P).symm).2
      (IsColimit.ofIsoColimit (denseAtUliftYoneda P) (Cocone.ext (Iso.refl _)))

end Functor.Elements

end CategoryTheory
