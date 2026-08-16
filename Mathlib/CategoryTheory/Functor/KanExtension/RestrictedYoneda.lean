/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.RestrictedYoneda

/-!
# ...

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Presheaf

open Limits Opposite

section shrinkYoneda

variable [LocallySmall.{w} C] [LocallySmall.{w} D] {L : (Cᵒᵖ ⥤ Type w) ⥤ D}
  {A : C ⥤ D} [shrinkYoneda.{w}.HasPointwiseLeftKanExtension A]
  (α : A ⟶ shrinkYoneda.{w} ⋙ L) [L.IsLeftKanExtension α]

variable (A) in
noncomputable def restrictedShrinkYonedaHomEquivAux (P : Cᵒᵖ ⥤ Type w) (E : D) :
    (CostructuredArrow.proj shrinkYoneda.{w} P ⋙ A ⟶
      (Functor.const (CostructuredArrow shrinkYoneda.{w} P)).obj E) ≃
    (P ⟶ (restrictedShrinkYoneda A).obj E) where
  toFun f :=
    { app X := ↾(fun x ↦
        shrinkYonedaObjObjEquiv.symm
          (f.app (CostructuredArrow.mk (shrinkYonedaEquiv.symm x))))
      naturality := sorry }
  invFun g :=
    { app y := shrinkYonedaObjObjEquiv.{w} (shrinkYonedaEquiv (y.hom ≫ g) :)
      naturality := sorry }
  left_inv := sorry
  right_inv := sorry

noncomputable def restrictedShrinkYonedaHomEquiv (P : Cᵒᵖ ⥤ Type w) (E : D) :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedShrinkYoneda.{w} A).obj E) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv.trans
    (restrictedShrinkYonedaHomEquivAux A P E)

noncomputable def restrictedShrinkYonedaAdjunction : L ⊣ restrictedShrinkYoneda.{w} A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictedShrinkYonedaHomEquiv α
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

include α in
/-- Any left Kan extension along the Yoneda embedding preserves colimits. -/
lemma preservesColimitsOfSize_of_isLeftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} L :=
  (restrictedShrinkYonedaAdjunction α).leftAdjoint_preservesColimits

end shrinkYoneda

section uliftYoneda

variable {L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ D}
  {A : C ⥤ D} [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A]
  (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L) [L.IsLeftKanExtension α]

noncomputable def restrictedULiftYonedaAdjunction : L ⊣ restrictedULiftYoneda.{max w v₁} A :=
  have : shrinkYoneda.{max w v₁ v₂}.HasPointwiseLeftKanExtension A := fun Y ↦ by
    rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso
      uliftYonedaIsoShrinkYoneda.{max w v₂} (Iso.refl A)]
    infer_instance
  (restrictedShrinkYonedaAdjunction (α ≫ Functor.whiskerRight
    (uliftYonedaIsoShrinkYoneda).hom L)).ofNatIsoRight (restrictedULiftYonedaIso A).symm

lemma restrictedULiftYonedaAdjunction_unit_app_app_down
    (P : Cᵒᵖ ⥤ Type (max w v₁ v₂)) {X : Cᵒᵖ} (x : P.obj X) :
    (((restrictedULiftYonedaAdjunction α).unit.app P).app X x).down =
      α.app X.unop ≫ L.map (uliftYonedaEquiv.symm x) := by
  dsimp
  sorry

instance : IsIso α := by
  have : uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A := inferInstance
  have : L.IsLeftKanExtension α := inferInstance
  sorry

end uliftYoneda

end Presheaf

end CategoryTheory
