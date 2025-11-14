/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Type valued flat functors

-/

universe w v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

-- to be moved
instance [InitiallySmall.{w} C] : FinallySmall.{w} Cᵒᵖ where
  final_smallCategory := ⟨_, _, (fromInitialModel.{w} C).op, inferInstance⟩

instance [FinallySmall.{w} C] : InitiallySmall.{w} Cᵒᵖ where
  initial_smallCategory := ⟨_, _, (fromFinalModel.{w} C).op, inferInstance⟩

--noncomputable def Equivalence.isInitialEquiv {D : Type*} [Category D] (e : C ≌ D) (X : C) :
--    IsInitial X ≃ IsInitial (e.functor.obj X) := by
--  exact IsInitial.isInitialIffObj e.functor X

namespace Presheaf

variable {F : C ⥤ Type w} [LocallySmall.{w} C]

@[simps]
noncomputable def toShrinkYonedaCompPtOfCocone
    (c : Cocone ((CategoryOfElements.π F).op ⋙ evaluation _ (Type w))) :
    F ⟶ shrinkYoneda.{w, v, u} ⋙ c.pt where
  app X x := (c.ι.app (op (Functor.elementsMk _ _ x))).app (shrinkYoneda.{w}.obj X)
    (shrinkYonedaObjObjEquiv.symm (𝟙 X))
  naturality X Y f := by
    ext x
    have := congr_app (c.w (CategoryOfElements.homMk (Functor.elementsMk _ _ x)
      (Functor.elementsMk _ _ (F.map f x)) f rfl).op)
    dsimp at this ⊢
    simp only [← this, types_comp_apply, ← FunctorToTypes.naturality, evaluation_obj_map]
    apply congr_arg
    dsimp
    rw [← map_shrinkYonedaEquiv, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm,
      op_id, Category.comp_id, FunctorToTypes.map_id_apply,
      shrinkYonedaEquiv_shrinkYoneda_map]

namespace leftExtensionAlongShrinkYonedaEquivalence

@[simps]
noncomputable def functor :
    Cocone ((CategoryOfElements.π F).op ⋙ evaluation _ (Type w)) ⥤
      shrinkYoneda.LeftExtension F where
  obj c := Functor.LeftExtension.mk c.pt (toShrinkYonedaCompPtOfCocone c)
  map {c₁ c₂} τ := StructuredArrow.homMk τ.hom (by
    ext X x
    exact congr_fun (congr_app (τ.w (op (Functor.elementsMk _ _ x))) _) _)

@[simps]
noncomputable def inverse :
    shrinkYoneda.LeftExtension F ⥤
      Cocone ((CategoryOfElements.π F).op ⋙ evaluation _ (Type w)) where
  obj E :=
    { pt := E.right
      ι.app x :=
        { app G g := E.right.map (shrinkYonedaEquiv.symm g) (E.hom.app x.unop.fst x.unop.snd)
          naturality G₁ G₂ f := by
            ext y
            dsimp at y ⊢
            rw [← FunctorToTypes.map_comp_apply, shrinkYonedaEquiv_symm_comp y f] }
      ι.naturality x x' φ := by
        ext G y
        dsimp at y ⊢
        simp only [shrinkYonedaEquiv_symm_map φ.unop.1.op y, FunctorToTypes.map_comp_apply,
          ← φ.unop.2]
        exact congr_arg _ (congr_fun (E.hom.naturality φ.unop.1).symm _) }
  map {E₁ E₂} φ :=
    { hom := φ.right
      w x := by
        ext G y
        simp [← StructuredArrow.w φ, FunctorToTypes.naturality] }

end leftExtensionAlongShrinkYonedaEquivalence

open leftExtensionAlongShrinkYonedaEquivalence in
variable (F) in
@[simps]
noncomputable def leftExtensionAlongShrinkYonedaEquivalence :
    Cocone ((CategoryOfElements.π F).op ⋙ evaluation _ (Type w)) ≌
      Functor.LeftExtension shrinkYoneda F where
  functor := functor
  inverse := inverse
  unitIso := NatIso.ofComponents (fun c ↦ Cocones.ext (Iso.refl _) (fun x ↦ by
    ext G y
    have := congr_fun ((c.ι.app x).naturality (shrinkYonedaEquiv.symm y))
      (shrinkYonedaObjObjEquiv.symm (𝟙 _))
    dsimp at this y ⊢
    convert this using 1
    apply congr_arg
    rw [shrinkYonedaEquiv_app_shrinkYonedaObjObjEquiv_symm]
    simp))
  counitIso := NatIso.ofComponents (fun E ↦ StructuredArrow.isoMk (Iso.refl _) (by
    ext X x
    dsimp at x ⊢
    rw [← shrinkYonedaEquiv_shrinkYoneda_map]
    simp))

noncomputable def leftExtensionAlongShrinkYoneda
    (c : Cocone ((CategoryOfElements.π F).op ⋙ evaluation _ (Type w))) :
    Functor.LeftExtension shrinkYoneda F :=
  Functor.LeftExtension.mk c.pt
    { app X x := (c.ι.app (op (Functor.elementsMk _ _ x))).app (shrinkYoneda.{w}.obj X)
        (shrinkYonedaObjObjEquiv.symm (𝟙 X))
      naturality X Y f := by
        ext x
        have := congr_app (c.w (CategoryOfElements.homMk (Functor.elementsMk _ _ x)
          (Functor.elementsMk _ _ (F.map f x)) f rfl).op)
        dsimp at this ⊢
        simp only [← this, types_comp_apply, ← FunctorToTypes.naturality, evaluation_obj_map]
        apply congr_arg
        dsimp
        rw [← map_shrinkYonedaEquiv, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm,
          op_id, Category.comp_id, FunctorToTypes.map_id_apply,
          shrinkYonedaEquiv_shrinkYoneda_map] }

lemma isLeftKanExtension_along_shrinkYoneda_iff
    {G : (Cᵒᵖ ⥤ Type w) ⥤ Type w} (α : F ⟶ shrinkYoneda ⋙ G) :
    G.IsLeftKanExtension α ↔
      Nonempty (IsColimit (leftExtensionAlongShrinkYonedaEquivalence.inverse.obj (.mk _ α))) := by
  trans Nonempty (Functor.LeftExtension.mk _ α).IsUniversal
  · exact ⟨fun h ↦ h.nonempty_isUniversal, fun h ↦ ⟨h⟩⟩
  · conv_rhs => rw [(Cocone.isColimitEquivIsInitial _).nonempty_congr]
    simp [(IsInitial.isInitialIffObj (leftExtensionAlongShrinkYonedaEquivalence F).inverse
      (Functor.LeftExtension.mk _ α)).nonempty_congr]

lemma isLeftKanExtension_toShrinkYonedaCompPtOfCocone_iff
    (c : Cocone ((CategoryOfElements.π F).op ⋙ evaluation _ (Type w))) :
    Functor.IsLeftKanExtension c.pt (toShrinkYonedaCompPtOfCocone c) ↔
      Nonempty (IsColimit c) := by
  rw [isLeftKanExtension_along_shrinkYoneda_iff]
  exact Equiv.nonempty_congr (IsColimit.equivIsoColimit
    ((leftExtensionAlongShrinkYonedaEquivalence F).unitIso.symm.app _))

section

variable (F) [InitiallySmall.{w} F.Elements]

attribute [local instance] hasColimitsOfShape_of_finallySmall

noncomputable def leftKanExtensionAlongShrinkYoneda : (Cᵒᵖ ⥤ Type w) ⥤ Type w :=
  colimit ((CategoryOfElements.π F).op ⋙ evaluation _ (Type w))

noncomputable def leftKanExtensionAlongShrinkYonedaUnit :
    F ⟶ shrinkYoneda ⋙ leftKanExtensionAlongShrinkYoneda F :=
  toShrinkYonedaCompPtOfCocone (colimit.cocone
    ((CategoryOfElements.π F).op ⋙ evaluation _ (Type w)))

instance : Functor.IsLeftKanExtension _ (leftKanExtensionAlongShrinkYonedaUnit F) :=
  (isLeftKanExtension_toShrinkYonedaCompPtOfCocone_iff ..).2 ⟨colimit.isColimit _⟩

--instance [IsCofiltered F.Elements] :
--    PreservesFiniteLimits (leftKanExtensionAlongShrinkYoneda F) := sorry

end

end Presheaf

end CategoryTheory
