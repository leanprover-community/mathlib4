/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `PUnit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/

@[expose] public section

assert_not_exists AddCommMonoid

open Opposite CategoryTheory Limits ConcreteCategory

universe t w w' v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type u} [Category.{v} C]

/-- The colimit cocone over `coyoneda.obj X`, with cocone point `PUnit`.
-/
@[simps]
def colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X) where
  pt := PUnit
  ι := { app _ := ↾fun _ ↦ by cat_disch }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X) where
  desc s := ↾fun _ ↦ s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    ext f
    simpa using congr_hom (s.w f).symm (𝟙 (unop X))
  uniq s m w := by
    ext ⟨⟩
    simp [← w]

instance (X : Cᵒᵖ) : HasColimit (coyoneda.obj X) :=
  HasColimit.mk
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

/-- The colimit of `coyoneda.obj X` is isomorphic to `PUnit`.
-/
noncomputable def colimitCoyonedaIso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit := by
  apply colimit.isoColimitCocone
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

end Coyoneda

variable {C : Type u} [Category.{v} C]

open Limits

section

variable {J : Type w} [Category.{t} J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone of `F` corresponding to an element in `(F ⋙ yoneda.obj X).sections`. -/
@[simps]
def Limits.coneOfSectionCompYoneda (F : J ⥤ Cᵒᵖ) (X : C)
    (s : (F ⋙ yoneda.obj X).sections) : Cone F where
  pt := Opposite.op X
  π := {
    app := fun j => (s.val j).op
    naturality _ _ f := by simp [(s.property f).symm] }

instance yoneda_preservesLimit (F : J ⥤ Cᵒᵖ) (X : C) :
    PreservesLimit F (yoneda.obj X) where
  preserves {c} hc := by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨(hc.lift (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩)).unop,
      fun j => Quiver.Hom.op_inj (hc.fac (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) j),
      fun m hm => Quiver.Hom.op_inj
        (hc.uniq (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) _
          (fun j => Quiver.Hom.unop_inj (hm j)))⟩

variable (J) in
noncomputable instance yoneda_preservesLimitsOfShape (X : C) :
    PreservesLimitsOfShape J (yoneda.obj X) where

set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embeddings jointly reflect limits. -/
def yonedaJointlyReflectsLimits (F : J ⥤ Cᵒᵖ) (c : Cone F)
    (hc : ∀ X : C, IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c where
  lift s := ((hc s.pt.unop).lift ((yoneda.obj s.pt.unop).mapCone s) (𝟙 _)).op
  fac s j := Quiver.Hom.unop_inj (by
    simpa using congr_hom ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 (unop s.pt)))
  uniq s m hm := Quiver.Hom.unop_inj (by
    apply (Types.isLimitEquivSections (hc s.pt.unop)).injective
    ext j
    have eq := congr_hom ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 (unop s.pt))
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    simp_all [← hm])

/-- A cocone is colimit iff it becomes limit after the
application of `yoneda.obj X` for all `X : C`. -/
noncomputable def Limits.Cocone.isColimitYonedaEquiv {F : J ⥤ C} (c : Cocone F) :
    IsColimit c ≃ ∀ (X : C), IsLimit ((yoneda.obj X).mapCone c.op) where
  toFun h _ := isLimitOfPreserves _ h.op
  invFun h := IsLimit.unop (yonedaJointlyReflectsLimits _ _ h)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone of `F` corresponding to an element in `(F ⋙ coyoneda.obj X).sections`. -/
@[simps]
def Limits.coneOfSectionCompCoyoneda (F : J ⥤ C) (X : Cᵒᵖ)
    (s : (F ⋙ coyoneda.obj X).sections) : Cone F where
  pt := X.unop
  π := {
    app := fun j => s.val j
    naturality _ _ f := by simp [(s.property f).symm] }

instance coyoneda_preservesLimit (F : J ⥤ C) (X : Cᵒᵖ) :
    PreservesLimit F (coyoneda.obj X) where
  preserves {c} hc := by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨hc.lift (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩), hc.fac _,
      hc.uniq (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩)⟩

variable (J) in
noncomputable instance coyonedaPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (coyoneda.obj X) where

set_option backward.isDefEq.respectTransparency false in
/-- The coyoneda embeddings jointly reflect limits. -/
def coyonedaJointlyReflectsLimits (F : J ⥤ C) (c : Cone F)
    (hc : ∀ X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c where
  lift s := (hc (op s.pt)).lift ((coyoneda.obj (op s.pt)).mapCone s) (𝟙 _)
  fac s j := by simpa using congr_hom ((hc (op s.pt)).fac
    ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 s.pt)
  uniq s m hm := by
    apply (Types.isLimitEquivSections (hc (op s.pt))).injective
    ext j
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    have eq := congr_hom ((hc (op s.pt)).fac ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 s.pt)
    cat_disch

/-- A cone is limit iff it is so after the application of `coyoneda.obj X` for all `X : Cᵒᵖ`. -/
noncomputable def Limits.Cone.isLimitCoyonedaEquiv {F : J ⥤ C} (c : Cone F) :
    IsLimit c ≃ ∀ (X : Cᵒᵖ), IsLimit ((coyoneda.obj X).mapCone c) where
  toFun h _ := isLimitOfPreserves _ h
  invFun h := coyonedaJointlyReflectsLimits _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

end

/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
instance yoneda_preservesLimits (X : C) :
    PreservesLimitsOfSize.{t, w} (yoneda.obj X) where

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
instance coyoneda_preservesLimits (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{t, w} (coyoneda.obj X) where

instance yonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (@yoneda C _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (coyoneda.obj K)
  infer_instance

noncomputable instance coyonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (@coyoneda C _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (yoneda.obj K)
  infer_instance

noncomputable instance yonedaFunctor_reflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@yoneda C _) := inferInstance

noncomputable instance coyonedaFunctor_reflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@coyoneda C _) := inferInstance

instance uliftYonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (uliftYoneda.{w'} : C ⥤ _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (coyoneda.obj K ⋙ uliftFunctor.{w'})
  infer_instance

instance [LocallySmall.{w'} C] :
    PreservesLimitsOfSize.{t, w} (shrinkYoneda.{w'} (C := C)) :=
  preservesLimits_of_evaluation _ (fun K ↦ ⟨fun {J _} ↦ by
    have := preservesLimitsOfShape_of_natIso (J := J) (Functor.associator _ _ _ ≪≫
      shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor.{w'} K).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{v}⟩)

namespace Functor

section Representable

variable (F : Cᵒᵖ ⥤ Type v) [F.IsRepresentable] {J : Type*} [Category* J]

instance representable_preservesLimit (G : J ⥤ Cᵒᵖ) :
    PreservesLimit G F :=
  preservesLimit_of_natIso _ F.reprW

variable (J) in
instance representable_preservesLimitsOfShape :
    PreservesLimitsOfShape J F where

instance representable_preservesLimits :
    PreservesLimitsOfSize.{t, w} F where

end Representable

section Corepresentable

variable (F : C ⥤ Type v) [F.IsCorepresentable] {J : Type*} [Category* J]

instance corepresentable_preservesLimit (G : J ⥤ C) :
    PreservesLimit G F :=
  preservesLimit_of_natIso _ F.coreprW

variable (J) in
instance corepresentable_preservesLimitsOfShape :
    PreservesLimitsOfShape J F where

instance corepresentable_preservesLimits :
    PreservesLimitsOfSize.{t, w} F where

end Corepresentable

end Functor

end CategoryTheory
