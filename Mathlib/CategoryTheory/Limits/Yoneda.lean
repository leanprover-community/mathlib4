/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.Util.AssertExists

#align_import category_theory.limits.yoneda from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `PUnit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/

open Opposite CategoryTheory Limits

universe t w v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type u} [Category.{v} C]

/-- The colimit cocone over `coyoneda.obj X`, with cocone point `PUnit`.
-/
@[simps]
def colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X) where
  pt := PUnit
  ι := { app := by aesop_cat }
#align category_theory.coyoneda.colimit_cocone CategoryTheory.Coyoneda.colimitCocone

/-- The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X) where
  desc s _ := s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    funext f
    convert congr_fun (s.w f).symm (𝟙 (unop X))
    simp only [coyoneda_obj_obj, Functor.const_obj_obj, types_comp_apply,
      coyoneda_obj_map, Category.id_comp]
  uniq s m w := by
    apply funext; rintro ⟨⟩
    dsimp
    rw [← w]
    simp
#align category_theory.coyoneda.colimit_cocone_is_colimit CategoryTheory.Coyoneda.colimitCoconeIsColimit

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
#align category_theory.coyoneda.colimit_coyoneda_iso CategoryTheory.Coyoneda.colimitCoyonedaIso

end Coyoneda

variable {C : Type u} [Category.{v} C]

open Limits

section

variable {J : Type w} [Category.{t} J]

/-- The cone of `F` corresponding to an element in `(F ⋙ yoneda.obj X).sections`. -/
@[simps]
def Limits.coneOfSectionCompYoneda (F : J ⥤ Cᵒᵖ) (X : C)
    (s : (F ⋙ yoneda.obj X).sections) : Cone F where
  pt := Opposite.op X
  π := compYonedaSectionsEquiv F X s

noncomputable instance yonedaPreservesLimit (F : J ⥤ Cᵒᵖ) (X : C) :
    PreservesLimit F (yoneda.obj X) where
  preserves {c} hc := Nonempty.some (by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨(hc.lift (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩)).unop,
      fun j => Quiver.Hom.op_inj (hc.fac (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) j),
      fun m hm => Quiver.Hom.op_inj
        (hc.uniq (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) _
          (fun j => Quiver.Hom.unop_inj (hm j)))⟩)

variable (J) in
noncomputable instance yonedaPreservesLimitsOfShape (X : C) :
    PreservesLimitsOfShape J (yoneda.obj X) where

/-- The yoneda embeddings jointly reflect limits. -/
def yonedaJointlyReflectsLimits (F : J ⥤ Cᵒᵖ) (c : Cone F)
    (hc : ∀ X : C, IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c where
  lift s := ((hc s.pt.unop).lift ((yoneda.obj s.pt.unop).mapCone s) (𝟙 _)).op
  fac s j := Quiver.Hom.unop_inj (by
    simpa using congr_fun ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 _))
  uniq s m hm := Quiver.Hom.unop_inj (by
    apply (Types.isLimitEquivSections (hc s.pt.unop)).injective
    ext j
    have eq := congr_fun ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 _)
    dsimp at eq
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    rw [eq, Category.comp_id, ← hm, unop_comp])
#align category_theory.yoneda_jointly_reflects_limits CategoryTheory.yonedaJointlyReflectsLimits

/-- The cone of `F` corresponding to an element in `(F ⋙ coyoneda.obj X).sections`. -/
@[simps]
def Limits.coneOfSectionCompCoyoneda (F : J ⥤ C) (X : Cᵒᵖ)
    (s : (F ⋙ coyoneda.obj X).sections) : Cone F where
  pt := X.unop
  π := compCoyonedaSectionsEquiv F X.unop s

noncomputable instance coyonedaPreservesLimit (F : J ⥤ C) (X : Cᵒᵖ) :
    PreservesLimit F (coyoneda.obj X) where
  preserves {c} hc := Nonempty.some (by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨hc.lift (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩), hc.fac _,
      hc.uniq (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩)⟩)

variable (J) in
noncomputable instance coyonedaPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (coyoneda.obj X) where

/-- The coyoneda embeddings jointly reflect limits. -/
def coyonedaJointlyReflectsLimits (F : J ⥤ C) (c : Cone F)
    (hc : ∀ X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c where
  lift s := (hc (op s.pt)).lift ((coyoneda.obj (op s.pt)).mapCone s) (𝟙 _)
  fac s j := by simpa using congr_fun ((hc (op s.pt)).fac
    ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 _)
  uniq s m hm := by
    apply (Types.isLimitEquivSections (hc (op s.pt))).injective
    ext j
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    have eq := congr_fun ((hc (op s.pt)).fac ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 _)
    dsimp at eq
    rw [eq, Category.id_comp, ← hm]
#align category_theory.coyoneda_jointly_reflects_limits CategoryTheory.coyonedaJointlyReflectsLimits

end

/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
noncomputable instance yonedaPreservesLimits (X : C) :
    PreservesLimitsOfSize.{t, w} (yoneda.obj X) where

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
noncomputable instance coyonedaPreservesLimits (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{t, w} (coyoneda.obj X) where
#align category_theory.coyoneda_preserves_limits CategoryTheory.coyonedaPreservesLimits

noncomputable instance yonedaFunctorPreservesLimits :
    PreservesLimitsOfSize.{t, w} (@yoneda C _) := by
  apply preservesLimitsOfEvaluation
  intro K
  change PreservesLimitsOfSize (coyoneda.obj K)
  infer_instance
#align category_theory.yoneda_functor_preserves_limits CategoryTheory.yonedaFunctorPreservesLimits

noncomputable instance coyonedaFunctorPreservesLimits :
    PreservesLimitsOfSize.{t, w} (@coyoneda C _) := by
  apply preservesLimitsOfEvaluation
  intro K
  change PreservesLimitsOfSize (yoneda.obj K)
  infer_instance
#align category_theory.coyoneda_functor_preserves_limits CategoryTheory.coyonedaFunctorPreservesLimits

noncomputable instance yonedaFunctorReflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@yoneda C _) := inferInstance
#align category_theory.yoneda_functor_reflects_limits CategoryTheory.yonedaFunctorReflectsLimits

noncomputable instance coyonedaFunctorReflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@coyoneda C _) := inferInstance
#align category_theory.coyoneda_functor_reflects_limits CategoryTheory.coyonedaFunctorReflectsLimits

namespace Functor

section Representable

variable (F : Cᵒᵖ ⥤ Type v) [F.Representable] {J : Type*} [Category J]

noncomputable instance representablePreservesLimit (G : J ⥤ Cᵒᵖ) :
    PreservesLimit G F :=
  preservesLimitOfNatIso _ F.reprW

variable (J) in
noncomputable instance representablePreservesLimitsOfShape :
    PreservesLimitsOfShape J F where

noncomputable instance representablePreservesLimits :
    PreservesLimitsOfSize.{t, w} F where

end Representable

section Corepresentable

variable (F : C ⥤ Type v) [F.Corepresentable] {J : Type*} [Category J]

noncomputable instance corepresentablePreservesLimit (G : J ⥤ C) :
    PreservesLimit G F :=
  preservesLimitOfNatIso _ F.coreprW

variable (J) in
noncomputable instance corepresentablePreservesLimitsOfShape :
    PreservesLimitsOfShape J F where

noncomputable instance corepresentablePreservesLimits :
    PreservesLimitsOfSize.{t, w} F where

end Corepresentable

end Functor

end CategoryTheory

assert_not_exists AddCommMonoid
