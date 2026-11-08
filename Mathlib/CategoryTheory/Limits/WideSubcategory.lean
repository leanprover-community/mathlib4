/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# ...


-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C] (W : MorphismProperty C)
  [W.IsMultiplicative] {J : Type*} [Category* J]

structure RespectsColimitWideSubcategory (F : J ⥤ WideSubcategory W) : Prop where
  prop_ι_app {c : Cocone (F ⋙ wideSubcategoryInclusion W)} (hc : IsColimit c) (j : J) :
    W (c.ι.app j)
  prop_desc {c : Cocone (F ⋙ wideSubcategoryInclusion W)} (hc : IsColimit c) (t : Cocone F) :
    W (hc.desc ((wideSubcategoryInclusion W).mapCocone t))

namespace RespectsColimitWideSubcategory

variable {W} {F : J ⥤ WideSubcategory W} (hF : W.RespectsColimitWideSubcategory F)
  {c : Cocone (F ⋙ wideSubcategoryInclusion W)} (hc : IsColimit c)

@[expose, simps, implicit_reducible]
def cocone : Cocone F where
  pt := .mk c.pt
  ι.app j := .mk (c.ι.app j) (hF.prop_ι_app hc j)
  ι.naturality j₁ j₂ f := by ext; simpa using c.w f

def isColimitCocone : IsColimit (hF.cocone hc) where
  desc t := .mk _ (hF.prop_desc hc t)
  fac t j := by ext; exact hc.fac ((wideSubcategoryInclusion W).mapCocone t) j
  uniq t m hm := by
    ext
    refine hc.hom_ext (fun j ↦ ?_)
    simp [dsimp% congr($(hm j).hom),
      dsimp% hc.fac ((wideSubcategoryInclusion W).mapCocone t) j]

variable [HasColimit (F ⋙ wideSubcategoryInclusion W)]

include hF

lemma hasColimit : HasColimit F :=
  ⟨_, hF.isColimitCocone (colimit.isColimit _)⟩

lemma preservesColimit : PreservesColimit F (wideSubcategoryInclusion W) :=
  preservesColimit_of_preserves_colimit_cocone (hF.isColimitCocone (colimit.isColimit _))
    (colimit.isColimit _)

end RespectsColimitWideSubcategory

variable (J) in
abbrev RespectsColimitsOfShapeWideSubcategory :=
  ∀ (F : J ⥤ WideSubcategory W), W.RespectsColimitWideSubcategory F

namespace RespectsColimitsOfShapeWideSubcategory

variable {W} (hW : W.RespectsColimitsOfShapeWideSubcategory J)
  [HasColimitsOfShape J C]

include hW

lemma hasColimitsOfShape :
    HasColimitsOfShape J (WideSubcategory W) where
  has_colimit F := (hW F).hasColimit

lemma preservesColimitsOfShape :
    PreservesColimitsOfShape J (wideSubcategoryInclusion W) where
  preservesColimit {F} := (hW F).preservesColimit

end RespectsColimitsOfShapeWideSubcategory

end CategoryTheory.MorphismProperty
