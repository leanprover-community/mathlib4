/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Presheaf

#align_import category_theory.limits.preserves.functor_category from "leanprover-community/mathlib"@"39478763114722f0ec7613cb2f3f7701f9b86c8d"

/-!
# Preservation of (co)limits in the functor category

* Show that if `X ⨯ -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -`
for `F : C ⥤ D` preserves colimits.

The idea of the proof is simply that products and colimits in the functor category are computed
pointwise, so pointwise preservation implies general preservation.

* Show that `F ⋙ -` preserves limits if the target category has limits.
* Show that `F : C ⥤ D` preserves limits of a certain shape
  if `Lan F.op : Cᵒᵖ ⥤ Type*` preserves such limits.

# References

https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits#preservation_by_functor_categories_and_localizations

-/


universe v₁ v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v₁} C]

variable {D : Type u₂} [Category.{u} D]

variable {E : Type u} [Category.{v₂} E]

/-- If `X × -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -` for
`F : C ⥤ D` also preserves colimits.

Note this is (mathematically) a special case of the statement that
"if limits commute with colimits in `D`, then they do as well in `C ⥤ D`"
but the story in Lean is a bit more complex, and this statement isn't directly a special case.
That is, even with a formalised proof of the general statement, there would still need to be some
work to convert to this version: namely, the natural isomorphism
`(evaluation C D).obj k ⋙ prod.functor.obj (F.obj k) ≅
  prod.functor.obj F ⋙ (evaluation C D).obj k`
-/
def FunctorCategory.prodPreservesColimits [HasBinaryProducts D] [HasColimits D]
    [∀ X : D, PreservesColimits (prod.functor.obj X)] (F : C ⥤ D) :
    PreservesColimits (prod.functor.obj F)
    where preservesColimitsOfShape {J : Type u} [Category.{u, u} J] :=
    {
      preservesColimit := fun {K : J ⥤ C ⥤ D} =>
        ( {
          preserves := fun {c : Cocone K} (t : IsColimit c) => by
            apply evaluationJointlyReflectsColimits _ fun {k} => ?_
            -- ⊢ IsColimit (((evaluation C D).obj k).mapCocone ((prod.functor.obj F).mapCocon …
            change IsColimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).mapCocone c)
            -- ⊢ IsColimit ((prod.functor.obj F ⋙ (evaluation C D).obj k).mapCocone c)
            let this :=
              isColimitOfPreserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t
            apply IsColimit.mapCoconeEquiv _ this
            -- ⊢ (evaluation C D).obj k ⋙ prod.functor.obj (F.obj k) ≅ prod.functor.obj F ⋙ ( …
            apply (NatIso.ofComponents _ _).symm
            -- ⊢ (X : C ⥤ D) → (prod.functor.obj F ⋙ (evaluation C D).obj k).obj X ≅ ((evalua …
            · intro G
              -- ⊢ (prod.functor.obj F ⋙ (evaluation C D).obj k).obj G ≅ ((evaluation C D).obj  …
              apply asIso (prodComparison ((evaluation C D).obj k) F G)
              -- 🎉 no goals
            · intro G G'
              -- ⊢ ∀ (f : G ⟶ G'), (prod.functor.obj F ⋙ (evaluation C D).obj k).map f ≫ (asIso …
              apply prodComparison_natural ((evaluation C D).obj k) (𝟙 F) } ) }
              -- 🎉 no goals
#align category_theory.functor_category.prod_preserves_colimits CategoryTheory.FunctorCategory.prodPreservesColimits

instance whiskeringLeftPreservesLimits [HasLimits D] (F : C ⥤ E) :
    PreservesLimits ((whiskeringLeft C E D).obj F) :=
  ⟨fun {J} [hJ : Category J] =>
    ⟨fun {K} =>
      ⟨fun c {hc} => by
        apply evaluationJointlyReflectsLimits
        -- ⊢ (k : C) → IsLimit (((evaluation C D).obj k).mapCone (((whiskeringLeft C E D) …
        intro Y
        -- ⊢ IsLimit (((evaluation C D).obj Y).mapCone (((whiskeringLeft C E D).obj F).ma …
        change IsLimit (((evaluation E D).obj (F.obj Y)).mapCone c)
        -- ⊢ IsLimit (((evaluation E D).obj (F.obj Y)).mapCone c)
        exact PreservesLimit.preserves hc⟩⟩⟩
        -- 🎉 no goals
#align category_theory.whiskering_left_preserves_limits CategoryTheory.whiskeringLeftPreservesLimits

instance whiskeringRightPreservesLimitsOfShape {C : Type u} [Category C] {D : Type*}
    [Category.{u} D] {E : Type*} [Category.{u} E] {J : Type u} [SmallCategory J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => by
      apply evaluationJointlyReflectsLimits _ (fun k => ?_)
      -- ⊢ IsLimit (((evaluation C E).obj k).mapCone (((whiskeringRight C D E).obj F).m …
      change IsLimit (((evaluation _ _).obj k ⋙ F).mapCone c)
      -- ⊢ IsLimit (((evaluation C D).obj k ⋙ F).mapCone c)
      exact PreservesLimit.preserves hc⟩⟩
      -- 🎉 no goals
#align category_theory.whiskering_right_preserves_limits_of_shape CategoryTheory.whiskeringRightPreservesLimitsOfShape

instance whiskeringRightPreservesLimits {C : Type u} [Category C] {D : Type*} [Category.{u} D]
    {E : Type*} [Category.{u} E] (F : D ⥤ E) [HasLimits D] [PreservesLimits F] :
    PreservesLimits ((whiskeringRight C D E).obj F) :=
  ⟨inferInstance⟩
#align category_theory.whiskering_right_preserves_limits CategoryTheory.whiskeringRightPreservesLimits

-- porting note: fixed spelling mistake in def
/-- If `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves limits of shape `J`, so will `F`. -/
noncomputable def preservesLimitOfLanPreservesLimit {C D : Type u} [SmallCategory C]
    [SmallCategory D] (F : C ⥤ D) (J : Type u) [SmallCategory J]
    [PreservesLimitsOfShape J (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u)] : PreservesLimitsOfShape J F := by
  apply @preservesLimitsOfShapeOfReflectsOfPreserves _ _ _ _ _ _ _ _ F yoneda ?_
  -- ⊢ PreservesLimitsOfShape J (F ⋙ yoneda)
  exact preservesLimitsOfShapeOfNatIso (compYonedaIsoYonedaCompLan F).symm
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.preserves_limit_of_Lan_preserves_limit CategoryTheory.preservesLimitOfLanPreservesLimit

end CategoryTheory
