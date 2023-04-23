/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.preserves.functor_category
! leanprover-community/mathlib commit 7cd8adb7a9d7d0498d2e76c23cd4255f966899f5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Yoneda
import Mathbin.CategoryTheory.Limits.Presheaf

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
`(evaluation C D).obj k ⋙ prod.functor.obj (F.obj k) ≅ prod.functor.obj F ⋙ (evaluation C D).obj k`
-/
def FunctorCategory.prodPreservesColimits [HasBinaryProducts D] [HasColimits D]
    [∀ X : D, PreservesColimits (prod.functor.obj X)] (F : C ⥤ D) :
    PreservesColimits (prod.functor.obj F)
    where PreservesColimitsOfShape J 𝒥 :=
    {
      PreservesColimit := fun K =>
        {
          preserves := fun c t =>
            by
            apply evaluation_jointly_reflects_colimits _ fun k => _
            change is_colimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).mapCocone c)
            let this :=
              is_colimit_of_preserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t
            apply is_colimit.map_cocone_equiv _ this
            apply (nat_iso.of_components _ _).symm
            · intro G
              apply as_iso (prod_comparison ((evaluation C D).obj k) F G)
            · intro G G'
              apply prod_comparison_natural ((evaluation C D).obj k) (𝟙 F) } }
#align category_theory.functor_category.prod_preserves_colimits CategoryTheory.FunctorCategory.prodPreservesColimits

instance whiskeringLeftPreservesLimits [HasLimits D] (F : C ⥤ E) :
    PreservesLimits ((whiskeringLeft C E D).obj F) :=
  ⟨fun J hJ =>
    ⟨fun K =>
      ⟨fun c hc => by
        apply evaluation_jointly_reflects_limits
        intro Y
        change is_limit (((evaluation E D).obj (F.obj Y)).mapCone c)
        exact preserves_limit.preserves hc⟩⟩⟩
#align category_theory.whiskering_left_preserves_limits CategoryTheory.whiskeringLeftPreservesLimits

instance whiskeringRightPreservesLimitsOfShape {C : Type u} [Category C] {D : Type _}
    [Category.{u} D] {E : Type _} [Category.{u} E] {J : Type u} [SmallCategory J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun K =>
    ⟨fun c hc => by
      apply evaluation_jointly_reflects_limits
      intro k
      change is_limit (((evaluation _ _).obj k ⋙ F).mapCone c)
      exact preserves_limit.preserves hc⟩⟩
#align category_theory.whiskering_right_preserves_limits_of_shape CategoryTheory.whiskeringRightPreservesLimitsOfShape

instance whiskeringRightPreservesLimits {C : Type u} [Category C] {D : Type _} [Category.{u} D]
    {E : Type _} [Category.{u} E] (F : D ⥤ E) [HasLimits D] [PreservesLimits F] :
    PreservesLimits ((whiskeringRight C D E).obj F) :=
  ⟨⟩
#align category_theory.whiskering_right_preserves_limits CategoryTheory.whiskeringRightPreservesLimits

/-- If `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves limits of shape `J`, so will `F`. -/
noncomputable def preservesLimitOfLanPresesrvesLimit {C D : Type u} [SmallCategory C]
    [SmallCategory D] (F : C ⥤ D) (J : Type u) [SmallCategory J]
    [PreservesLimitsOfShape J (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u)] : PreservesLimitsOfShape J F :=
  by
  apply preserves_limits_of_shape_of_reflects_of_preserves F yoneda
  exact preserves_limits_of_shape_of_nat_iso (comp_yoneda_iso_yoneda_comp_Lan F).symm
  infer_instance
#align category_theory.preserves_limit_of_Lan_presesrves_limit CategoryTheory.preservesLimitOfLanPresesrvesLimit

end CategoryTheory

