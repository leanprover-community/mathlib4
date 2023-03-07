/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.shapes.disjoint_coproduct
! leanprover-community/mathlib commit c9c9fa15fec7ca18e9ec97306fb8764bfe988a7e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks

/-!
# Disjoint coproducts

Defines disjoint coproducts: coproducts where the intersection is initial and the coprojections
are monic.
Shows that a category with disjoint coproducts is `initial_mono_class`.

## TODO

* Adapt this to the infinitary (small) version: This is one of the conditions in Giraud's theorem
  characterising sheaf topoi.
* Construct examples (and counterexamples?), eg Type, Vec.
* Define extensive categories, and show every extensive category has disjoint coproducts.
* Define coherent categories and use this to define positive coherent categories.
-/


universe v u u₂

namespace CategoryTheory

namespace Limits

open Category

variable {C : Type u} [Category.{v} C]

/-- Given any pullback diagram of the form

Z  ⟶  X₁
↓      ↓
X₂ ⟶  X

where `X₁ ⟶ X ← X₂` is a coproduct diagram, then `Z` is initial, and both `X₁ ⟶ X` and `X₂ ⟶ X`
are mono.
-/
class CoproductDisjoint (X₁ X₂ : C) where
  isInitialOfIsPullbackOfIsCoproduct :
    ∀ {X Z} {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} {f : Z ⟶ X₁} {g : Z ⟶ X₂}
      (cX : IsColimit (BinaryCofan.mk pX₁ pX₂)) {comm : f ≫ pX₁ = g ≫ pX₂},
      IsLimit (PullbackCone.mk _ _ comm) → IsInitial Z
  mono_inl : ∀ (X) (X₁ : X₁ ⟶ X) (X₂ : X₂ ⟶ X) (cX : IsColimit (BinaryCofan.mk X₁ X₂)), Mono X₁
  mono_inr : ∀ (X) (X₁ : X₁ ⟶ X) (X₂ : X₂ ⟶ X) (cX : IsColimit (BinaryCofan.mk X₁ X₂)), Mono X₂
#align category_theory.limits.coproduct_disjoint CategoryTheory.Limits.CoproductDisjoint

/-- If the coproduct of `X₁` and `X₂` is disjoint, then given any pullback square

Z  ⟶  X₁
↓      ↓
X₂ ⟶  X

where `X₁ ⟶ X ← X₂` is a coproduct, then `Z` is initial.
-/
def isInitialOfIsPullbackOfIsCoproduct {Z X₁ X₂ X : C} [CoproductDisjoint X₁ X₂] {pX₁ : X₁ ⟶ X}
    {pX₂ : X₂ ⟶ X} (cX : IsColimit (BinaryCofan.mk pX₁ pX₂)) {f : Z ⟶ X₁} {g : Z ⟶ X₂}
    {comm : f ≫ pX₁ = g ≫ pX₂} (cZ : IsLimit (PullbackCone.mk _ _ comm)) : IsInitial Z :=
  CoproductDisjoint.isInitialOfIsPullbackOfIsCoproduct cX cZ
#align category_theory.limits.is_initial_of_is_pullback_of_is_coproduct CategoryTheory.Limits.isInitialOfIsPullbackOfIsCoproduct

/-- If the coproduct of `X₁` and `X₂` is disjoint, then given any pullback square

Z  ⟶  X₁
↓       ↓
X₂ ⟶  X₁ ⨿ X₂

`Z` is initial.
-/
noncomputable def isInitialOfIsPullbackOfCoproduct {Z X₁ X₂ : C} [HasBinaryCoproduct X₁ X₂]
    [CoproductDisjoint X₁ X₂] {f : Z ⟶ X₁} {g : Z ⟶ X₂}
    {comm : f ≫ (coprod.inl : X₁ ⟶ _ ⨿ X₂) = g ≫ coprod.inr}
    (cZ : IsLimit (PullbackCone.mk _ _ comm)) : IsInitial Z :=
  CoproductDisjoint.isInitialOfIsPullbackOfIsCoproduct (coprodIsCoprod _ _) cZ
#align category_theory.limits.is_initial_of_is_pullback_of_coproduct CategoryTheory.Limits.isInitialOfIsPullbackOfCoproduct

/-- If the coproduct of `X₁` and `X₂` is disjoint, then provided `X₁ ⟶ X ← X₂` is a coproduct the
pullback is an initial object:

        X₁
        ↓
X₂ ⟶  X
-/
noncomputable def isInitialOfPullbackOfIsCoproduct {X X₁ X₂ : C} [CoproductDisjoint X₁ X₂]
    {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} [HasPullback pX₁ pX₂] (cX : IsColimit (BinaryCofan.mk pX₁ pX₂)) :
    IsInitial (pullback pX₁ pX₂) :=
  CoproductDisjoint.isInitialOfIsPullbackOfIsCoproduct cX (pullbackIsPullback _ _)
#align category_theory.limits.is_initial_of_pullback_of_is_coproduct CategoryTheory.Limits.isInitialOfPullbackOfIsCoproduct

/-- If the coproduct of `X₁` and `X₂` is disjoint, the pullback of `X₁ ⟶ X₁ ⨿ X₂` and `X₂ ⟶ X₁ ⨿ X₂`
is initial.
-/
noncomputable def isInitialOfPullbackOfCoproduct {X₁ X₂ : C} [HasBinaryCoproduct X₁ X₂]
    [CoproductDisjoint X₁ X₂] [HasPullback (coprod.inl : X₁ ⟶ _ ⨿ X₂) coprod.inr] :
    IsInitial (pullback (coprod.inl : X₁ ⟶ _ ⨿ X₂) coprod.inr) :=
  isInitialOfIsPullbackOfCoproduct (pullbackIsPullback _ _)
#align category_theory.limits.is_initial_of_pullback_of_coproduct CategoryTheory.Limits.isInitialOfPullbackOfCoproduct

instance {X₁ X₂ : C} [HasBinaryCoproduct X₁ X₂] [CoproductDisjoint X₁ X₂] :
    Mono (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) :=
  CoproductDisjoint.mono_inl _ _ _ (coprodIsCoprod _ _)

instance {X₁ X₂ : C} [HasBinaryCoproduct X₁ X₂] [CoproductDisjoint X₁ X₂] :
    Mono (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) :=
  CoproductDisjoint.mono_inr _ _ _ (coprodIsCoprod _ _)

/-- `C` has disjoint coproducts if every coproduct is disjoint. -/
class CoproductsDisjoint (C : Type u) [Category.{v} C] where
  CoproductDisjoint : ∀ X Y : C, CoproductDisjoint X Y
#align category_theory.limits.coproducts_disjoint CategoryTheory.Limits.CoproductsDisjoint

attribute [instance] coproducts_disjoint.coproduct_disjoint

/-- If `C` has disjoint coproducts, any morphism out of initial is mono. Note it isn't true in
general that `C` has strict initial objects, for instance consider the category of types and
partial functions. -/
theorem initialMonoClass_of_disjoint_coproducts [CoproductsDisjoint C] : InitialMonoClass C :=
  {
    isInitial_mono_from := fun I X hI =>
      CoproductDisjoint.mono_inl _ _ (𝟙 X)
        { desc := fun s : BinaryCofan _ _ => s.inr
          fac := fun s j =>
            Discrete.casesOn j fun j => WalkingPair.casesOn j (hI.hom_ext _ _) (id_comp _)
          uniq := fun (s : BinaryCofan _ _) m w =>
            (id_comp _).symm.trans (w ⟨WalkingPair.right⟩) } }
#align category_theory.limits.initial_mono_class_of_disjoint_coproducts CategoryTheory.Limits.initialMonoClass_of_disjoint_coproducts

end Limits

end CategoryTheory

