/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Lifting properties and pushout-products / pullback-homs

Various equivalent lifting properties involving pushout-products and pullback-homs. For
`f : A ⟶ B`, `g : K ⟶ L`, `h : X ⟶ Y` in a monoidal closed category with pushouts and pullbacks,
`f □ g` lifts against `h` if and only if `g` lifts against `f ⋔ h`.

Special cases are considered when any of `A = ∅`, `K = ∅`, or `Y = ⋆` are true.

## References

* [Charles Rezk, *Introduction to Quasi-categories*, Proposition 21.5][Rezk2022]
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

namespace MonoidalCategory.Arrow

namespace PushoutProduct

/-- `X □ Y` lifts against `Z` if and only if `Y` lifts against `X ⋔ Z`. -/
lemma hasLiftingProperty_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] {X Y Z : Arrow C} :
    HasLiftingProperty (X □ Y).hom Z.hom ↔ HasLiftingProperty Y.hom ((.op X) ⋔ Z).hom :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

/-- `X □ Y` lifts against `Z` if and only if `X` lifts against `Y ⋔ Z`. -/
lemma hasLiftingProperty_iff' [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] {X Y Z : Arrow C} :
    HasLiftingProperty (X □ Y).hom Z.hom ↔ HasLiftingProperty X.hom ((.op Y) ⋔ Z).hom := by
  rw [← hasLiftingProperty_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) _

/-- `f □ g` lifts against `h` if and only if `g` lifts against `f ⋔ h`. -/
lemma hasLiftingProperty_mk_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
    HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty g ((.op f) ⋔ h).hom :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

/-- `f □ g` lifts against `h` if and only if `f` lifts against `g ⋔ h`. -/
lemma hasLiftingProperty_mk_iff' [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
    HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty f ((.op g) ⋔ h).hom := by
  rw [← hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

/-- `(∅ ⟶ B) □ g` lifts against `X ⟶ Y` if and only if `g` lifts against `B ⟹ X ⟶ B ⟹ Y`. -/
lemma hasLiftingProperty_mk_isInitial_iff [HasPushouts C] [HasPullbacks C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {g : K ⟶ L} {h : X ⟶ Y}
    (i : IsInitial A) :
    HasLiftingProperty (i.to B □ g).hom h ↔
      HasLiftingProperty g ((ihom B).map h) := by
  change HasLiftingProperty (ofHasPushout ..).ι _ ↔ _
  rw [HasLiftingProperty.iff_of_arrow_iso_left (isInitialIso' _ _)]
  exact Adjunction.hasLiftingProperty_iff (ihom.adjunction B) g h

/-- `f □ (∅ ⟶ L)` lifts against `X ⟶ Y` if and only if `f` lifts against `L ⟹ X ⟶ L ⟹ Y`. -/
lemma hasLiftingProperty_mk_isInitial_iff' [HasPushouts C] [HasPullbacks C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B} {h : X ⟶ Y}
    (i : IsInitial K) :
    HasLiftingProperty (f □ i.to L).hom h ↔
      HasLiftingProperty f ((ihom L).map h) := by
  rw [← hasLiftingProperty_mk_isInitial_iff i]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

/-- `f □ g` lifts against `X ⟶ ⋆` if and only if `g` lifts against `B ⟹ X ⟶ A ⟹ X`. -/
lemma hasLiftingProperty_mk_isTerminal_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L}
    (t : IsTerminal Y) :
    HasLiftingProperty (f □ g).hom (t.from X) ↔
      HasLiftingProperty g ((MonoidalClosed.pre f).app X) := by
  rw [hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g (PullbackHom.isTerminalIso _ t)

/-- `(∅ ⟶ B) □ g` lifts against `X ⟶ ⋆` if and only if `g` lifts against `(B ⟹ X) ⟶ ⋆`. -/
lemma hasLiftingProperty_mk_isInitial_isTerminal_iff [HasPushouts C] [HasPullbacks C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {g : K ⟶ L}
    (i : IsInitial A) (t : IsTerminal Y) :
    HasLiftingProperty (i.to B □ g).hom (t.from X) ↔
      HasLiftingProperty g (t.from ((ihom B).obj X)) := by
  rw [hasLiftingProperty_mk_isInitial_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom B) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

/-- `f □ (∅ ⟶ L)` lifts against `X ⟶ ⋆` if and only if `f` lifts against `(L ⟹ X) ⟶ ⋆`. -/
lemma hasLiftingProperty_mk_isInitial_isTerminal_iff' [HasPushouts C] [HasPullbacks C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B}
    (i : IsInitial K) (t : IsTerminal Y) :
    HasLiftingProperty (f □ i.to L).hom (t.from X) ↔
      HasLiftingProperty f (t.from ((ihom L).obj X)) := by
  rw [hasLiftingProperty_mk_isInitial_iff']
  exact HasLiftingProperty.iff_of_arrow_iso_right f
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom L) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

end PushoutProduct

end MonoidalCategory.Arrow

end CategoryTheory
