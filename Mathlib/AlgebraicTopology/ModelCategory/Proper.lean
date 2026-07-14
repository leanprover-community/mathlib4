/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Proper model categories

## References
* [Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory][goerss-jardine-2009]
* https://ncatlab.org/nlab/show/proper+model+category

-/

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type*} [Category* C]

variable (C) in
/-- A model category is right proper when the pullback of a weak equivalence
by a fibration is a weak equivalence. -/
class IsRightProper [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] : Prop where
  isStableUnderBaseChangeAlong {E B : C} (p : E ⟶ B) [Fibration p] :
    (weakEquivalences C).IsStableUnderBaseChangeAlong p

namespace IsRightProper

attribute [instance] isStableUnderBaseChangeAlong

variable [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] [IsRightProper C]

variable {E' B' E B : C}
lemma weakEquivalence {t : E' ⟶ B'} {l : E' ⟶ E} {r : B' ⟶ B} {b : E ⟶ B}
    [WeakEquivalence r] [Fibration b] (sq : IsPullback t l r b) :
    WeakEquivalence l :=
  (weakEquivalence_iff ..).2
    (MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
      sq (mem_weakEquivalences r))

lemma weakEquivalence' {t : E' ⟶ E} {l : E' ⟶ B'} {r : E ⟶ B} {b : B' ⟶ B}
    [WeakEquivalence b] [Fibration r] (sq : IsPullback t l r b) :
    WeakEquivalence t :=
  weakEquivalence sq.flip

instance (p : E ⟶ B) (w : B' ⟶ B) [Fibration p] [WeakEquivalence w]
    [HasPullback w p] :
    WeakEquivalence (pullback.snd w p) :=
  weakEquivalence (IsPullback.of_hasPullback w p)

instance (p : E ⟶ B) (w : B' ⟶ B) [Fibration p] [WeakEquivalence w]
    [HasPullback p w] :
    WeakEquivalence (pullback.fst p w) :=
  weakEquivalence' (IsPullback.of_hasPullback p w)

set_option backward.isDefEq.respectTransparency false in
instance [(fibrations C).IsStableUnderBaseChange]
    (p : E ⟶ B) {X Y : C} (w : X ⟶ Y) (a : Y ⟶ B) [HasPullback p a] [HasPullback p (w ≫ a)]
    [WeakEquivalence w] [Fibration p] :
    WeakEquivalence (pullback.map _ _ _ _ (𝟙 _) w (𝟙 _) (by simp) (by simp) :
      pullback p (w ≫ a) ⟶ pullback p a) :=
  have :
      IsPullback (pullback.map _ _ _ _ (𝟙 _) w (𝟙 _) (by simp) (by simp))
        (pullback.snd p (w ≫ a)) (pullback.snd p a) w :=
    IsPullback.of_right (by simpa using IsPullback.of_hasPullback p (w ≫ a)) (by cat_disch)
      (IsPullback.of_hasPullback p a)
  weakEquivalence' this

set_option backward.isDefEq.respectTransparency false in
instance [(fibrations C).IsStableUnderBaseChange]
    (p : E ⟶ B) {X Y : C} (w : X ⟶ Y) (a : Y ⟶ B) [HasPullback a p] [HasPullback (w ≫ a) p]
    [WeakEquivalence w] [Fibration p] :
    WeakEquivalence (pullback.map _ _ _ _ w (𝟙 _) (𝟙 _) (by simp) (by simp) :
      pullback (w ≫ a) p ⟶ pullback a p) :=
  have :
      IsPullback (pullback.fst (w ≫ a) p)
        (pullback.map _ _ _ _ w (𝟙 _) (𝟙 _) (by simp) (by simp)) w (pullback.fst a p ) :=
    IsPullback.of_bot (by simpa using IsPullback.of_hasPullback (w ≫ a) p) (by cat_disch)
      (IsPullback.of_hasPullback a p)
  weakEquivalence this

end IsRightProper

end HomotopicalAlgebra
