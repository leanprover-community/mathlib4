/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy

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

end IsRightProper

end HomotopicalAlgebra
