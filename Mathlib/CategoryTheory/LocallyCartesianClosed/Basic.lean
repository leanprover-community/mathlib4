/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/

import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Adjunction.Over

/-!
# Locally cartesian closed categories

There are several equivalent definitions of locally
cartesian closed categories.

1. A locally cartesian closed category is a category C such that all
the slices `Over I` are cartesian closed categories.

2. Equivalently, a locally cartesian closed category `C` is a category with pullbacks such that
each base change functor has a right adjoint, called the pushforward functor.

In this file we prove the equivalence of these conditions.

We also show that a locally cartesian closed category with a terminal object is cartesian closed.

-/

noncomputable section

namespace CategoryTheory

open CategoryTheory Category Limits Functor Adjunction Over

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
class ExponentiableMorphism [HasPullbacks C] {I J : C} (f : I ⟶ J) where
  /-- The pushforward functor -/
  pushforward : Over I ⥤ Over J
  /-- The pushforward functor is right adjoint to the pullback functor -/
  adj : pullback f ⊣ pushforward := by infer_instance

namespace ExponentiableMorphism

variable [HasPullbacks C]

#check Over.pullback

/-- The identity morphisms `𝟙` are exponentiable. -/
def id {I : C} : ExponentiableMorphism (𝟙 I) where
  pushforward := 𝟭 (Over I)
  adj := ofNatIsoLeft (F:= 𝟭 _) Adjunction.id (pullbackId).symm

/-- The composition of exponentiable morphisms is exponentiable. -/
def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
  ExponentiableMorphism (f ≫ g) where
  pushforward := (pushforward f) ⋙ (pushforward g)
  adj := ofNatIsoLeft (gexp.adj.comp fexp.adj) (pullbackComp f g).symm

/-- The conjugate isomorphism between pushforward functor the composition and the composition of
pushforward functors. -/
def pushforwardCompIso {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
  (comp f g).pushforward ≅ fexp.pushforward ⋙ gexp.pushforward  :=
  conjugateIsoEquiv (gexp.adj.comp fexp.adj) ((comp f g).adj) (pullbackComp f g)

attribute [local instance] monoidalOfChosenFiniteProducts
attribute [local instance] ChosenFiniteProducts.ofFiniteProducts
attribute [local instance] ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
-- attribute [local instance] hasFiniteWidePullbacks_of_hasFiniteLimits


/-- An arrow with a pushforward is exponentiable in the slice category. -/
instance exponentiableOverMk [HasFiniteWidePullbacks C] {X I : C} (f : X ⟶ I)
    [ExponentiableMorphism f] : Exponentiable (Over.mk f) where
  rightAdj := pullback f ⋙ pushforward f
  adj := by
    apply ofNatIsoLeft _ _
    · exact Over.pullback f ⋙ Over.map f
    · exact Adjunction.comp ExponentiableMorphism.adj (Over.mapPullbackAdj _)
    · sorry --exact natIsoTensorLeftOverMk f




end ExponentiableMorphism



attribute [local instance] monoidalOfChosenFiniteProducts



section

variable (C : Type u) [Category.{v} C]

attribute [local instance] hasFiniteWidePullbacks_of_hasFiniteLimits
attribute [local instance] ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

class LCC (C : Type u) [Category.{v} C] [HasFiniteWidePullbacks C] where
  over_cc : Π (I : C), CartesianClosed (Over I)
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj {X Y : C} (f : X ⟶ Y) : Over.pullback f ⊣ pushforward f := by infer_instance




end




end CategoryTheory
