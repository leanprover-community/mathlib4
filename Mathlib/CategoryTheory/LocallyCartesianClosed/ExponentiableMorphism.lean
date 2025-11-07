/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullback

/-!
# Exponentiable morphisms

We define an exponentiable morphism `f : I ⟶ J` to be a morphism with a chosen pullback functor
`Over J ⥤ Over I` together with a right adjoint, called the pushforward functor.

## Main results

- The identity morphisms are exponentiable.
- The composition of exponentiable morphisms is exponentiable.

### TODO

- The pullback of an exponentiable morphism is exponentiable.

-/

universe v u

namespace CategoryTheory

open Category MonoidalCategory Functor Adjunction

open Over hiding pullback mapPullbackAdj pullbackId pullbackComp

open ChosenPullback

attribute [local instance] CartesianMonoidalCategory.ofFiniteProducts

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
class ExponentiableMorphism {I J : C} (f : I ⟶ J) [Over.ChosenPullback f] where
  /-- The pushforward functor -/
  pushforward : Over I ⥤ Over J
  /-- The pushforward functor is right adjoint to the pullback functor -/
  pullbackAdjPushforward (f) : pullback f ⊣ pushforward

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
abbrev IsExponentiable [ChosenPullbacks C] : MorphismProperty C :=
  fun _ _ f ↦ IsLeftAdjoint (pullback f)

namespace ExponentiableMorphism

instance isExponentiable [ChosenPullbacks C] {I J : C} (f : I ⟶ J) [ExponentiableMorphism f] :
  IsExponentiable f := ⟨pushforward f, ⟨pullbackAdjPushforward f⟩⟩

section

variable {I J : C} (f : I ⟶ J) [ChosenPullback f] [ExponentiableMorphism f]

/-- The dependent evaluation natural transformation as the counit of the adjunction. -/
abbrev ev : pushforward f ⋙ pullback f ⟶ 𝟭 _ :=
  pullbackAdjPushforward f |>.counit

/-- The dependent coevaluation natural transformation as the unit of the adjunction. -/
abbrev coev : 𝟭 _ ⟶ pullback f ⋙ pushforward f :=
  pullbackAdjPushforward f |>.unit

variable {f}

/-- The first triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
theorem ev_coev (X : Over J) :
    (pullback f).map (pullbackAdjPushforward f |>.unit.app X) ≫
    (pullbackAdjPushforward f |>.counit.app (pullback f |>.obj X)) =
    𝟙 (pullback f |>.obj X) :=
  pullbackAdjPushforward f |>.left_triangle_components X

/-- The second triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
theorem coev_ev (Y : Over I) :
    (pullbackAdjPushforward f |>.unit.app (pushforward f |>.obj Y)) ≫
    (pushforward f |>.map (pullbackAdjPushforward f |>.counit.app Y)) =
    𝟙 (pushforward f |>.obj Y) :=
  pullbackAdjPushforward f |>.right_triangle_components Y

/-- The currying of `(pullback f).obj A ⟶ X` in `Over I` to a morphism `A ⟶ (pushforward f).obj X`
in `Over J`. -/
def pushforwardCurry {X : Over I} {A : Over J}
    (u : (pullback f).obj A ⟶ X) :
    A ⟶ (pushforward f).obj X :=
  pullbackAdjPushforward f |>.homEquiv A X u

/-- The uncurrying of `A ⟶ (pushforward f).obj X` in `Over J` to a morphism
`(Over.pullback f).obj A ⟶ X` in `Over I`. -/
def pushforwardUncurry {X : Over I} {A : Over J}
    (v : A ⟶ (pushforward f).obj X) :
    (pullback f).obj A ⟶ X :=
  pullbackAdjPushforward f |>.homEquiv A X |>.invFun v

theorem homEquiv_apply_eq {X : Over I} {A : Over J} (u : (pullback f).obj A ⟶ X) :
    (pullbackAdjPushforward f |>.homEquiv _ _) u = pushforwardCurry u :=
  rfl

theorem homEquiv_symm_apply_eq {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    (pullbackAdjPushforward f |>.homEquiv _ _).symm v = pushforwardUncurry v :=
  rfl

theorem pushforward_uncurry_curry {X : Over I} {A : Over J}
    (u : (pullback f).obj A ⟶ X) :
    pushforwardUncurry (pushforwardCurry u) = u :=
  pullbackAdjPushforward f |>.homEquiv A X |>.left_inv u

theorem pushforward_curry_uncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    pushforwardCurry (pushforwardUncurry v) = v :=
  pullbackAdjPushforward f |>.homEquiv A X |>.right_inv v

instance : ChosenPullback (Over.mk f).hom := by
  dsimp only [mk_hom]
  infer_instance

instance OverMkHom : ExponentiableMorphism (Over.mk f).hom := by
  dsimp only [mk_hom]
  infer_instance

end

section

attribute [local instance] ChosenPullback.id

attribute [local instance] ChosenPullback.comp

/-- The identity morphisms `𝟙 _` are exponentiable. -/
@[simps]
instance id (I : C) : ExponentiableMorphism (𝟙 I) :=
  ⟨𝟭 _, ofNatIsoLeft (F:= 𝟭 _) Adjunction.id (pullbackId I).symm⟩

/-- The pushforward of the identity is naturally isomorphic to the identity functor. -/
def pushforwardIdIso (I : C) : pushforward (𝟙 I) ≅ 𝟭 (Over I) := Iso.refl _

/-- The composition of exponentiable morphisms is exponentiable. -/
@[simps]
instance comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullback f] [ChosenPullback g]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    ExponentiableMorphism (f ≫ g) :=
  ⟨pushforward f ⋙ pushforward g,
    ofNatIsoLeft (pullbackAdjPushforward g |>.comp <| pullbackAdjPushforward f)
    (pullbackComp f g).symm⟩

/-- The natural isomorphism between pushforward of the composition and the composition of
pushforward functors. -/
def pushforwardCompIso {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullback f] [ChosenPullback g]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    pushforward (f ≫ g) ≅ pushforward f ⋙ pushforward g :=
  Iso.refl _

end

end ExponentiableMorphism

end CategoryTheory
