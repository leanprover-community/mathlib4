/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-!
# Exponentiable morphisms

We define an exponentiable morphism `f : I ⟶ J` to be a morphism with a functorial choice of
pullbacks, given by `ChosenPullbacksAlong f`, together with a right adjoint to
the pullback functor `ChosenPullbacksAlong.pulback f : Over J ⥤ Over I`. We call this right adjoint
the pushforward functor along `f`.

## Main results

- The identity morphisms are exponentiable.
- The composition of exponentiable morphisms is exponentiable.

### TODO

- Any pullback of an exponentiable morphism is exponentiable.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category MonoidalCategory Functor Adjunction

open ChosenPullbacksAlong

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
class ExponentiableMorphism {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] where
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

variable {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] [ExponentiableMorphism f]

/-- The dependent evaluation natural transformation as the counit of the adjunction. -/
def ev : pushforward f ⋙ pullback f ⟶ 𝟭 _ :=
  pullbackAdjPushforward f |>.counit

/-- The dependent coevaluation natural transformation as the unit of the adjunction. -/
def coev : 𝟭 _ ⟶ pullback f ⋙ pushforward f :=
  pullbackAdjPushforward f |>.unit

@[simp]
theorem ev_def : ev f = (pullbackAdjPushforward f).counit :=
  rfl

@[simp]
theorem coev_def : coev f = (pullbackAdjPushforward f).unit :=
  rfl

theorem ev_naturality {X Y : Over I} (g : X ⟶ Y) :
    (pullback f).map ((pushforward f).map g) ≫ (ev f).app Y = (ev f).app X ≫ g :=
  ev f |>.naturality g

theorem coev_naturality {X Y : Over J} (g : X ⟶ Y) :
    g ≫ (coev f).app Y = (coev f).app X ≫ (pushforward f).map ((pullback f).map g) :=
  coev f |>.naturality g

/-- The first triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
theorem ev_coev (X : Over J) :
    (pullback f).map (coev f |>.app X) ≫ (ev f |>.app (pullback f |>.obj X)) =
    𝟙 (pullback f |>.obj X) :=
  pullbackAdjPushforward f |>.left_triangle_components X

/-- The second triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
theorem coev_ev (Y : Over I) :
    (coev f |>.app (pushforward f |>.obj Y)) ≫
    (pushforward f |>.map (ev f |>.app Y)) =
    𝟙 (pushforward f |>.obj Y) :=
  pullbackAdjPushforward f |>.right_triangle_components Y

variable {f}

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

instance : ChosenPullbacksAlong (Over.mk f).hom := by
  dsimp only [Over.mk_hom]
  infer_instance

instance OverMkHom : ExponentiableMorphism (Over.mk f).hom := by
  dsimp only [Over.mk_hom]
  infer_instance

end

section

/-- The identity morphisms `𝟙 _` are exponentiable. -/
@[simps]
def id (I : C) [ChosenPullbacksAlong (𝟙 I)] : ExponentiableMorphism (𝟙 I) :=
  ⟨𝟭 _, ofNatIsoLeft (F := 𝟭 _) Adjunction.id (pullbackId I).symm⟩

/-- Any pushforward of the identity morphism is naturally isomorphic to the identity functor. -/
def pushforwardId (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)] :
    pushforward (𝟙 I) ≅ 𝟭 (Over I) :=
  Adjunction.rightAdjointUniq (pullbackAdjPushforward (𝟙 I)) (id I).pullbackAdjPushforward

/-- The composition of exponentiable morphisms is exponentiable. -/
@[simps]
def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    ExponentiableMorphism (f ≫ g) :=
  ⟨pushforward f ⋙ pushforward g,
    ofNatIsoLeft (pullbackAdjPushforward g |>.comp <| pullbackAdjPushforward f)
    (pullbackComp f g).symm⟩

/-- The natural isomorphism between pushforward of the composition and the composition of
pushforward functors. -/
def pushforwardComp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    pushforward (C:= C) (f ≫ g) ≅ pushforward f ⋙ pushforward g :=
  Adjunction.rightAdjointUniq (pullbackAdjPushforward (f ≫ g)) ((comp f g).pullbackAdjPushforward)

end

end ExponentiableMorphism

end CategoryTheory
