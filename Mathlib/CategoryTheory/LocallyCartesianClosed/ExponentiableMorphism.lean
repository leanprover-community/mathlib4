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
the pullback functor `ChosenPullbacksAlong.pullback f : Over J ⥤ Over I`. We call this right adjoint
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
  pullbackPushforwardAdj (f) : pullback f ⊣ pushforward

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
abbrev IsExponentiable [ChosenPullbacks C] : MorphismProperty C :=
  fun _ _ f ↦ IsLeftAdjoint (pullback f)

namespace ExponentiableMorphism

instance isExponentiable [ChosenPullbacks C] {I J : C} (f : I ⟶ J) [ExponentiableMorphism f] :
  IsExponentiable f := ⟨pushforward f, ⟨pullbackPushforwardAdj f⟩⟩

section

variable {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] [ExponentiableMorphism f]

/-- The dependent evaluation natural transformation as the counit of the adjunction. -/
def ev : pushforward f ⋙ pullback f ⟶ 𝟭 _ :=
  pullbackPushforwardAdj f |>.counit

/-- The dependent coevaluation natural transformation as the unit of the adjunction. -/
def coev : 𝟭 _ ⟶ pullback f ⋙ pushforward f :=
  pullbackPushforwardAdj f |>.unit

@[simp]
theorem ev_def : ev f = (pullbackPushforwardAdj f).counit :=
  rfl

@[simp]
theorem coev_def : coev f = (pullbackPushforwardAdj f).unit :=
  rfl

@[reassoc]
theorem ev_naturality {X Y : Over I} (g : X ⟶ Y) :
    (pullback f).map ((pushforward f).map g) ≫ (ev f).app Y = (ev f).app X ≫ g :=
  ev f |>.naturality g

@[reassoc]
theorem coev_naturality {X Y : Over J} (g : X ⟶ Y) :
    g ≫ (coev f).app Y = (coev f).app X ≫ (pushforward f).map ((pullback f).map g) :=
  coev f |>.naturality g

/-- The first triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
theorem ev_coev (X : Over J) :
    (pullback f).map (coev f |>.app X) ≫ (ev f |>.app (pullback f |>.obj X)) =
    𝟙 (pullback f |>.obj X) :=
  pullbackPushforwardAdj f |>.left_triangle_components X

/-- The second triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
theorem coev_ev (Y : Over I) :
    (coev f |>.app (pushforward f |>.obj Y)) ≫
    (pushforward f |>.map (ev f |>.app Y)) =
    𝟙 (pushforward f |>.obj Y) :=
  pullbackPushforwardAdj f |>.right_triangle_components Y

variable {f}

/-- The currying of `(pullback f).obj A ⟶ X` in `Over I` to a morphism `A ⟶ (pushforward f).obj X`
in `Over J`. -/
def pushforwardCurry {X : Over I} {A : Over J}
    (u : (pullback f).obj A ⟶ X) :
    A ⟶ (pushforward f).obj X :=
  pullbackPushforwardAdj f |>.homEquiv A X u

/-- The uncurrying of `A ⟶ (pushforward f).obj X` in `Over J` to a morphism
`(Over.pullback f).obj A ⟶ X` in `Over I`. -/
def pushforwardUncurry {X : Over I} {A : Over J}
    (v : A ⟶ (pushforward f).obj X) :
    (pullback f).obj A ⟶ X :=
  pullbackPushforwardAdj f |>.homEquiv A X |>.invFun v

theorem homEquiv_apply_eq {X : Over I} {A : Over J} (u : (pullback f).obj A ⟶ X) :
    (pullbackPushforwardAdj f |>.homEquiv _ _) u = pushforwardCurry u :=
  rfl

theorem homEquiv_symm_apply_eq {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    (pullbackPushforwardAdj f |>.homEquiv _ _).symm v = pushforwardUncurry v :=
  rfl

theorem pushforward_uncurry_curry {X : Over I} {A : Over J}
    (u : (pullback f).obj A ⟶ X) :
    pushforwardUncurry (pushforwardCurry u) = u :=
  pullbackPushforwardAdj f |>.homEquiv A X |>.left_inv u

theorem pushforward_curry_uncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    pushforwardCurry (pushforwardUncurry v) = v :=
  pullbackPushforwardAdj f |>.homEquiv A X |>.right_inv v

instance : ChosenPullbacksAlong (Over.mk f).hom :=
  inferInstanceAs <| ChosenPullbacksAlong f

instance OverMkHom : ExponentiableMorphism (Over.mk f).hom :=
  inferInstanceAs <| ExponentiableMorphism f

end

section

/-- The identity morphisms `𝟙 _` are exponentiable. -/
@[implicit_reducible]
def id (I : C) [ChosenPullbacksAlong (𝟙 I)] : ExponentiableMorphism (𝟙 I) :=
  ⟨𝟭 _, ofNatIsoLeft (F := 𝟭 _) Adjunction.id (pullbackId I).symm⟩

theorem id_pushforward (I : C) [ChosenPullbacksAlong (𝟙 I)] :
    (id I).pushforward = 𝟭 (Over I) := by
  dsimp +instances only [id]

/-- Any pushforward of the identity morphism is naturally isomorphic to the identity functor. -/
def pushforwardId (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)] :
    pushforward (𝟙 I) ≅ 𝟭 (Over I) :=
  Adjunction.rightAdjointUniq (pullbackPushforwardAdj (𝟙 I)) (id I).pullbackPushforwardAdj

@[reassoc (attr := simp)]
theorem unit_pushforwardId_hom (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)] :
    (pullbackPushforwardAdj (𝟙 I)).unit ≫
      (pullback (𝟙 I)).whiskerLeft (pushforwardId I).hom =
      (id I).pullbackPushforwardAdj.unit := by
  rw [pushforwardId, Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
theorem pushforwardId_hom_counit (I : C) [ChosenPullbacksAlong (𝟙 I)]
    [ExponentiableMorphism (𝟙 I)] :
    Functor.whiskerRight (pushforwardId I).hom (pullback (𝟙 I)) ≫
      (id I).pullbackPushforwardAdj.counit =
      (pullbackPushforwardAdj (𝟙 I)).counit := by
  rw [pushforwardId, Adjunction.rightAdjointUniq_hom_counit]

/-- The composition of exponentiable morphisms is exponentiable. -/
@[implicit_reducible]
def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    ExponentiableMorphism (f ≫ g) :=
  ⟨pushforward f ⋙ pushforward g,
    ofNatIsoLeft (pullbackPushforwardAdj g |>.comp <| pullbackPushforwardAdj f)
    (pullbackComp f g).symm⟩

theorem comp_pushforward {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    (comp f g).pushforward = pushforward f ⋙ pushforward g := by
  dsimp +instances only [comp]

/-- The natural isomorphism between pushforward of the composition and the composition of
pushforward functors. -/
def pushforwardComp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    pushforward (C := C) (f ≫ g) ≅ pushforward f ⋙ pushforward g :=
  Adjunction.rightAdjointUniq (pullbackPushforwardAdj (f ≫ g)) ((comp f g).pullbackPushforwardAdj)

@[reassoc (attr := simp)]
theorem unit_pushforwardComp_hom {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    (pullbackPushforwardAdj (f ≫ g)).unit ≫
      (pullback (f ≫ g)).whiskerLeft (pushforwardComp f g).hom =
      (comp f g).pullbackPushforwardAdj.unit := by
  rw [pushforwardComp, Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
theorem pushforwardComp_hom_counit {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    Functor.whiskerRight (pushforwardComp f g).hom (pullback (f ≫ g)) ≫
      (comp f g).pullbackPushforwardAdj.counit =
      (pullbackPushforwardAdj (f ≫ g)).counit := by
  rw [pushforwardComp, Adjunction.rightAdjointUniq_hom_counit]

end

end ExponentiableMorphism

end CategoryTheory
