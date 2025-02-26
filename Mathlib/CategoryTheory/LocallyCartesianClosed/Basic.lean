/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
import Mathlib.CategoryTheory.Comma.Over.Sections

/-!
# Locally cartesian closed categories

There are several equivalent definitions of locally cartesian closed categories. For instance
the following two definitions are equivalent:

1. A locally cartesian closed category is a category `C` such that for every object `I`
the slice category `Over I` is cartesian closed.

2. Equivalently, a locally cartesian closed category is a category with pullbacks where
all morphisms `f` are exponentiable, that is the base change functor `Over.pullback f`
has a right adjoint for every morphisms `f : I ⟶ J`. This latter condition is equivalent to
exponentiability of `Over.mk f` in `Over J`. The right adjoint of `Over.pullback f`
is called the pushforward functor.

In this file we prove the equivalence of these definitions.

## Implementation notes

The type class `LocallyCartesianClosed` extends `HasPushforwards` with the extra data carrying the
witness of cartesian closedness of the slice categories. `HasPushforwards.cartesianClosedOver` shows
that the cartesian closed structure of the slices follows from existence of pushforwards
along all morphisms. As such when instantiating a `LocallyCartesianClosed` structure,
providing the the cartesian closed structure of the slices is not necessary and it will be filled
in automatically. See `LocallyCartesianClosed.mkOfHasPushforwards` and
`LocallyCartesianClosed.mkOfCartesianClosedOver`.

The advanatge we obtain from this implementation is that when using a
`LocallyCartesianClosed` structure, both the pushforward functor and the cartesian closed structure
of slices are automatically available.

## Main results

- `exponentiableOverMk` shows that the exponentiable structure on a morphism `f` makes
the object `Over.mk f` in the appropriate slice category exponentiable.
- `ofOverExponentiable` shows that an exponentiable object in a slice category gives rise to an
exponentiable morphism.
- `CartesianClosedOver.pushforward` constructs, in a category with cartesian closed slices,
the pushforward functor along a morphism `f : I ⟶ J`.
- `CartesianClosedOver.pushforwardAdj` shows that `pushforward` is right adjoint to the
pullback functor.
- Conversely, `HasPushforwards.cartesianClosedOver` shows that, in a category with pushforwards
along all morphisms, the slice categories are cartesian closed.
- `LocallyCartesianClosed.cartesianClosed` proves that a locally cartesian closed category with a
terminal object is cartesian closed.
- `LocallyCartesianClosed.overLocallyCartesianClosed` shows that the slices of a locally cartesian
closed category are locally cartesian closed.

-/

noncomputable section

universe v u

namespace CategoryTheory

open CategoryTheory Category MonoidalCategory Limits Functor Adjunction Over

variable {C : Type u} [Category.{v} C]

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
class ExponentiableMorphism [HasPullbacks C] {I J : C} (f : I ⟶ J) where
  /-- The pushforward functor -/
  pushforward : Over I ⥤ Over J
  /-- The pushforward functor is right adjoint to the pullback functor -/
  adj : pullback f ⊣ pushforward := by infer_instance

namespace ExponentiableMorphism

variable [HasPullbacks C]

instance OverMkHom {I J : C} {f : I ⟶ J} [ExponentiableMorphism f] :
    ExponentiableMorphism (Over.mk f).hom := by
  dsimp
  infer_instance

/-- The identity morphisms `𝟙` are exponentiable. -/
@[simps]
instance id {I : C} : ExponentiableMorphism (𝟙 I) where
  pushforward := 𝟭 (Over I)
  adj := ofNatIsoLeft (F:= 𝟭 _) Adjunction.id (pullbackId).symm

/-- The conjugate iso between the pushforward of the identity and the identity of the
pushforward. -/
def pushfowardIdIso {I : C} : (id : ExponentiableMorphism (𝟙 I)).pushforward ≅ 𝟭 (Over I) :=
  conjugateIsoEquiv Adjunction.id id.adj pullbackId

/-- The composition of exponentiable morphisms is exponentiable. -/
def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
  ExponentiableMorphism (f ≫ g) where
  pushforward := (pushforward f) ⋙ (pushforward g)
  adj := ofNatIsoLeft (gexp.adj.comp fexp.adj) (pullbackComp f g).symm

/-- The conjugate isomorphism between pushforward of the composition and the composition of
pushforward functors. -/
def pushforwardCompIso {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
  (comp f g).pushforward ≅ fexp.pushforward ⋙ gexp.pushforward  :=
  conjugateIsoEquiv (gexp.adj.comp fexp.adj) ((comp f g).adj) (pullbackComp f g)

/-- A morphism with a pushforward is an exponentiable object in the slice category. -/
def exponentiableOverMk [HasFiniteWidePullbacks C] {X I : C} (f : X ⟶ I)
    [ExponentiableMorphism f] :
    Exponentiable (Over.mk f) where
  rightAdj := pullback f ⋙ pushforward f
  adj := by
    apply ofNatIsoLeft _ _
    · exact Over.pullback f ⋙ Over.map f
    · exact Adjunction.comp ExponentiableMorphism.adj (Over.mapPullbackAdj _)
    · exact sigmaReindexNatIsoTensorLeft (Over.mk f)

/-- An exponentibale object `X` in the slice category `Over I` gives rise to an exponentiable
morphism `X.hom`. -/
def ofOverExponentiable [HasFiniteWidePullbacks C] {I : C} (X : Over I) [Exponentiable X] :
    ExponentiableMorphism X.hom where
  pushforward := X.iteratedSliceEquiv.inverse ⋙ sections X
  adj := by
    refine ofNatIsoLeft (Adjunction.comp ?_ ?_) (starIteratedSliceForwardIsoPullback X.hom)
    · exact starSectionsAdj X
    · apply (Over.mk X.hom).iteratedSliceEquiv.toAdjunction

end ExponentiableMorphism

variable (C)

/-- A category `HasPushforwards` if every morphism is exponentiable. -/
class HasPushforwards [HasFiniteWidePullbacks C] where
  /-- A function assigning to every morphism `f : I ⟶ J` an exponentiable structure. -/
  exponentiable {I J : C} (f : I ⟶ J) : ExponentiableMorphism f := by infer_instance

namespace HasPushforwards

open Over ExponentiableMorphism

variable {C} [HasFiniteWidePullbacks C] [HasPushforwards C]

/-- The pushforward functor along a morphism `f : I ⟶ J` in a category `C` with pushforwards. -/
def pushforward {I J : C} (f : I ⟶ J) :
    Over I ⥤ Over J :=
  (exponentiable f).pushforward

/-- `Pi X Y` is the dependent product of `Y` along `X` in the slice category `Over I`. This
is analogous to the dependent function type `Π x : X, Y x` in type theory. See `Over.Sigma`
and `Over.Reindex` for related constructions. -/
abbrev Pi {I : C} (X : Over I) (Y : Over X.left) : Over I :=
  (pushforward X.hom).obj Y

/-- In a category where pushforwards exists along all morphisms, every slice category `Over I` is
cartesian closed. -/
instance cartesianClosedOver
    [HasFiniteWidePullbacks C] [HasPushforwards C] (I : C) :
    CartesianClosed (Over I) where
  closed X := @exponentiableOverMk _ _ _ _ _ _ X.hom (HasPushforwards.exponentiable X.hom)

end HasPushforwards

namespace CartesianClosedOver

open Over Reindex IsIso ChosenFiniteProducts CartesianClosed HasPushforwards

variable {C} [HasFiniteWidePullbacks C] {I J : C} [CartesianClosed (Over J)] (f : I ⟶ J)

/-- The pushforward functor along a morphism `f : I ⟶ J` defined using the section functor
Over (Over.mk f) ⥤ Over J. -/
@[simps!]
def pushforward : (Over I) ⥤ (Over J) :=
  (Over.mk f).iteratedSliceEquiv.inverse ⋙ sections (Over.mk f)

/-- `CartesianClosedOver.pushforward` is a right adjoint to `Over.pullback f`. -/
@[simps! unit_app counit_app]
def pushforwardAdj : pullback f ⊣ pushforward f := by
  refine ofNatIsoLeft (Adjunction.comp ?_ ?_) (starIteratedSliceForwardIsoPullback f)
  · apply starSectionsAdj
  · apply (Over.mk f).iteratedSliceEquiv.toAdjunction

variable {f}

/-- The currying of `(Over.pullback f).obj A ⟶ X` in `Over I` to a morphism
`A ⟶ (pushforward f).obj X` in `Over J`. -/
def pushforwardCurry {X : Over I} {A : Over J} (u : (Over.pullback f).obj A ⟶ X) :
    A ⟶ (pushforward f).obj X :=
  (pushforwardAdj f).homEquiv A X u

/-- The uncurrying of `A ⟶ (pushforward f).obj X` in `Over J` to a morphism
`(Over.pullback f).obj A ⟶ X` in `Over I`. -/
def pushforwardUncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    (Over.pullback f).obj A ⟶ X :=
  ((pushforwardAdj f).homEquiv A X).invFun v

theorem pushforward_uncurry_curry {X : Over I} {A : Over J} (u : (Over.pullback f).obj A ⟶ X) :
    pushforwardUncurry (pushforwardCurry u) = u := by
  exact ((pushforwardAdj f).homEquiv A X).left_inv u

theorem pushforward_curry_uncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    pushforwardCurry (pushforwardUncurry v) = v := by
  exact ((pushforwardAdj f).homEquiv A X).right_inv v

end CartesianClosedOver

/-- A category with cartesian closed slices has pushforwards along all morphisms. -/
instance CartesianClosedOver.hasPushforwards [HasFiniteWidePullbacks C]
    [Π (I : C), CartesianClosed (Over I)] : HasPushforwards C where
  exponentiable f := ExponentiableMorphism.ofOverExponentiable (Over.mk f)

/-- A category with `FiniteWidePullbacks` is locally cartesian closed if every morphism in it
is exponentiable and all the slices are cartesian closed. -/
class LocallyCartesianClosed [HasFiniteWidePullbacks C] extends
    HasPushforwards C where
  /-- every slice category `Over I` is cartesian closed. This is filled in by default. -/
  cartesianClosedOver : Π (I : C), CartesianClosed (Over I) := HasPushforwards.cartesianClosedOver

namespace LocallyCartesianClosed

open Over Sigma Reindex HasPushforwards

variable {C} [HasFiniteWidePullbacks C]

attribute [scoped instance] hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- A category with pushforwards along all morphisms is locally cartesian closed. -/
instance mkOfHasPushforwards [HasPushforwards C] : LocallyCartesianClosed C where

/-- A category with cartesian closed slices is locally cartesian closed. -/
instance mkOfCartesianClosedOver [Π (I : C), CartesianClosed (Over I)] :
  LocallyCartesianClosed C where

variable [LocallyCartesianClosed C]

/-- The dependent evaluation natural transformation as the counit of the adjunction. -/
abbrev ev {X I : C} (f : X ⟶ I) : pushforward f ⋙ Over.pullback f ⟶ 𝟭 _ :=
(exponentiable f).adj.counit

/-- The dependent evaluation morphisms. -/
abbrev ev' {I : C} (X : Over I) (Y : Over X.left) : Reindex X (Pi X Y) ⟶ Y :=
  (exponentiable X.hom).adj.counit.app Y

/-- A locally cartesian closed category with a terminal object is cartesian closed. -/
def cartesianClosed [HasTerminal C] :
    CartesianClosed C := cartesianClosedOfEquiv <| equivOverTerminal C

/-- The slices of a locally cartesian closed category are locally cartesian closed. -/
def overLocallyCartesianClosed (I : C) : LocallyCartesianClosed (Over I) := by
  apply (config := { allowSynthFailures:= true}) mkOfCartesianClosedOver
  intro X
  exact cartesianClosedOfEquiv (C := Over (X.left)) X.iteratedSliceEquiv.symm

/-- The exponential `X^^A` in the slice category `Over I` is isomorphic to the pushforward of the
pullback of `X` along `A`. -/
def expIso {I : C} (A X : Over I) :  Pi A (Reindex A X) ≅ A ⟹ X := Iso.refl _

end LocallyCartesianClosed

end CategoryTheory
