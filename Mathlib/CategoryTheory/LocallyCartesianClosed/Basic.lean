/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
import Mathlib.CategoryTheory.MorphismProperty.Composition

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

attribute [local instance] CartesianMonoidalCategory.ofFiniteProducts

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
abbrev ExponentiableMorphism [HasPullbacks C] : MorphismProperty C :=
  fun _ _ f ↦ IsLeftAdjoint (Over.pullback f)

namespace ExponentiableMorphism

variable [HasPullbacks C] {I J : C}

/-- The pushforward functor along a morphism `f : I ⟶ J` as the right adjoint
to the pullback functor. -/
abbrev pushforward (f : I ⟶ J) [ExponentiableMorphism f] :=
  rightAdjoint (Over.pullback f)

/-- The adjunction between the pullback and pushforward functors along a morphism `f : I ⟶ J`. -/
def adj (f : I ⟶ J) [ExponentiableMorphism f] :=
  Adjunction.ofIsLeftAdjoint (Over.pullback f)

/-- The dependent evaluation natural transformation as the counit of the adjunction. -/
abbrev ev (f : I ⟶ J) [ExponentiableMorphism f] :
    pushforward f ⋙ Over.pullback f ⟶ 𝟭 _ :=
  adj f |>.counit

/-- The dependent coevaluation natural transformation as the unit of the adjunction. -/
abbrev coev (f : I ⟶ J) [ExponentiableMorphism f] :
    𝟭 _ ⟶ Over.pullback f ⋙ pushforward f :=
  adj f |>.unit

variable {f : I ⟶ J}

/-- The first triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
theorem ev_coev [ExponentiableMorphism f] (X : Over J) :
    (Over.pullback f).map (adj f |>.unit.app X) ≫ (adj f |>.counit.app (Over.pullback f |>.obj X)) =
    𝟙 (Over.pullback f |>.obj X) :=
  adj f |>.left_triangle_components X

/-- The second triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
theorem coev_ev [ExponentiableMorphism f] (Y : Over I) :
    (adj f |>.unit.app (pushforward f |>.obj Y)) ≫ (pushforward f |>.map (adj f |>.counit.app Y)) =
    𝟙 (pushforward f |>.obj Y) :=
  adj f |>.right_triangle_components Y

/-- The currying of `(Over.pullback f).obj A ⟶ X` in `Over I` to a morphism
`A ⟶ (pushforward f).obj X` in `Over J`. -/
def pushforwardCurry [ExponentiableMorphism f] {X : Over I} {A : Over J}
    (u : (Over.pullback f).obj A ⟶ X) :
    A ⟶ (pushforward f).obj X :=
  adj f |>.homEquiv A X u

/-- The uncurrying of `A ⟶ (pushforward f).obj X` in `Over J` to a morphism
`(Over.pullback f).obj A ⟶ X` in `Over I`. -/
def pushforwardUncurry [ExponentiableMorphism f] {X : Over I} {A : Over J}
    (v : A ⟶ (pushforward f).obj X) :
    (Over.pullback f).obj A ⟶ X :=
  adj f |>.homEquiv A X |>.invFun v

theorem homEquiv_apply_eq [ExponentiableMorphism f] {X : Over I} {A : Over J}
    (u : (Over.pullback f).obj A ⟶ X) : (adj f |>.homEquiv _ _) u = pushforwardCurry u :=
  rfl

theorem homEquiv_symm_apply_eq [ExponentiableMorphism f] {X : Over I} {A : Over J}
    (v : A ⟶ (pushforward f).obj X) : (adj f |>.homEquiv _ _).symm v = pushforwardUncurry v :=
  rfl

theorem pushforward_uncurry_curry [ExponentiableMorphism f] {X : Over I} {A : Over J}
    (u : (Over.pullback f).obj A ⟶ X) :
    pushforwardUncurry (pushforwardCurry u) = u :=
  adj f |>.homEquiv A X |>.left_inv u

theorem pushforward_curry_uncurry [ExponentiableMorphism f] {X : Over I} {A : Over J}
    (v : A ⟶ (pushforward f).obj X) :
    pushforwardCurry (pushforwardUncurry v) = v :=
  adj f |>.homEquiv A X |>.right_inv v

instance OverMkHom {I J : C} {f : I ⟶ J} [ExponentiableMorphism f] :
    ExponentiableMorphism (Over.mk f).hom := by
  dsimp only [mk_hom]
  infer_instance

/-- The identity morphisms `𝟙` are exponentiable. -/
@[simps]
instance id {I : C} : ExponentiableMorphism (𝟙 I) :=
  ⟨𝟭 _, ⟨ofNatIsoLeft (F:= 𝟭 _) Adjunction.id (pullbackId).symm⟩⟩

/-- The conjugate iso between the pushforward of the identity and the identity of the
pushforward. -/
def pushforwardIdIso (I : C) : pushforward (𝟙 I) ≅ 𝟭 (Over I) :=
  Iso.symm <| conjugateIsoEquiv Adjunction.id (id.adj) pullbackId

/-- The composition of exponentiable morphisms is exponentiable. -/
@[simps]
instance comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    ExponentiableMorphism (f ≫ g) :=
  ⟨pushforward f ⋙ pushforward g, ⟨ofNatIsoLeft (adj g |>.comp <| adj f) (pullbackComp f g).symm⟩⟩

/-- The conjugate isomorphism between pushforward of the composition and the composition of
pushforward functors. -/
def pushforwardCompIso {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    let _ := comp f g
    pushforward (f ≫ g) ≅ pushforward f ⋙ pushforward g :=
  Iso.symm <| conjugateIsoEquiv ((adj g |>.comp <| adj f)) ((comp f g).adj) (pullbackComp f g)

instance isMultiplicative : (ExponentiableMorphism (C:= C)).IsMultiplicative where
  id_mem _ := by infer_instance
  comp_mem f g fexp gexp := by infer_instance

/-- A morphism with a pushforward is an exponentiable object in the slice category. -/
def exponentiableOverMk [HasFiniteWidePullbacks C] {X I : C} (f : X ⟶ I)
    [ExponentiableMorphism f] :
    Exponentiable (Over.mk f) where
  rightAdj := pullback f ⋙ pushforward f
  adj := by
    apply ofNatIsoLeft _ _
    · exact Over.pullback f ⋙ Over.map f
    · exact Adjunction.comp (adj f) (Over.mapPullbackAdj _)
    · exact sigmaReindexNatIsoTensorLeft (Over.mk f)

/-- An exponentibale object `X` in the slice category `Over I` gives rise to an exponentiable
morphism `X.hom`.
Here the pushforward functor along a morphism `f : I ⟶ J` is defined using the section functor
`Over (Over.mk f) ⥤ Over J`.
-/
def ofOverExponentiable [HasFiniteWidePullbacks C] {I : C} (X : Over I) [Exponentiable X] :
    ExponentiableMorphism X.hom :=
  ⟨X.iteratedSliceEquiv.inverse ⋙ sections X, ⟨by
    refine ofNatIsoLeft (Adjunction.comp ?_ ?_) (starIteratedSliceForwardIsoPullback X.hom)
    · exact starSectionsAdj X
    · apply (Over.mk X.hom).iteratedSliceEquiv.toAdjunction⟩⟩

end ExponentiableMorphism

variable (C)

/-- A category `HasPushforwards` if every morphism is exponentiable. -/
class HasPushforwards [HasFiniteWidePullbacks C] where
  /-- A function assigning to every morphism `f : I ⟶ J` an exponentiable structure. -/
  exponentiable {I J : C} (f : I ⟶ J) : ExponentiableMorphism f := by infer_instance

namespace HasPushforwards

open Over ExponentiableMorphism

variable {C} [HasFiniteWidePullbacks C] [HasPushforwards C]

/-- In a category where pushforwards exists along all morphisms, every slice category `Over I` is
cartesian closed. -/
instance cartesianClosedOver (I : C) :
    CartesianClosed (Over I) where
  closed X := @exponentiableOverMk _ _ _ _ _ _ X.hom (HasPushforwards.exponentiable X.hom)

end HasPushforwards

namespace CartesianClosedOver

open Over Reindex IsIso CartesianClosed HasPushforwards ExponentiableMorphism

variable {C} [HasFiniteWidePullbacks C] {I J : C} [CartesianClosed (Over J)]

instance (f : I ⟶ J) : ExponentiableMorphism f :=
  ExponentiableMorphism.ofOverExponentiable (Over.mk f)

/-- A category with cartesian closed slices has pushforwards along all morphisms. -/
instance hasPushforwards [Π (I : C), CartesianClosed (Over I)] : HasPushforwards C where
  exponentiable f := ExponentiableMorphism.ofOverExponentiable (Over.mk f)

end CartesianClosedOver

/-- A category with `FiniteWidePullbacks` is locally cartesian closed if every morphism in it
is exponentiable and all the slices are cartesian closed. -/
class LocallyCartesianClosed [HasFiniteWidePullbacks C] extends
    HasPushforwards C where
  /-- every slice category `Over I` is cartesian closed. This is filled in by default. -/
  cartesianClosedOver : Π (I : C), CartesianClosed (Over I) := HasPushforwards.cartesianClosedOver

namespace LocallyCartesianClosed

open Over Sigma Reindex ExponentiableMorphism HasPushforwards

variable {C} [HasFiniteWidePullbacks C]

attribute [scoped instance] hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- A category with pushforwards along all morphisms is locally cartesian closed. -/
instance mkOfHasPushforwards [HasPushforwards C] : LocallyCartesianClosed C where

/-- A category with cartesian closed slices is locally cartesian closed. -/
instance mkOfCartesianClosedOver [Π (I : C), CartesianClosed (Over I)] :
  LocallyCartesianClosed C where

variable [LocallyCartesianClosed C]

/-- Every morphism in a locally cartesian closed category is exponentiable. -/
instance {I J : C} (f : I ⟶ J) : ExponentiableMorphism f := HasPushforwards.exponentiable f

/-- `Pi X Y` is the dependent product of `Y` along `X`. This is analogous to the dependent function
type `Π x : X, Y x` in type theory. See `Over.Sigma` and `Over.Reindex` for related constructions.
-/
abbrev Pi {I : C} (X : Over I) (Y : Over X.left) : Over I :=
  (pushforward X.hom).obj Y

/-- `Pi'` is a variant of `Pi` which takes as input morphisms and outputs morphisms. -/
abbrev Pi' {I X Y : C} (f : X ⟶ I) (u : Y ⟶ X) : (Pi (Over.mk f) (Over.mk u)).left ⟶ I :=
  Comma.hom <| Pi (Over.mk f) (Over.mk u)

theorem Pi'_def {I X Y : C} (f : X ⟶ I) (u : Y ⟶ X) :
  Pi' f u = ((pushforward f).obj (Over.mk u)).hom := rfl

/-- The dependent evaluation morphisms. -/
abbrev ev' {I : C} (X : Over I) (Y : Over X.left) : Reindex X (Pi X Y) ⟶ Y :=
  adj X.hom |>.counit.app Y

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
