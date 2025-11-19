/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullback
import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

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

### References

The content here is based on our work on the formalization of polynomial functors project at the
Trimester "Prospect of Formal Mathematics" at the Hausdorff Institute (HIM) in Bonn.

You can find the polynomial functors project at https://github.com/sinhp/Poly

-/

universe v u

namespace CategoryTheory

open Category MonoidalCategory Limits Adjunction CartesianMonoidalCategory

open Over hiding pullback mapPullbackAdj pullbackId pullbackComp

open ChosenPullback

attribute [local instance] CartesianMonoidalCategory.ofFiniteProducts

variable {C : Type u} [Category.{v} C]

section BinaryProduct

variable {X : C} (Y Z : Over X)

/-- The canonical pullback cone constructed from `ChosenPullback.isPullback.`
Note: The source of noncomputability is the non-constructive implementation of `IsPullback.isLimit`.
Otherwise, `ChosenPullback.isPullback` is constructive.
-/
noncomputable def isLimitPullbackCone [ChosenPullback Z.hom] :
    IsLimit (isPullback Y.hom Z.hom |>.cone) :=
  isPullback Y.hom Z.hom |>.isLimit

/-- The binary fan provided by `fst'` and `snd'`. -/
def binaryFan [ChosenPullback Z.hom] : BinaryFan Y Z :=
  BinaryFan.mk (P:= Over.mk (Y := pullbackObj Y.hom Z.hom) (snd Y.hom Z.hom ≫ Z.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

@[simp]
theorem binaryFan_pt [ChosenPullback Z.hom] :
    (binaryFan Y Z).pt = Over.mk (Y:= pullbackObj Y.hom Z.hom) (snd Y.hom Z.hom ≫ Z.hom) := by
  rfl

@[simp]
theorem binaryFan_pt_hom [ChosenPullback Z.hom] :
    (binaryFan Y Z).pt.hom = snd Y.hom Z.hom ≫ Z.hom := by
  rfl

/-- The binary fan provided by `fst'` and `snd'` is a binary product in `Over X`. -/
def binaryFanIsBinaryProduct [ChosenPullback Z.hom] :
    IsLimit (binaryFan Y Z) :=
  BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [w u, w v])) (by simp))
    (fun a b => by simp [binaryFan]; aesop)
    (fun a b => by simp [binaryFan]; aesop)
    (fun a b m h₁ h₂ => by
      apply Over.OverMorphism.ext
      simp only [homMk_left]
      apply hom_ext (f:= Y.hom) (g:= Z.hom) <;> aesop)

attribute [local instance] Over.cartesianMonoidalCategory

/-- The push-pull object `(pullback Z.hom).obj Y` is isomorphic to the cartesian product
`Y ⊗ Z` in the slice category `Over X`.
Note: Whereas the left hand-side is defined in a computable way, the right hand-side relies on
the non-constructive monoidal structure on `Over X` so this isomorphism is noncomputable.
-/
@[simps!]
noncomputable def mapPullbackIsoProd [ChosenPullbacks C] :
    (map Z.hom).obj ((ChosenPullback.pullback Z.hom).obj Y) ≅ Y ⊗ Z :=
  IsLimit.conePointUniqueUpToIso
    (binaryFanIsBinaryProduct Y Z) (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor

attribute [local instance] ofHasPullbacksAlong in
/-- Given a morphism `g : W ⟶ X` and an object `Y` over `X`, the object
`(map g).obj ((pullback g).obj Y)` is isomorphic to the cartesian product of `Y` and `Over.mk f`. -/
noncomputable def mapPullbackIsoProdOverMk [ChosenPullbacks C] {W : C} (g : W ⟶ X) :
    (map g).obj ((ChosenPullback.pullback g).obj Y) ≅ Y ⊗ Over.mk g :=
  mapPullbackIsoProd Y (Over.mk g)

attribute [local instance] ofHasPullbacksAlong in
@[reassoc (attr := simp)]
theorem mapPullbackIsoProd_hom_comp_fst [ChosenPullbacks C] :
    (mapPullbackIsoProd Y Z).hom ≫ CartesianMonoidalCategory.fst Y Z = fst' Y.hom Z.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (binaryFanIsBinaryProduct Y Z)
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor ⟨.left⟩

attribute [local instance] ofHasPullbacksAlong in
@[reassoc (attr := simp)]
theorem mapPullbackIsoProd_hom_comp_snd [ChosenPullbacks C] :
    (mapPullbackIsoProd Y Z).hom ≫ CartesianMonoidalCategory.snd Y Z = snd' Y.hom Z.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (binaryFanIsBinaryProduct Y Z)
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor ⟨.right⟩

end BinaryProduct

section TensorRight

open CartesianMonoidalCategory

variable {X : C}

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] ofHasPullbacksAlong in
/-- The pull-push composition `pullback Z.hom ⋙ map Z.hom` is naturally isomorphic
to the right tensor product functor `_ ⊗ Z` in the slice category `Over X`. -/
noncomputable def pullbackMapNatIsoTensorRight [ChosenPullback C] (Z : Over X) :
    pullback Z.hom ⋙ map Z.hom ≅ tensorRight Z :=
  NatIso.ofComponents
    (fun Y => mapPullbackIsoProd Y Z)
    (by
      intro Y Y' f
      simp
      ext1 <;> simp_rw [assoc]
      · rw [whiskerRight_fst]
        ext
        rw [mapPullbackIsoProd_hom_comp_fst, mapPullbackIsoProd_hom_comp_fst_assoc]
        simp [fst']
      · simp_rw [whiskerRight_snd]
        ext
        iterate rw [mapPullbackIsoProd_hom_comp_snd]
        simp [ChosenPullback.snd])

attribute [local instance] ofHasPullbacksAlong in
@[simp]
theorem Over.pullbackMapNatIsoTensorRight_hom_app [HasPullbacks C] {Y : Over X} (Z : Over X) :
    (pullbackMapNatIsoTensorRight Z).hom.app Y = (mapPullbackIsoProd Y Z).hom := by
  aesop

end TensorRight

namespace ExponentiableMorphism

open MonoidalClosed BraidedCategory

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

attribute [local instance] ofHasPullbacksAlong in
/-- A morphism with a pushforward is an exponentiable object in the slice category. -/
noncomputable def exponentiableOverMk [ChosenPullbacks C] {X I : C} (f : X ⟶ I)
    [ExponentiableMorphism f] :
    Exponentiable (Over.mk f) where
  rightAdj := pullback f ⋙ pushforward f
  adj := ofNatIsoLeft (F:= pullback f ⋙ Over.map f)
    ((pullbackAdjPushforward f).comp (mapPullbackAdj f))
    ((pullbackMapNatIsoTensorRight <| Over.mk f) ≪≫ (tensorLeftIsoTensorRight _).symm)

example {X: C} : ChosenPullback (curry <|z (ρ_ X).hom) := by infer_instance

attribute [local instance] ofHasPullbacksAlong in
/-- An exponentibale object `X` in the slice category `Over I` gives rise to an exponentiable
morphism `X.hom`.
Here the pushforward functor along a morphism `f : I ⟶ J` is defined using the section functor
`Over (Over.mk f) ⥤ Over J`.
-/
def ofOverExponentiable [ChosenPullbacks C] {I : C} (X : Over I) [Exponentiable X] :
    ExponentiableMorphism X.hom :=
  ⟨X.iteratedSliceEquiv.inverse ⋙ Over.sections X, by
    refine ofNatIsoLeft (Adjunction.comp ?_ ?_) (toOverIteratedSliceForwardIsoPullback X.hom)
    · exact starSectionsAdj X
    · apply (Over.mk X.hom).iteratedSliceEquiv.toAdjunction⟩

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
class LocallyCartesianClosed [ChosenPullbacks C] extends
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
