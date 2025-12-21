/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
public import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism


/-!
# Locally cartesian closed categories

There are several equivalent definitions of locally cartesian closed categories. For instance
the following two definitions are equivalent:

1. A locally cartesian closed category is a category `C` such that for every object `I`
the slice category `Over I` is cartesian closed.

2. Equivalently, a locally cartesian closed category is a category with pullbacks where
all morphisms `f` are exponentiable, that is the base change functor `Over.pullback f`
has a right adjoint for every morphisms `f : I ⟶ J`. This latter condition is equivalent to
exponentiability of `Over.mk f` – morphism `f` considered as an object of `Over J`.
The right adjoint of `Over.pullback f` is called the pushforward functor.

In this file we prove the equivalence of these definitions.

## Implementation notes

- The type class `ChosenPushforwards` provides pushforward functors, that is right adjoints to
  the chosen pullback functor, for every morphism in the category.

- `ChosenPushforwards.cartesianClosedOver` provides the cartesian closed structure of the slices
  from an instance of `ChosenPushforwards` on the category.

- The type class `LocallyCartesianClosed` extends `ChosenPushforwards` with the extra data carrying
  the witness of cartesian closedness of the slice categories. As such when instantiating a
  `LocallyCartesianClosed` structure, the cartesian closed structure of the slices will be filled
  in automatically. See `LocallyCartesianClosed.mkOfChosenPushforwards` and
  `LocallyCartesianClosed.mkOfCartesianClosedOver`.

  The advantage we obtain from this implementation is that when using a
  `LocallyCartesianClosed` structure, both the pushforward functor and the cartesian closedness
  of slices are automatically available, whereas for proving locally cartesian closedness proving
  only one of these two conditions is sufficient.

## Main results

- `exponentiableOverMk` shows that the exponentiable structure on a morphism `f` makes
the object `Over.mk f` in the appropriate slice category exponentiable.

- `ofOverExponentiable` shows that an exponentiable object in a slice category gives rise to an
exponentiable morphism.

- `CartesianClosedOver.pushforward` constructs, in a category with cartesian closed slices,
the pushforward functor along a morphism `f : I ⟶ J`.

- `CartesianClosedOver.pushforwardAdj` shows that `pushforward` is right adjoint to the
pullback functor.

- Conversely, `ChosenPushforwards.cartesianClosedOver` shows that, in a category with pushforwards
along all morphisms, the slice categories are cartesian closed.

- `LocallyCartesianClosed.cartesianClosed` proves that a locally cartesian closed category with a
terminal object is cartesian closed.

- `LocallyCartesianClosed.overLocallyCartesianClosed` shows that the slices of a locally cartesian
closed category are locally cartesian closed.

### TODO

- Under the assumptions that `C` has chosen pullbacks and a terminal object, show that the functor
  `toOverUnit : C ⥤ Over (𝟙_ C)` is strong monoidal (in fact strict monoidal).

### References

The content here is based on our work on the formalization of polynomial functors project at the
Trimester "Prospect of Formal Mathematics" at the Hausdorff Institute (HIM) in Bonn.

You can find the polynomial functors project at https://github.com/sinhp/Poly

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Adjunction MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] {X : C} {f : Over X}

attribute [local instance] ChosenPullbacksAlong.cartesianMonoidalCategoryOver

namespace Over

/-- The naturality of the iterated slice equivalence up to isomorphism. -/
@[simps! hom_app inv_app]
def iteratedSliceForwardNaturalityIso {g : Over X} (p : f ⟶ g) :
    Over.iteratedSliceForward f ⋙ Over.map p.left ≅ Over.map p ⋙ Over.iteratedSliceForward g :=
  NatIso.ofComponents (fun h => Iso.refl _) (by cat_disch)

/-- The natural isomorphism witnessing `Over.map` in the iterated slice is
compatible with `Over.map` base category, mediated by the iterated slice equivalence. -/
@[simps! hom_app inv_app]
def iteratedSliceEquivOverMapIso {f g : Over X} (p : f ⟶ g) :
    f.iteratedSliceForward ⋙ Over.map p.left ⋙ g.iteratedSliceBackward ≅ Over.map p :=
  NatIso.ofComponents (fun h => Over.isoMk (Over.isoMk (Iso.refl _))) (by cat_disch)

end Over

namespace ChosenPullbacks

open ChosenPullbacksAlong

/-- The binary fan provided by `fst'` and `snd'`. -/
def binaryFan (T Y Z : C) (h : Limits.IsTerminal T)
    [ChosenPullbacksAlong <| h.from Z] :
    Limits.BinaryFan Y Z :=
  Limits.BinaryFan.mk (P:= pullbackObj (h.from Y) (h.from Z)) (fst _ _) (snd _ _)

@[simp]
theorem binaryFan_pt {T Y Z : C} {h : Limits.IsTerminal T}
  [ChosenPullbacksAlong <| h.from Z] :
  (binaryFan T Y Z h).pt = pullbackObj (h.from Y) (h.from Z) :=
  rfl

@[simp]
theorem binaryFan_fst {T Y Z : C} {h : Limits.IsTerminal T}
  [ChosenPullbacksAlong <| h.from Z] :
  (binaryFan T Y Z h).fst = fst (h.from Y) (h.from Z) :=
  rfl

@[simp]
theorem binaryFan_snd {T Y Z : C} {h : Limits.IsTerminal T}
  [ChosenPullbacksAlong <| h.from Z] :
  (binaryFan T Y Z h).snd = snd (h.from Y) (h.from Z) :=
  rfl

/-- The binary fan constructed via the chosen pullback along the morphism from `Z` to the terminal
object is a binary product. -/
def binaryFanIsBinaryProduct (T Y Z : C) (h : Limits.IsTerminal T)
    [ChosenPullbacksAlong <| h.from Z] :
    Limits.IsLimit (binaryFan T Y Z h) :=
  Limits.BinaryFan.IsLimit.mk (binaryFan T Y Z h)
    (fun a b => lift a b)
    (by simp)
    (by simp)
    (fun f g m h₁ h₂ => by cat_disch)

/-- A cartesian monoidal category structure on `C` induced by chosen pullbacks and a terminal
object `T`. -/
def cartesianMonoidalCategory (T : C) (h : Limits.IsTerminal T) [ChosenPullbacks C] :
    CartesianMonoidalCategory C :=
  ofChosenFiniteProducts (C := C)
    ⟨Limits.asEmptyCone T, h⟩
    (fun Y Z ↦ ⟨_, binaryFanIsBinaryProduct T Y Z h⟩)

attribute [local instance] cartesianMonoidalCategory

#print CartesianMonoidalCategory.toSemiCartesianMonoidalCategory

#check SemiCartesianMonoidalCategory.toMonoidalCategory

instance (T : C) (h : Limits.IsTerminal T) [ChosenPullbacks C] :
    MonoidalCategory C :=
  by
    letI := cartesianMonoidalCategory T h
    infer_instance


example (T : C) (h : Limits.IsTerminal T) [ChosenPullbacks C] (Y : C) :
  letI := cartesianMonoidalCategory T h
  X ⊗ Y = pullbackObj (h.from X) (h.from Y) := rfl



end ChosenPullbacks

namespace ChosenPullbacks

open ChosenPullbacksAlong

variable {X : C}

/-- The push-pull object `(Over.map Z.hom).obj ((pullback Z.hom).obj Y)` is isomorphic to the
cartesian product `Y ⊗ Z` in the slice category `Over X`.
Note: The monoidal structure of `Over X` is the one induced by the chosen pullbacks, namely
the one provided by `cartesianMonoidalCategoryOver`.
-/
@[simps!]
def mapPullbackIsoProd [ChosenPullbacks C] (Y Z : Over X) :
    (Over.map Z.hom).obj ((pullback Z.hom).obj Y) ≅ Y ⊗ Z :=
  Iso.refl _

@[reassoc (attr := simp)]
lemma mapPullbackIsoProd_hom [ChosenPullbacks C] {Y Z : Over X} :
    (mapPullbackIsoProd Y Z).hom = 𝟙 _ :=
  rfl

/-- The pull-push composition `pullback Z.hom ⋙ map Z.hom` is naturally isomorphic
to the right tensor product functor `_ ⊗ Z` in the slice category `Over X`. -/
def pullbackMapNatIsoTensorRight [ChosenPullbacks C] (Z : Over X) :
    pullback Z.hom ⋙ Over.map Z.hom ≅ tensorRight Z :=
  NatIso.ofComponents
    (fun Y => mapPullbackIsoProd Y Z)
    (by
      intro Y' Y f
      simp only [Functor.const_obj_obj, Functor.id_obj, Functor.comp_obj, Functor.flip_obj_obj,
        curriedTensor_obj_obj, Functor.comp_map, mapPullbackIsoProd_hom, comp_id,
        Functor.flip_obj_map, curriedTensor_map_app, id_comp]
      ext
      · simp only [Over.map_obj_left, whiskerRight_fst]
        apply pullback_map_left_fst
      · rw [Over.comp_left, Over.map_map_left]
        simp only [Over.map_obj_left, Over.tensorObj_left, whiskerRight_snd]
        simp [Over.snd_eq_snd'])

@[simp]
theorem pullbackMapNatIsoTensorRight_hom_app [ChosenPullbacks C] {Y : Over X} (Z : Over X) :
    (pullbackMapNatIsoTensorRight Z).hom.app Y = 𝟙 _ := by
  cat_disch

/-- If `C` has chosen pullbacks, then `Over X` also has chosen pullbacks`.
Note: Move this to the file ChosenPullbacksAlong before merging.
-/
@[simps]
instance chosenPullbacksOver [ChosenPullbacks C] :
    ChosenPullbacks (Over X) := fun {Y Z : Over X} g => {
  pullback := Y.iteratedSliceForward ⋙ pullback g.left ⋙ Z.iteratedSliceBackward
  mapPullbackAdj :=
    Z.iteratedSliceEquiv.toAdjunction.comp (mapPullbackAdj g.left) |>.comp
        Y.iteratedSliceEquiv.symm.toAdjunction |>.ofNatIsoLeft
      (Functor.associator _ _ _ ≪≫
        Over.iteratedSliceEquivOverMapIso g)
  }

end ChosenPullbacks

namespace ExponentiableMorphism

open BraidedCategory ChosenPullbacksAlong ChosenPullbacks

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- A exponentiable morphism is an exponentiable object in the slice category of its codomain. -/
def exponentiableOverMk [ChosenPullbacks C] {X I : C}
    (f : X ⟶ I) [ExponentiableMorphism f] :
    Exponentiable (Over.mk f) where
  rightAdj := pullback f ⋙ pushforward f
  adj := ofNatIsoLeft (F:= pullback f ⋙ Over.map f)
    ((pullbackAdjPushforward f).comp (mapPullbackAdj f))
    ((pullbackMapNatIsoTensorRight <| Over.mk f) ≪≫ (tensorLeftIsoTensorRight _).symm)

instance [CartesianMonoidalCategory C] [ChosenPullbacks C] (X : C) [Exponentiable X] :
    ChosenPullbacksAlong (curryId X) := by
  infer_instance

/-- If `X : Over I` is an exponentiable object then `X.hom : X.left ⟶ I` is an exponentiable
morphism. Here the pushforward functor along a morphism `f : I ⟶ J` is defined by the way of the
section functor `Over (Over.mk f) ⥤ Over J`. -/
def ofExponentiable [ChosenPullbacks C] {I : C} (X : Over I)
    [Exponentiable X] :
    ExponentiableMorphism X.hom :=
  ⟨X.iteratedSliceEquiv.inverse ⋙ Over.sections X,
    ofNatIsoLeft
      (Adjunction.comp (Over.toOverSectionsAdj X) (Over.mk X.hom).iteratedSliceEquiv.toAdjunction)
      (toOverIteratedSliceForwardIsoPullback X.hom)⟩


end ExponentiableMorphism

variable (C)

/-- A category `ChosenPushforwards` if every morphism is exponentiable. -/
class ChosenPushforwards [ChosenPullbacks C] where
  /-- A function assigning to every morphism `f : I ⟶ J` an exponentiable structure. -/
  exponentiable {I J : C} (f : I ⟶ J) : ExponentiableMorphism f := by infer_instance

namespace ChosenPushforwards

open Over ChosenPullbacksAlong ChosenPullbacks ExponentiableMorphism

variable {C} [ChosenPullbacks C] [ChosenPushforwards C]

/-- In a category where pushforwards exists along all morphisms, every slice category `Over I` is
cartesian closed. -/
instance cartesianClosedOver (I : C) :
    CartesianClosed (Over I) where
  closed X := @exponentiableOverMk _ _ _ _ _ X.hom (ChosenPushforwards.exponentiable X.hom)

end ChosenPushforwards

namespace CartesianClosedOver

attribute [local instance] ChosenPullbacksAlong.cartesianMonoidalCategoryOver

variable {C} [ChosenPullbacks C] {I J : C} [CartesianClosed (Over J)]

instance (f : I ⟶ J) : ExponentiableMorphism f :=
  ExponentiableMorphism.ofExponentiable (Over.mk f)

/-- A category with cartesian closed slices has chosen pushforwards along all morphisms. -/
instance chosenPushforwards [Π (I : C), CartesianClosed (Over I)] : ChosenPushforwards C where
  exponentiable f := ExponentiableMorphism.ofExponentiable (Over.mk f)

end CartesianClosedOver

open ChosenPushforwards

/-- A category with `ChosenPullbacks` is locally cartesian closed if every morphism in it
is exponentiable and all the slices are cartesian closed. -/
class LocallyCartesianClosed [ChosenPullbacks C] extends ChosenPushforwards C where
  /-- every slice category `Over I` is cartesian closed. This is filled in by default. -/
  cartesianClosedOver : Π (I : C), CartesianClosed (Over I) := cartesianClosedOver

namespace LocallyCartesianClosed

open ExponentiableMorphism ChosenPullbacksAlong ChosenPushforwards ChosenPullbacks

variable {C} [ChosenPullbacks C]

/-- A category with pushforwards along all morphisms is locally cartesian closed. -/
instance ofChosenPushforwards [ChosenPushforwards C] : LocallyCartesianClosed C where

/-- A category with cartesian closed slices is locally cartesian closed. -/
instance ofCartesianClosedOver [Π (I : C), CartesianClosed (Over I)] :
  LocallyCartesianClosed C where

variable [LocallyCartesianClosed C]

/-- Every morphism in a locally cartesian closed category is exponentiable. -/
instance exponentiableMorphism {I J : C} (f : I ⟶ J) : ExponentiableMorphism f :=
  ChosenPushforwards.exponentiable f

/-- A locally cartesian closed category with a terminal object is cartesian closed. -/
noncomputable def cartesianClosed (T : C) (h : Limits.IsTerminal T) :
    letI := cartesianMonoidalCategory T h
    CartesianClosed C :=
    let := cartesianMonoidalCategory T h
    cartesianClosedOfEquiv <| equivToOverUnit C

/-- The slices of a locally cartesian closed category are locally cartesian closed. -/
noncomputable def overLocallyCartesianClosed (I : C) : LocallyCartesianClosed (Over I) := by
  apply (config := { allowSynthFailures:= true}) ofCartesianClosedOver
  intro X
  exact cartesianClosedOfEquiv (C := Over (X.left)) X.iteratedSliceEquiv.symm

end LocallyCartesianClosed

end CategoryTheory
