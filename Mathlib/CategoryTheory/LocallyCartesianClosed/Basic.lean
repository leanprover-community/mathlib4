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

### References

The content here is based on our work on the formalization of polynomial functors project at the
Trimester "Prospect of Formal Mathematics" at the Hausdorff Institute (HIM) in Bonn.

You can find the polynomial functors project at https://github.com/sinhp/Poly

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory Adjunction CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

namespace ChosenPullbacks

variable [ChosenPullbacks C] {X : C}

open ChosenPullbacksAlong

/-- The binary fan provided by `fst'` and `snd'`. -/
def binaryFan (T Y Z : C) (h : Limits.IsTerminal T) :
    Limits.BinaryFan Y Z :=
  Limits.BinaryFan.mk (P:= pullbackObj (h.from Y) (h.from Z)) (fst _ _) (snd _ _)

@[simp]
theorem binaryFan_pt (T Y Z : C) (h : Limits.IsTerminal T) :
    (binaryFan T Y Z h).pt = pullbackObj (h.from Y) (h.from Z) :=
  rfl

@[simp]
theorem binaryFan_fst (T Y Z : C) (h : Limits.IsTerminal T) :
    (binaryFan T Y Z h).fst = fst (h.from Y) (h.from Z) :=
  rfl

@[simp]
theorem binaryFan_snd (T Y Z : C) (h : Limits.IsTerminal T) :
    (binaryFan T Y Z h).snd = snd (h.from Y) (h.from Z) :=
  rfl

def binaryFanIsBinaryProduct (T Y Z : C) (h : Limits.IsTerminal T) :
    Limits.IsLimit (binaryFan T Y Z h) :=
  Limits.BinaryFan.IsLimit.mk (binaryFan T Y Z h)
    (fun a b => lift a b)
    (by simp)
    (by simp)
    (fun f g m h₁ h₂ => by cat_disch)

def cartesianMonoidalCategory (T : C) (h : Limits.IsTerminal T := by infer_instance) :
    CartesianMonoidalCategory C :=
  ofChosenFiniteProducts (C := C)
    ⟨Limits.asEmptyCone T, h⟩
    (fun Y Z ↦ ⟨_, binaryFanIsBinaryProduct T Y Z h⟩)

end ChosenPullbacks

namespace ChosenPullbacksAlong

variable {X : C}

@[reassoc (attr := simp)]
theorem pullback_map_left_fst {Z : C} {Y Y' : Over X} (f : Y' ⟶ Y) (g : Z ⟶ X)
    [ChosenPullbacksAlong g] :
    ((pullback g).map f).left ≫ ChosenPullbacksAlong.fst Y.hom g =
      ChosenPullbacksAlong.fst Y'.hom g ≫ f.left := by
  sorry

@[reassoc (attr := simp)]
theorem pullback_map_left_snd {Z : C} {Y Y' : Over X} (f : Y' ⟶ Y) (g : Z ⟶ X)
    [ChosenPullbacksAlong g] :
    ((pullback g).map f).left ≫ ChosenPullbacksAlong.snd Y.hom g =
      ChosenPullbacksAlong.snd Y'.hom g :=
  Over.w ((pullback g).map f)

end ChosenPullbacksAlong

namespace ChosenPullbacks

open ChosenPullbacksAlong

attribute [instance] cartesianMonoidalCategoryOver

variable {X : C}

/-- The push-pull object `(pullback Z.hom).obj Y` is isomorphic to the cartesian product
`Y ⊗ Z` in the slice category `Over X`.
Note: Whereas the left hand-side is defined in a computable way, the right hand-side relies on
the non-constructive monoidal structure on `Over X` so this isomorphism is noncomputable.
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
      simp
      ext
      · simp only [Over.map_obj_left, whiskerRight_fst]
        apply pullback_map_left_fst
      · rw [Over.comp_left, Over.map_map_left]
        simp only [Over.map_obj_left, Over.tensorObj_left, whiskerRight_snd]
        simp [Over.snd_eq_snd'])

@[simp]
theorem pullbackMapNatIsoTensorRight_hom_app [ChosenPullbacks C] {Y : Over X} (Z : Over X) :
    (pullbackMapNatIsoTensorRight Z).hom.app Y = (mapPullbackIsoProd Y Z).hom := by
  cat_disch

def _root_.Over.mapIsoMapLeft {Y Z : Over X} (g : Y ⟶ Z) :
    Over.map g ≅ Y.iteratedSliceEquiv.functor ⋙ Over.map g.left ⋙ Z.iteratedSliceEquiv.inverse :=
  NatIso.ofComponents
    (fun A => by
      simp [Over.map_obj_left]
      fapply Over.isoMk
      · simp
        apply Iso.refl
      · sorry
        )


/-
A
|
|  g
Z ---⟶  Y
 \     /
  \  /
    X

-/

/-- If `C` has chosen pullbacks, then `Over I` also has chosen pullbacks`. -/
instance chosenPullbacksOver [ChosenPullbacks C] :
    ChosenPullbacks (Over X) := fun {Y Z : Over X} g => {
  pullback := Y.iteratedSliceEquiv.functor ⋙ pullback g.left ⋙ Z.iteratedSliceEquiv.inverse,
  mapPullbackAdj.unit.app A :=
    Over.homMk (
      Over.homMk (
          (mapPullbackAdj g.left).unit.app (Over.mk (Y:= A.left.left) A.hom.left) |>.left)
            (by simp; sorry)) (by cat_disch)
  mapPullbackAdj.counit.app := sorry
    }


end ChosenPullbacks

namespace ExponentiableMorphism

open BraidedCategory ChosenPullbacksAlong ChosenPullbacks

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- A exponentiable morphism is an exponentiable object in the slice category of its codomain. -/
def exponentiableOverMk [ChosenPullbacks C] {X I : C} (f : X ⟶ I)
    [ExponentiableMorphism f] :
    Exponentiable (Over.mk f) where
  rightAdj := pullback f ⋙ pushforward f
  adj := ofNatIsoLeft (F:= pullback f ⋙ Over.map f)
    ((pullbackAdjPushforward f).comp (mapPullbackAdj f))
    ((pullbackMapNatIsoTensorRight <| Over.mk f) ≪≫ (tensorLeftIsoTensorRight _).symm)

-- attribute [local instance] cartesianMonoidalCategory

-- instance foo [ChosenPullbacks C] : CartesianMonoidalCategory C :=
--   cartesianMonoidalCategory T h

instance [CartesianMonoidalCategory C] [ChosenPullbacks C] (X : C) [Exponentiable X] :
    ChosenPullbacksAlong (curryId X) := by
  infer_instance

/-- If `X : Over I` is an exponentiable object then `X.hom : X.left ⟶ I` is an exponentiable
morphism. Here the pushforward functor along a morphism `f : I ⟶ J` is defined by the way of the
section functor `Over (Over.mk f) ⥤ Over J`. -/
def ofExponentiable [ChosenPullbacks C] {I : C} (X : Over I)
    [Exponentiable X] :
    ExponentiableMorphism X.hom :=
  ⟨X.iteratedSliceEquiv.inverse ⋙ Over.sections X, by
    refine ofNatIsoLeft (Adjunction.comp ?_ ?_) (toOverIteratedSliceForwardIsoPullback X.hom)
    · exact Over.toOverSectionsAdj X
    · apply (Over.mk X.hom).iteratedSliceEquiv.toAdjunction⟩

end ExponentiableMorphism

variable (C)

/-- A category `ChosenPushforwards` if every morphism is exponentiable. -/
class ChosenPushforwards [ChosenPullbacks C] where
  /-- A function assigning to every morphism `f : I ⟶ J` an exponentiable structure. -/
  exponentiable {I J : C} (f : I ⟶ J) : ExponentiableMorphism f := by infer_instance

namespace ChosenPushforwards

open Over ExponentiableMorphism

variable {C} [ChosenPullbacks C] [ChosenPushforwards C]

/-- In a category where pushforwards exists along all morphisms, every slice category `Over I` is
cartesian closed. -/
instance cartesianClosedOver (I : C) :
    CartesianClosed (Over I) where
  closed X := @exponentiableOverMk _ _ _ _ _ X.hom (ChosenPushforwards.exponentiable X.hom)

end ChosenPushforwards

namespace CartesianClosedOver

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

variable [ChosenPullbacks C] [LocallyCartesianClosed C]

/-- Every morphism in a locally cartesian closed category is exponentiable. -/
instance {I J : C} (f : I ⟶ J) : ExponentiableMorphism f := ChosenPushforwards.exponentiable f

attribute [instance] cartesianMonoidalCategory
attribute [instance] cartesianMonoidalCategoryOver



#exit

variable {D : Type u₂} [Category.{v₂} D]

example {F : C ⥤ C} {G : C ⥤ C} {e : C ≌ D} (adjFG : F ⊣ G) :
    e.inverse ⋙ F ⋙ e.functor ⊣ e.inverse ⋙ G ⋙ e.functor where
  unit.app X := by
    simp
    let d1 := e.unitIso.hom.app
    simp at d1
    let d2 := G.map (d1 X)
    let d3 : R.obj X ⟶ G.obj (F.obj (R.obj X)) := adjFG.unit.app (R.obj X)
    let d4 := d3 ≫ d2
    let d5 := L.map d4
    let d6 := adjLR.counit.app (L.obj (R.obj X))
    sorry
  counit.app := sorry




/-- A locally cartesian closed category with a terminal object is cartesian closed. -/
def cartesianClosed (T : C) (h : Limits.IsTerminal T) :
    letI := cartesianMonoidalCategory T h
    CartesianClosed C := letI := cartesianMonoidalCategory T h; ⟨fun X => {
      rightAdj := toOverUnit C ⋙ exp ((toOverUnit C).obj X) ⋙ Over.forget _
      adj := by
        let adj1 : Over.forget _ ⊣ toOver _ := forgetAdjToOver (𝟙_ C)
        let iso1 : toOver _ ≅ toOverUnit C := toOverIsoToOverUnit
        let adj2 : Over.forget _ ⊣ toOverUnit C := by exact adj1.ofNatIsoRight iso1
        fapply Adjunction.ofNatIsoLeft
        · exact toOverUnit C ⋙ tensorLeft ((toOverUnit C).obj X) ⋙ Over.forget (𝟙_ C)
        · nth_rewrite 2 [← CategoryTheory.Functor.assoc]
          apply adj2.comp

        · sorry
    }⟩


#check cartesianClosedOfEquiv

/-- A locally cartesian closed category with a terminal object is cartesian closed. -/
noncomputable def cartesianClosed' (T : C) (h : Limits.IsTerminal T) :
    letI := cartesianMonoidalCategory T h
    CartesianClosed C :=
    let := cartesianMonoidalCategory T h
    cartesianClosedOfEquiv <| equivToOverUnit C

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
