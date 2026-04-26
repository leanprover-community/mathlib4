/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Monomorphisms over a fixed object

As preparation for defining `Subobject X`, we set up the theory for
`MonoOver X := { f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not yet a partial order.

`Subobject X` will be defined as the skeletalization of `MonoOver X`.

We provide
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X`
* `def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y`
* `def «exists» [HasImages C] (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y`

and prove their basic properties and relationships.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Kim Morrison.

-/

@[expose] public section


universe w' w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

/-- The object property in `Over X` of the structure morphism being a monomorphism. -/
abbrev Over.isMono (X : C) : ObjectProperty (Over X) :=
  fun f : Over X => Mono f.hom

/-- The category of monomorphisms into `X` as a full subcategory of the over category.
This isn't skeletal, so it's not a partial order.

Later we define `Subobject X` as the quotient of this by isomorphisms.
-/
abbrev MonoOver (X : C) := (Over.isMono X).FullSubcategory

namespace MonoOver

instance mono_obj_hom (S : MonoOver X) : Mono S.obj.hom := S.2

/-- Construct a `MonoOver X`. -/
@[simps]
def mk {X A : C} (f : A ⟶ X) [hf : Mono f] : MonoOver X where
  obj := Over.mk f
  property := hf

@[deprecated (since := "2025-12-18")] alias mk' := mk

/-- The inclusion from monomorphisms over X to morphisms over X. -/
abbrev forget (X : C) : MonoOver X ⥤ Over X :=
  ObjectProperty.ι _

instance : CoeOut (MonoOver X) C where coe Y := Y.obj.left

@[simp]
theorem forget_obj_left {f} : ((forget X).obj f).left = (f : C) :=
  rfl

@[simp]
theorem mk_coe {X A : C} (f : A ⟶ X) [Mono f] : (mk f : C) = A :=
  rfl

@[deprecated (since := "2025-12-18")] alias mk'_coe' := mk_coe

/-- Convenience notation for the underlying arrow of a monomorphism over X. -/
abbrev arrow (f : MonoOver X) : (f : C) ⟶ X := f.obj.hom

@[simp]
theorem mk_arrow {X A : C} (f : A ⟶ X) [Mono f] : (mk f).arrow = f :=
  rfl

@[deprecated (since := "2025-12-18")] alias mk'_arrow := mk_arrow

theorem forget_obj_hom {f} : ((forget X).obj f).hom = f.arrow := rfl

/-- The forget functor `MonoOver X ⥤ Over X` is fully faithful. -/
def fullyFaithfulForget (X : C) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance mono (f : MonoOver X) : Mono f.arrow :=
  f.property

instance {X : C} {f : MonoOver X} : Mono ((MonoOver.forget X).obj f).hom := f.mono

/-- The category of monomorphisms over X is a thin category,
which makes defining its skeleton easy. -/
instance isThin {X : C} : Quiver.IsThin (MonoOver X) := fun f g =>
  ⟨by
    intro h₁ h₂
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    rw [← cancel_mono g.arrow]
    erw [Over.w h₁.hom]
    erw [Over.w h₂.hom]⟩

@[reassoc]
theorem w {f g : MonoOver X} (k : f ⟶ g) : k.hom.left ≫ g.arrow = f.arrow :=
  Over.w _

/-- Convenience constructor for a morphism in monomorphisms over `X`. -/
abbrev homMk {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left)
    (w : h ≫ g.arrow = f.arrow := by aesop_cat) : f ⟶ g :=
  InducedCategory.homMk (Over.homMk h w)

/-- Convenience constructor for an isomorphism in monomorphisms over `X`. -/
@[simps]
def isoMk {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left)
    (w : h.hom ≫ g.arrow = f.arrow := by cat_disch) : f ≅ g where
  hom := homMk h.hom w
  inv := homMk h.inv (by rw [h.inv_comp_eq, w])

/-- If `f : MonoOver X`, then `mk' f.arrow` is of course just `f`, but not definitionally, so we
package it as an isomorphism. -/
@[simps!]
def mkArrowIso {X : C} (f : MonoOver X) : mk f.arrow ≅ f :=
  isoMk (Iso.refl _)

@[deprecated (since := "2025-12-18")] alias mk'ArrowIso := mkArrowIso

instance {A B : MonoOver X} (f : A ⟶ B) [IsIso f] : IsIso f.hom.left :=
  inferInstanceAs (IsIso ((MonoOver.forget _ ⋙ Over.forget _).map f))

lemma isIso_iff_isIso_hom_left {A B : MonoOver X} (f : A ⟶ B) :
    IsIso f ↔ IsIso f.hom.left :=
  (isIso_iff_of_reflects_iso _ (MonoOver.forget X ⋙ Over.forget _)).symm

@[deprecated (since := "2025-12-18")] alias isIso_iff_isIso_left := isIso_iff_isIso_hom_left

/-- Lift a functor between over categories to a functor between `MonoOver` categories,
given suitable evidence that morphisms are taken to monomorphisms.
-/
@[simps!]
def lift {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    MonoOver Y ⥤ MonoOver X :=
  ObjectProperty.lift _ (forget _ ⋙ F) h

/-- Isomorphic functors `Over Y ⥤ Over X` lift to isomorphic functors `MonoOver Y ⥤ MonoOver X`.
-/
def liftIso {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂) : lift F₁ h₁ ≅ lift F₂ h₂ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget X) (isoWhiskerLeft (MonoOver.forget Y) i)

/-- `MonoOver.lift` commutes with composition of functors. -/
def liftComp {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁ h₂) :
    lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) fun f => h₂ ⟨_, h₁ f⟩ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

/-- `MonoOver.lift` preserves the identity functor. -/
def liftId : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

@[simp]
theorem lift_comm (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    lift F h ⋙ MonoOver.forget X = MonoOver.forget Y ⋙ F :=
  rfl

@[simp]
theorem lift_obj_arrow {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) (f : MonoOver Y) :
    ((lift F h).obj f).arrow = (F.obj ((forget Y).obj f)).hom :=
  rfl

/-- Monomorphisms over an object `f : Over A` in an over category
are equivalent to monomorphisms over the source of `f`.
-/
def slice {A : C} {f : Over A}
    (h₁ : ∀ (g : MonoOver f),
      Mono ((Over.iteratedSliceEquiv f).functor.obj ((forget f).obj g)).hom)
    (h₂ : ∀ (g : MonoOver f.left),
      Mono ((Over.iteratedSliceEquiv f).inverse.obj ((forget f.left).obj g)).hom) :
    MonoOver f ≌ MonoOver f.left where
  functor := MonoOver.lift f.iteratedSliceEquiv.functor h₁
  inverse := MonoOver.lift f.iteratedSliceEquiv.inverse h₂
  unitIso :=
    MonoOver.liftId.symm ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.unitIso ≪≫ (MonoOver.liftComp _ _ _ _).symm
  counitIso :=
    MonoOver.liftComp _ _ _ _ ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.counitIso ≪≫ MonoOver.liftId

section Limits

variable {J : Type u₃} [Category.{v₃} J] (X : C)

set_option backward.isDefEq.respectTransparency false in
instance : (Over.isMono X).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := fun F ⟨p, hp⟩ ↦ ⟨fun g h e ↦ by
    refine (WithTerminal.isLimitEquiv.invFun p.isLimit).hom_ext (fun j ↦ ?_)
    cases j with
    | of j => have := hp j; rw [← cancel_mono ((p.diag.obj j).hom)]; simpa
    | star => exact e⟩

instance hasLimit (F : J ⥤ MonoOver X) [HasLimit (F ⋙ (Over.isMono X).ι)] :
    HasLimit F :=
  hasLimit_of_closedUnderLimits _ _ _

instance hasLimitsOfShape [HasLimitsOfShape J (Over X)] :
    HasLimitsOfShape J (MonoOver X) where

instance hasFiniteLimits [HasFiniteLimits (Over X)] : HasFiniteLimits (MonoOver X) where
  out _ _ _ := inferInstance

instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} (Over X)] :
    HasLimitsOfSize.{w, w'} (MonoOver X) where

end Limits

section Colimits

variable [HasCoproducts C] [HasStrongEpiMonoFactorisations C] {J : Type u₂} [Category.{v₂} J]

/-- A helper function, providing the strong epi-mono factorization used construct to colimits. -/
def strongEpiMonoFactorisationSigmaDesc (F : J ⥤ MonoOver Y) :
    StrongEpiMonoFactorisation (Sigma.desc fun i ↦ (F.obj i).arrow) :=
  Classical.choice <| HasStrongEpiMonoFactorisations.has_fac (Sigma.desc fun i ↦ (F.obj i).arrow)

set_option backward.isDefEq.respectTransparency false in
/-- If a category `C` has strong epi-mono factorization, for any `Y : C` and functor
`F : J ⥤ MonoOver Y`, there is a cocone under F. -/
def coconeOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) :
    Cocone F where
  pt := MonoOver.mk ((strongEpiMonoFactorisationSigmaDesc F).m)
  ι.app j := homMk (Sigma.ι (fun i ↦ (F.obj i : C)) j ≫
    (strongEpiMonoFactorisationSigmaDesc F).e)

set_option backward.isDefEq.respectTransparency false in
lemma commSqOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) (c : Cocone F) :
    CommSq (Sigma.desc fun i ↦ (c.ι.app i).hom.left) (strongEpiMonoFactorisationSigmaDesc F).e
      c.pt.arrow (strongEpiMonoFactorisationSigmaDesc F).m where

/-- A helper function, providing the lift structure used to construct colimits. -/
def liftStructOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) (c : Cocone F) :
    (commSqOfHasStrongEpiMonoFactorisation F c).LiftStruct :=
  Classical.choice
    (((strongEpiMonoFactorisationSigmaDesc F).e_strong_epi.llp _).sq_hasLift
      (commSqOfHasStrongEpiMonoFactorisation F c)).exists_lift

/-- The cocone `coconeOfHasStrongEpiMonoFactorisation F` is a colimit -/
def isColimitCoconeOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) :
    IsColimit (coconeOfHasStrongEpiMonoFactorisation F) where
  desc c := homMk (liftStructOfHasStrongEpiMonoFactorisation F c).l
    (liftStructOfHasStrongEpiMonoFactorisation F c).fac_right

instance hasColimitsOfSize_of_hasStrongEpiMonoFactorisations :
    HasColimitsOfSize.{w, w'} (MonoOver Y) where
  has_colimits_of_shape _ _ :=
    ⟨fun F ↦
      ⟨coconeOfHasStrongEpiMonoFactorisation F, isColimitCoconeOfHasStrongEpiMonoFactorisation F⟩⟩

end Colimits

section Pullback

variable [HasPullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `MonoOver Y ⥤ MonoOver X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X :=
  MonoOver.lift (Over.pullback f) (fun g => by
    haveI : Mono ((forget Y).obj g).hom := (inferInstance : Mono g.arrow)
    apply pullback.snd_of_mono)

/-- pullback commutes with composition (up to a natural isomorphism) -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  liftIso _ _ (Over.pullbackComp _ _) ≪≫ (liftComp _ _ _ _).symm

/-- pullback preserves the identity (up to a natural isomorphism) -/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ Over.pullbackId ≪≫ liftId

@[simp]
theorem pullback_obj_left (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g : C) = Limits.pullback g.arrow f :=
  rfl

@[simp]
theorem pullback_obj_arrow (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g).arrow = pullback.snd _ _ :=
  rfl

end Pullback

section IsPullback

/--
Given two monomorphisms `S` and `T` over `X` and `Y` and two morphisms `f` and `f'` between them
forming the following pullback square:

```
(T : C) -f'-> (S : C)
   |             |
T.arrow       S.arrow
   |             |
   v             v
   Y -----f----> X
```

we get an isomorphism between `T` and the pullback of `S` along `f` through the `pullback` functor.
-/
def pullbackObjIsoOfIsPullback [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (S : MonoOver X)
    (T : MonoOver Y) (f' : (T : C) ⟶ (S : C))
    (h : IsPullback f' T.arrow S.arrow f) :
    (pullback f).obj S ≅ T :=
  isoMk ((IsPullback.isoPullback h).symm)

end IsPullback

section Map

/-- We can map monomorphisms over `X` to monomorphisms over `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y :=
  lift (Over.map f) fun g => mono_comp g.arrow f

/-- `MonoOver.map` commutes with composition (up to a natural isomorphism). -/
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : map (f ≫ g) ≅ map f ⋙ map g :=
  liftIso _ _ (Over.mapComp _ _) ≪≫ (liftComp _ _ _ _).symm

variable (X) in
/-- `MonoOver.map` preserves the identity (up to a natural isomorphism). -/
def mapId : map (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ (Over.mapId X) ≪≫ liftId

@[simp]
theorem map_obj_left (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g : C) = g.obj.left :=
  rfl

@[simp]
theorem map_obj_arrow (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g).arrow = g.arrow ≫ f :=
  rfl

instance full_map (f : X ⟶ Y) [Mono f] : Functor.Full (map f) where
  map_surjective {g h} e := by
    refine ⟨homMk e.hom.left ?_, rfl⟩
    · rw [← cancel_mono f, assoc]
      apply w e

instance faithful_map (f : X ⟶ Y) [Mono f] : Functor.Faithful (map f) where

/-- Isomorphic objects have equivalent `MonoOver` categories.
-/
@[simps]
def mapIso {A B : C} (e : A ≅ B) : MonoOver A ≌ MonoOver B where
  functor := map e.hom
  inverse := map e.inv
  unitIso := ((mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)).symm
  counitIso := (mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)

section

variable (X)

/-- An equivalence of categories `e` between `C` and `D` induces an equivalence between
`MonoOver X` and `MonoOver (e.functor.obj X)` whenever `X` is an object of `C`. -/
@[simps]
def congr (e : C ≌ D) : MonoOver X ≌ MonoOver (e.functor.obj X) where
  functor :=
    lift (Over.post e.functor) fun f => by
      dsimp
      infer_instance
  inverse :=
    (lift (Over.post e.inverse) fun f => by
        dsimp
        infer_instance) ⋙
      (mapIso (e.unitIso.symm.app X)).functor
  unitIso := NatIso.ofComponents fun Y => isoMk (e.unitIso.app Y)
  counitIso := NatIso.ofComponents fun Y => isoMk (e.counitIso.app Y)

end

section

variable [HasPullbacks C]

/-- `map f` is left adjoint to `pullback f` when `f` is a monomorphism -/
def mapPullbackAdj (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  (Over.mapPullbackAdj f).restrictFullyFaithful (fullyFaithfulForget X) (fullyFaithfulForget Y)
    (Iso.refl _) (Iso.refl _)

/-- `MonoOver.map f` followed by `MonoOver.pullback f` is the identity. -/
def pullbackMapSelf (f : X ⟶ Y) [Mono f] : map f ⋙ pullback f ≅ 𝟭 _ :=
  (asIso (MonoOver.mapPullbackAdj f).unit).symm

end

end Map

section Image

variable (f : X ⟶ Y) [HasImage f]

/-- The `MonoOver Y` for the image inclusion for a morphism `f : X ⟶ Y`.
-/
def imageMonoOver (f : X ⟶ Y) [HasImage f] : MonoOver Y :=
  MonoOver.mk (image.ι f)

@[simp]
theorem imageMonoOver_arrow (f : X ⟶ Y) [HasImage f] : (imageMonoOver f).arrow = image.ι f :=
  rfl

end Image

section Image

variable [HasImages C]

/-- Taking the image of a morphism gives a functor `Over X ⥤ MonoOver X`.
-/
@[simps]
def image : Over X ⥤ MonoOver X where
  obj f := imageMonoOver f.hom
  map {f g} k := by
    apply (forget X).preimage _
    apply Over.homMk _ _
    · exact
        image.lift
          { I := Limits.image _
            m := image.ι g.hom
            e := k.left ≫ factorThruImage g.hom }
    · apply image.lift_fac

set_option backward.isDefEq.respectTransparency false in
/-- `MonoOver.image : Over X ⥤ MonoOver X` is left adjoint to
`MonoOver.forget : MonoOver X ⥤ Over X`
-/
def imageForgetAdj : image ⊣ forget X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun f g =>
        { toFun := fun k => by
            apply Over.homMk (factorThruImage f.hom ≫ k.hom.left) _
            rw [assoc, Over.w k.hom]
            apply image.fac
          invFun k :=
            homMk
              (image.lift
                { I := g.obj.left
                  m := g.arrow
                  e := k.left
                  fac := Over.w k }) (image.lift_fac _)
          left_inv _ := Subsingleton.elim _ _
          right_inv k := by ext; simp } }

instance : (forget X).IsRightAdjoint :=
  ⟨_, ⟨imageForgetAdj⟩⟩

instance reflective : Reflective (forget X) where
  L := image
  adj := imageForgetAdj

/-- Forgetting that a monomorphism over `X` is a monomorphism, then taking its image,
is the identity functor.
-/
def forgetImage : forget X ⋙ image ≅ 𝟭 (MonoOver X) :=
  asIso (Adjunction.counit imageForgetAdj)

end Image

section Exists

variable [HasImages C]

/-- In the case where `f` is not a monomorphism but `C` has images,
we can still take the "forward map" under it, which agrees with `MonoOver.map f`.
-/
def «exists» (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y :=
  forget _ ⋙ Over.map f ⋙ image

instance faithful_exists (f : X ⟶ Y) : Functor.Faithful («exists» f) where

set_option backward.isDefEq.respectTransparency false in
/-- When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
def existsIsoMap (f : X ⟶ Y) [Mono f] : «exists» f ≅ map f :=
  NatIso.ofComponents (by
    intro Z
    suffices (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z) by
      apply (forget _).preimageIso this
    apply Over.isoMk _ _
    · apply imageMonoIsoSource (Z.arrow ≫ f)
    · apply imageMonoIsoSource_hom_self)

/-- `exists` is adjoint to `pullback` when images exist -/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  ((Over.mapPullbackAdj f).comp imageForgetAdj).restrictFullyFaithful
    (fullyFaithfulForget X) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end Exists

end MonoOver

end CategoryTheory
