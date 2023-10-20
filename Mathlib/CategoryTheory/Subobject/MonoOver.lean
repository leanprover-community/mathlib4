/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Adjunction.Reflective

#align_import category_theory.subobject.mono_over from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

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
and was ported to mathlib by Scott Morrison.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

/-- The category of monomorphisms into `X` as a full subcategory of the over category.
This isn't skeletal, so it's not a partial order.

Later we define `Subobject X` as the quotient of this by isomorphisms.
-/
def MonoOver (X : C) :=
  FullSubcategory fun f : Over X => Mono f.hom
#align category_theory.mono_over CategoryTheory.MonoOver

instance (X : C) : Category (MonoOver X) :=
  FullSubcategory.category _

namespace MonoOver

/-- Construct a `MonoOver X`. -/
@[simps]
def mk' {X A : C} (f : A ⟶ X) [hf : Mono f] : MonoOver X where
  obj := Over.mk f
  property := hf
#align category_theory.mono_over.mk' CategoryTheory.MonoOver.mk'

/-- The inclusion from monomorphisms over X to morphisms over X. -/
def forget (X : C) : MonoOver X ⥤ Over X :=
  fullSubcategoryInclusion _
#align category_theory.mono_over.forget CategoryTheory.MonoOver.forget

instance : CoeOut (MonoOver X) C where coe Y := Y.obj.left

@[simp]
theorem forget_obj_left {f} : ((forget X).obj f).left = (f : C) :=
  rfl
#align category_theory.mono_over.forget_obj_left CategoryTheory.MonoOver.forget_obj_left

@[simp]
theorem mk'_coe' {X A : C} (f : A ⟶ X) [Mono f] : (mk' f : C) = A :=
  rfl
#align category_theory.mono_over.mk'_coe' CategoryTheory.MonoOver.mk'_coe'

/-- Convenience notation for the underlying arrow of a monomorphism over X. -/
abbrev arrow (f : MonoOver X) : (f : C) ⟶ X :=
  ((forget X).obj f).hom
#align category_theory.mono_over.arrow CategoryTheory.MonoOver.arrow

@[simp]
theorem mk'_arrow {X A : C} (f : A ⟶ X) [Mono f] : (mk' f).arrow = f :=
  rfl
#align category_theory.mono_over.mk'_arrow CategoryTheory.MonoOver.mk'_arrow

@[simp]
theorem forget_obj_hom {f} : ((forget X).obj f).hom = f.arrow :=
  rfl
#align category_theory.mono_over.forget_obj_hom CategoryTheory.MonoOver.forget_obj_hom

instance : Full (forget X) :=
  FullSubcategory.full _

instance : Faithful (forget X) :=
  FullSubcategory.faithful _

instance mono (f : MonoOver X) : Mono f.arrow :=
  f.property
#align category_theory.mono_over.mono CategoryTheory.MonoOver.mono

/-- The category of monomorphisms over X is a thin category,
which makes defining its skeleton easy. -/
instance isThin {X : C} : Quiver.IsThin (MonoOver X) := fun f g =>
  ⟨by
    intro h₁ h₂
    apply Over.OverMorphism.ext
    erw [← cancel_mono g.arrow, Over.w h₁, Over.w h₂]⟩
#align category_theory.mono_over.is_thin CategoryTheory.MonoOver.isThin

@[reassoc]
theorem w {f g : MonoOver X} (k : f ⟶ g) : k.left ≫ g.arrow = f.arrow :=
  Over.w _
#align category_theory.mono_over.w CategoryTheory.MonoOver.w

/-- Convenience constructor for a morphism in monomorphisms over `X`. -/
abbrev homMk {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left)
    (w : h ≫ g.arrow = f.arrow := by aesop_cat) : f ⟶ g :=
  Over.homMk h w
#align category_theory.mono_over.hom_mk CategoryTheory.MonoOver.homMk

/-- Convenience constructor for an isomorphism in monomorphisms over `X`. -/
@[simps]
def isoMk {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left)
    (w : h.hom ≫ g.arrow = f.arrow := by aesop_cat) : f ≅ g where
  hom := homMk h.hom w
  inv := homMk h.inv (by rw [h.inv_comp_eq, w])
#align category_theory.mono_over.iso_mk CategoryTheory.MonoOver.isoMk

/-- If `f : MonoOver X`, then `mk' f.arrow` is of course just `f`, but not definitionally, so we
    package it as an isomorphism. -/
@[simp]
def mk'ArrowIso {X : C} (f : MonoOver X) : mk' f.arrow ≅ f :=
  isoMk (Iso.refl _)
#align category_theory.mono_over.mk'_arrow_iso CategoryTheory.MonoOver.mk'ArrowIso

/-- Lift a functor between over categories to a functor between `MonoOver` categories,
given suitable evidence that morphisms are taken to monomorphisms.
-/
@[simps]
def lift {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    MonoOver Y ⥤ MonoOver X where
  obj f := ⟨_, h f⟩
  map k := (MonoOver.forget X).preimage ((MonoOver.forget Y ⋙ F).map k)
#align category_theory.mono_over.lift CategoryTheory.MonoOver.lift

/-- Isomorphic functors `Over Y ⥤ Over X` lift to isomorphic functors `MonoOver Y ⥤ MonoOver X`.
-/
def liftIso {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂) : lift F₁ h₁ ≅ lift F₂ h₂ :=
  fullyFaithfulCancelRight (MonoOver.forget X) (isoWhiskerLeft (MonoOver.forget Y) i)
#align category_theory.mono_over.lift_iso CategoryTheory.MonoOver.liftIso

/-- `MonoOver.lift` commutes with composition of functors. -/
def liftComp {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁ h₂) :
    lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) fun f => h₂ ⟨_, h₁ f⟩ :=
  fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)
#align category_theory.mono_over.lift_comp CategoryTheory.MonoOver.liftComp

/-- `MonoOver.lift` preserves the identity functor. -/
def liftId : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _ :=
  fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)
#align category_theory.mono_over.lift_id CategoryTheory.MonoOver.liftId

@[simp]
theorem lift_comm (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    lift F h ⋙ MonoOver.forget X = MonoOver.forget Y ⋙ F :=
  rfl
#align category_theory.mono_over.lift_comm CategoryTheory.MonoOver.lift_comm

@[simp]
theorem lift_obj_arrow {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) (f : MonoOver Y) :
    ((lift F h).obj f).arrow = (F.obj ((forget Y).obj f)).hom :=
  rfl
#align category_theory.mono_over.lift_obj_arrow CategoryTheory.MonoOver.lift_obj_arrow

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
#align category_theory.mono_over.slice CategoryTheory.MonoOver.slice

section Pullback

variable [HasPullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `MonoOver Y ⥤ MonoOver X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X :=
  MonoOver.lift (Over.pullback f) (fun g => by
    haveI : Mono ((forget Y).obj g).hom := (inferInstance : Mono g.arrow)
    apply pullback.snd_of_mono)
#align category_theory.mono_over.pullback CategoryTheory.MonoOver.pullback

/-- pullback commutes with composition (up to a natural isomorphism) -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  liftIso _ _ (Over.pullbackComp _ _) ≪≫ (liftComp _ _ _ _).symm
#align category_theory.mono_over.pullback_comp CategoryTheory.MonoOver.pullbackComp

/-- pullback preserves the identity (up to a natural isomorphism) -/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ Over.pullbackId ≪≫ liftId
#align category_theory.mono_over.pullback_id CategoryTheory.MonoOver.pullbackId

@[simp]
theorem pullback_obj_left (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g : C) = Limits.pullback g.arrow f :=
  rfl
#align category_theory.mono_over.pullback_obj_left CategoryTheory.MonoOver.pullback_obj_left

@[simp]
theorem pullback_obj_arrow (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g).arrow = pullback.snd :=
  rfl
#align category_theory.mono_over.pullback_obj_arrow CategoryTheory.MonoOver.pullback_obj_arrow

end Pullback

section Map

attribute [instance] mono_comp

/-- We can map monomorphisms over `X` to monomorphisms over `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y :=
  lift (Over.map f) fun g => by apply mono_comp g.arrow f
#align category_theory.mono_over.map CategoryTheory.MonoOver.map

/-- `MonoOver.map` commutes with composition (up to a natural isomorphism). -/
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : map (f ≫ g) ≅ map f ⋙ map g :=
  liftIso _ _ (Over.mapComp _ _) ≪≫ (liftComp _ _ _ _).symm
#align category_theory.mono_over.map_comp CategoryTheory.MonoOver.mapComp

/-- `MonoOver.map` preserves the identity (up to a natural isomorphism). -/
def mapId : map (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ Over.mapId ≪≫ liftId
#align category_theory.mono_over.map_id CategoryTheory.MonoOver.mapId

@[simp]
theorem map_obj_left (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g : C) = g.obj.left :=
  rfl
#align category_theory.mono_over.map_obj_left CategoryTheory.MonoOver.map_obj_left

@[simp]
theorem map_obj_arrow (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g).arrow = g.arrow ≫ f :=
  rfl
#align category_theory.mono_over.map_obj_arrow CategoryTheory.MonoOver.map_obj_arrow

instance fullMap (f : X ⟶ Y) [Mono f] : Full (map f) where
  preimage {g h} e := by
    refine' homMk e.left _
    rw [← cancel_mono f, assoc]
    apply w e
#align category_theory.mono_over.full_map CategoryTheory.MonoOver.fullMap

instance faithful_map (f : X ⟶ Y) [Mono f] : Faithful (map f) where
#align category_theory.mono_over.faithful_map CategoryTheory.MonoOver.faithful_map

/-- Isomorphic objects have equivalent `MonoOver` categories.
-/
@[simps]
def mapIso {A B : C} (e : A ≅ B) : MonoOver A ≌ MonoOver B where
  functor := map e.hom
  inverse := map e.inv
  unitIso := ((mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ mapId).symm
  counitIso := (mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ mapId
#align category_theory.mono_over.map_iso CategoryTheory.MonoOver.mapIso

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
#align category_theory.mono_over.congr CategoryTheory.MonoOver.congr

end

section

variable [HasPullbacks C]

/-- `map f` is left adjoint to `pullback f` when `f` is a monomorphism -/
def mapPullbackAdj (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  Adjunction.restrictFullyFaithful (forget X) (forget Y) (Over.mapPullbackAdj f) (Iso.refl _)
    (Iso.refl _)
#align category_theory.mono_over.map_pullback_adj CategoryTheory.MonoOver.mapPullbackAdj

/-- `MonoOver.map f` followed by `MonoOver.pullback f` is the identity. -/
def pullbackMapSelf (f : X ⟶ Y) [Mono f] : map f ⋙ pullback f ≅ 𝟭 _ :=
  (asIso (MonoOver.mapPullbackAdj f).unit).symm
#align category_theory.mono_over.pullback_map_self CategoryTheory.MonoOver.pullbackMapSelf

end

end Map

section Image

variable (f : X ⟶ Y) [HasImage f]

/-- The `MonoOver Y` for the image inclusion for a morphism `f : X ⟶ Y`.
-/
def imageMonoOver (f : X ⟶ Y) [HasImage f] : MonoOver Y :=
  MonoOver.mk' (image.ι f)
#align category_theory.mono_over.image_mono_over CategoryTheory.MonoOver.imageMonoOver

@[simp]
theorem imageMonoOver_arrow (f : X ⟶ Y) [HasImage f] : (imageMonoOver f).arrow = image.ι f :=
  rfl
#align category_theory.mono_over.image_mono_over_arrow CategoryTheory.MonoOver.imageMonoOver_arrow

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
    refine'
      image.lift
        { I := Limits.image _
          m := image.ι g.hom
          e := k.left ≫ factorThruImage g.hom }
    apply image.lift_fac
#align category_theory.mono_over.image CategoryTheory.MonoOver.image

/-- `MonoOver.image : Over X ⥤ MonoOver X` is left adjoint to
`MonoOver.forget : MonoOver X ⥤ Over X`
-/
def imageForgetAdj : image ⊣ forget X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun f g =>
        { toFun := fun k => by
            apply Over.homMk (factorThruImage f.hom ≫ k.left) _
            change (factorThruImage f.hom ≫ k.left) ≫ _ = f.hom
            rw [assoc, Over.w k]
            apply image.fac
          invFun := fun k => by
            refine' Over.homMk _ _
            refine'
              image.lift
                { I := g.obj.left
                  m := g.arrow
                  e := k.left
                  fac := Over.w k }
            apply image.lift_fac
          left_inv := fun k => Subsingleton.elim _ _
          right_inv := fun k => by
            ext1
            change factorThruImage _ ≫ image.lift _ = _
            rw [← cancel_mono g.arrow, assoc, image.lift_fac, image.fac f.hom]
            exact (Over.w k).symm } }
#align category_theory.mono_over.image_forget_adj CategoryTheory.MonoOver.imageForgetAdj

instance : IsRightAdjoint (forget X) where
  left := image
  adj := imageForgetAdj

instance reflective : Reflective (forget X) where
#align category_theory.mono_over.reflective CategoryTheory.MonoOver.reflective

/-- Forgetting that a monomorphism over `X` is a monomorphism, then taking its image,
is the identity functor.
-/
def forgetImage : forget X ⋙ image ≅ 𝟭 (MonoOver X) :=
  asIso (Adjunction.counit imageForgetAdj)
#align category_theory.mono_over.forget_image CategoryTheory.MonoOver.forgetImage

end Image

section Exists

variable [HasImages C]

/-- In the case where `f` is not a monomorphism but `C` has images,
we can still take the "forward map" under it, which agrees with `MonoOver.map f`.
-/
def «exists» (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y :=
  forget _ ⋙ Over.map f ⋙ image
#align category_theory.mono_over.exists CategoryTheory.MonoOver.exists

instance faithful_exists (f : X ⟶ Y) : Faithful («exists» f) where
#align category_theory.mono_over.faithful_exists CategoryTheory.MonoOver.faithful_exists

/-- When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
def existsIsoMap (f : X ⟶ Y) [Mono f] : «exists» f ≅ map f :=
  NatIso.ofComponents (by
    intro Z
    suffices (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z) by
      apply (forget _).preimageIso this
    apply Over.isoMk _ _
    apply imageMonoIsoSource (Z.arrow ≫ f)
    apply imageMonoIsoSource_hom_self)
#align category_theory.mono_over.exists_iso_map CategoryTheory.MonoOver.existsIsoMap

/-- `exists` is adjoint to `pullback` when images exist -/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  Adjunction.restrictFullyFaithful (forget X) (𝟭 _) ((Over.mapPullbackAdj f).comp imageForgetAdj)
    (Iso.refl _) (Iso.refl _)
#align category_theory.mono_over.exists_pullback_adj CategoryTheory.MonoOver.existsPullbackAdj

end Exists

end MonoOver

end CategoryTheory
