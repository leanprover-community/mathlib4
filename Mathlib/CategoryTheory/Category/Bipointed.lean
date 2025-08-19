/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Category.Pointed

/-!
# The category of bipointed types

This defines `Bipointed`, the category of bipointed types.

## TODO

Monoidal structure
-/


open CategoryTheory

universe u

/-- The category of bipointed types. -/
structure Bipointed : Type (u + 1) where
  /-- The underlying type of a bipointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair. -/
  toProd : X × X

namespace Bipointed

instance : CoeSort Bipointed Type* := ⟨Bipointed.X⟩

/-- Turns a bipointing into a bipointed type. -/
abbrev of {X : Type*} (to_prod : X × X) : Bipointed :=
  ⟨X, to_prod⟩

theorem coe_of {X : Type*} (to_prod : X × X) : ↥(of to_prod) = X :=
  rfl

alias _root_.Prod.Bipointed := of

instance : Inhabited Bipointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Bipointed`. -/
@[ext]
protected structure Hom (X Y : Bipointed.{u}) : Type u where
  /-- The underlying function of a morphism of bipointed types. -/
  toFun : X → Y
  map_fst : toFun X.toProd.1 = Y.toProd.1
  map_snd : toFun X.toProd.2 = Y.toProd.2

namespace Hom

/-- The identity morphism of `X : Bipointed`. -/
@[simps]
nonrec def id (X : Bipointed) : Bipointed.Hom X X :=
  ⟨id, rfl, rfl⟩

instance (X : Bipointed) : Inhabited (Bipointed.Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Bipointed`. -/
@[simps]
def comp {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y Z) :
    Bipointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_fst, g.map_fst], by
    rw [Function.comp_apply, f.map_snd, g.map_snd]⟩

end Hom

instance largeCategory : LargeCategory Bipointed where
  Hom := Bipointed.Hom
  id := Hom.id
  comp := @Hom.comp

/-- The subtype of functions corresponding to the morphisms in `Bipointed`. -/
abbrev HomSubtype (X Y : Bipointed) :=
  { f : X → Y // f X.toProd.1 = Y.toProd.1 ∧ f X.toProd.2 = Y.toProd.2 }

instance (X Y : Bipointed) : FunLike (HomSubtype X Y) X Y where
  coe f := f
  coe_injective' _ _ := Subtype.ext

instance hasForget : ConcreteCategory Bipointed HomSubtype where
  hom f := ⟨f.1, ⟨f.2, f.3⟩⟩
  ofHom f := ⟨f.1, f.2.1, f.2.2⟩

/-- Swaps the pointed elements of a bipointed type. `Prod.swap` as a functor. -/
@[simps]
def swap : Bipointed ⥤ Bipointed where
  obj X := ⟨X, X.toProd.swap⟩
  map f := ⟨f.toFun, f.map_snd, f.map_fst⟩

/-- The equivalence between `Bipointed` and itself induced by `Prod.swap` both ways. -/
@[simps!]
def swapEquiv : Bipointed ≌ Bipointed where
  functor := swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl

end Bipointed

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the second point. -/
def bipointedToPointedFst : Bipointed ⥤ Pointed where
  obj X := ⟨X, X.toProd.1⟩
  map f := ⟨f.toFun, f.map_fst⟩

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the first point. -/
def bipointedToPointedSnd : Bipointed ⥤ Pointed where
  obj X := ⟨X, X.toProd.2⟩
  map f := ⟨f.toFun, f.map_snd⟩

@[simp]
theorem bipointedToPointedFst_comp_forget :
    bipointedToPointedFst ⋙ forget Pointed = forget Bipointed :=
  rfl

@[simp]
theorem bipointedToPointedSnd_comp_forget :
    bipointedToPointedSnd ⋙ forget Pointed = forget Bipointed :=
  rfl

@[simp]
theorem swap_comp_bipointedToPointedFst :
    Bipointed.swap ⋙ bipointedToPointedFst = bipointedToPointedSnd :=
  rfl

@[simp]
theorem swap_comp_bipointedToPointedSnd :
    Bipointed.swap ⋙ bipointedToPointedSnd = bipointedToPointedFst :=
  rfl

/-- The functor from `Pointed` to `Bipointed` which bipoints the point. -/
def pointedToBipointed : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨X, X.point, X.point⟩
  map f := ⟨f.toFun, f.map_point, f.map_point⟩

/-- The functor from `Pointed` to `Bipointed` which adds a second point. -/
def pointedToBipointedFst : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨Option X, X.point, none⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

/-- The functor from `Pointed` to `Bipointed` which adds a first point. -/
def pointedToBipointedSnd : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨Option X, none, X.point⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

@[simp]
theorem pointedToBipointedFst_comp_swap :
    pointedToBipointedFst ⋙ Bipointed.swap = pointedToBipointedSnd :=
  rfl

@[simp]
theorem pointedToBipointedSnd_comp_swap :
    pointedToBipointedSnd ⋙ Bipointed.swap = pointedToBipointedFst :=
  rfl

/-- `BipointedToPointed_fst` is inverse to `PointedToBipointed`. -/
@[simps!]
def pointedToBipointedCompBipointedToPointedFst :
    pointedToBipointed ⋙ bipointedToPointedFst ≅ 𝟭 _ :=
  NatIso.ofComponents fun X ↦
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

/-- `BipointedToPointed_snd` is inverse to `PointedToBipointed`. -/
@[simps!]
def pointedToBipointedCompBipointedToPointedSnd :
    pointedToBipointed ⋙ bipointedToPointedSnd ≅ 𝟭 _ :=
  NatIso.ofComponents fun X ↦
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

/-- The free/forgetful adjunction between `PointedToBipointed_fst` and `BipointedToPointed_fst`.
-/
def pointedToBipointedFstBipointedToPointedFstAdjunction :
    pointedToBipointedFst ⊣ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun f ↦ ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f ↦ ⟨fun o ↦ o.elim Y.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f ↦ by
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.map_snd.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g ↦ by
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }

/-- The free/forgetful adjunction between `PointedToBipointed_snd` and `BipointedToPointed_snd`.
-/
def pointedToBipointedSndBipointedToPointedSndAdjunction :
    pointedToBipointedSnd ⊣ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun f ↦ ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f ↦ ⟨fun o ↦ o.elim Y.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f ↦ by
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.map_fst.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g ↦ by
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }
