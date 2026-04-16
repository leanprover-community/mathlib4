/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Order.Category.Preord

/-!
Weewoo a docstring

### Partial Maps
This file defines *partial map diagrams* and *partial maps* in categories. It defines the partial
order of partial maps from `X` to `Y` as well as the category of partial map diagrams from `X` to
`Y`.

## Short explanation

A partial map (in usual parlance, i.e. say set theory) from `X` to `Y` is a function from some
subset of X to Y. In category theory, when interpreting morphisms as functions between sets/types,
this corresponds to an object `U` and two morphisms `m : U ⟶ X` and `f : U ⟶ Y` with `m` mono
(making `U` a literal subobject of `X`, and `f` the function from the subobject to `Y`).
Similar to how `Subobject`s of `X` are monomorphisms into `X` "up to isomorphism", for partial maps
we only consider the previously mentioned diagrams up to isomorphisms (between the respective
objects `U`) which transform the respective maps `m` and `f` into eachother.

## Definitions

- `ObjectProperty.IsPartialMap X Y` is the predicate on objects in `BinaryFan X Y` satisfied by
  fans where the projection to `X` is mono.
- `PrePartialMap X Y` is the category of partial map diagrams with domain `X` and codomain `Y`.
  It is defined as the full subcategory of `BinaryFan X Y` induced by `IsPartialMap X Y`.
  This category is thin (Homsets are subsingleton).
  In the file we also introduce the notation `X ⇀' Y` (typed with \rightharpoonup) for this type.
- `PartialMap X Y` is the partial order of partial maps with domain `X` and codomain `Y`.
  It is defined as the thin skeleton of `PrePartialMap X Y` (i.e. the quotient by iso)
  In the file we also introduce the notation `X ⇀ Y` for this type.

- `WithPrePartialMaps C` is the bicategory with objects in `C` where morphisms are partial
  map diagrams


-/
@[expose] public section

universe v u
namespace CategoryTheory
open Limits
variable {C : Type u} [Category.{v} C]

/-- A (concrete) partial map diagram in a category `C` from `X` to `Y` is a binary fan into `X` and
  `Y` such that the map into `X` is mono. -/
def ObjectProperty.IsPartialMap (X Y : C) : ObjectProperty (Limits.BinaryFan X Y) :=
  (Mono ·.fst)

/-- The category of concrete partial map diagrams in the category `C` with domain `X` and
  codomain `X` -/
@[ext]
structure PrePartialMap (X Y : C) where
  mk' :: (out : (ObjectProperty.IsPartialMap X Y).FullSubcategory)

def PrePartialMap.domain {X Y : C} (f : PrePartialMap X Y) : C := f.out.obj.pt

def PrePartialMap.fst {X Y : C} (f : PrePartialMap X Y) : f.domain ⟶ X := f.out.obj.fst

def PrePartialMap.hom {X Y : C} (f : PrePartialMap X Y) : f.domain ⟶ Y := f.out.obj.snd

variable (C) in
structure WithPrePartialMaps where
  mk :: (out : C)

attribute [pp_nodot] WithPrePartialMaps.mk

@[app_unexpander WithPrePartialMaps.mk]
protected meta def WithPrePartialMaps.unexpander_mk : Lean.PrettyPrinter.Unexpander
  | s => pure s

instance : Quiver (WithPrePartialMaps C) where
  Hom X Y := PrePartialMap X.out Y.out

@[inherit_doc PrePartialMap]
scoped notation:40 x:41 " ⇀' " y:41 =>
  (WithPrePartialMaps.mk x) ⟶ (WithPrePartialMaps.mk y)

instance {X Y : C} (c : X ⇀' Y) :
  Mono (c.fst) := c.out.property


namespace PrePartialMap

/--
create a partial map diagram by providing a monomorphism `m : U ⟶ X` and a morphism `f : U ⟶ Y`
-/
def mk {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    X ⇀' Y where
  out.obj := BinaryFan.mk m f
  out.property := inferInstanceAs (Mono m)

lemma mk_obj {X Y : C} (x : X ⇀' Y) :
    .mk x.fst x.hom = x := by
  refine PrePartialMap.ext <| ObjectProperty.FullSubcategory.ext ?_
  simp only [mk, fst, hom]
  dsimp [BinaryFan.mk]
  congr
  ext j
  match j with
  | .mk .left => simp
  | .mk .right => simp

@[simp]
lemma mk_domain {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  (mk m f).domain = U := rfl

@[simp]
lemma mk_fst {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  (mk m f).fst = m := rfl

@[simp]
lemma mk_hom {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  (mk m f).hom = f := rfl

def mkOfHom {X Y : C} (f : X ⟶ Y) : X ⇀' Y := mk (𝟙 X) f

@[simp]
lemma mkOfHom_domain {X Y : C} (f : X ⟶ Y) : (mkOfHom f).domain = X := rfl

@[simp]
lemma mkOfHom_fst {X Y : C} (f : X ⟶ Y) : (mkOfHom f).fst = 𝟙 X := rfl

@[simp]
lemma mkOfHom_hom {X Y : C} (f : X ⟶ Y) : (mkOfHom f).hom = f := rfl

def mkOfMono {X Y : C} (m : Y ⟶ X) [Mono m] : X ⇀' Y := mk m (𝟙 Y)

@[simp]
lemma mkOfMono_domain {X Y : C} (m : Y ⟶ X) [Mono m] : (mkOfMono m).domain = Y := rfl

@[simp]
lemma mkOfMono_fst {X Y : C} (m : Y ⟶ X) [Mono m] : (mkOfMono m).fst = m := rfl

@[simp]
lemma mkOfMono_hom {X Y : C} (m : Y ⟶ X) [Mono m] : (mkOfMono m).hom = 𝟙 Y := rfl

structure Hom {X Y : C} (f g : X ⇀' Y) where

  mk :: (hom' : f.out ⟶ g.out)

instance {X Y : WithPrePartialMaps C} : Category (X ⟶ Y) where
  Hom := Hom
  id f := ⟨𝟙 f.out⟩
  comp f g := ⟨f.hom' ≫ g.hom'⟩

/-- The subcategory of partial map diagrams is thin, making it sensible to use `ThinSkeleton` -/
instance {X Y : WithPrePartialMaps C} : Quiver.IsThin (X ⟶ Y) := fun
  a b => { allEq f₁ f₂ :=
    congrArg PrePartialMap.Hom.mk <| ObjectProperty.hom_ext _ <| ConeMorphism.ext _ _ <|
      b.out.property.right_cancellation f₁.hom'.hom.hom f₂.hom'.hom.hom (by
        simp [dsimp% f₁.hom'.hom.w ⟨.left⟩, dsimp% f₂.hom'.hom.w ⟨.left⟩])}

def Hom.hom {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f ⟶ g) : f.domain ⟶ g.domain :=
  h.hom'.hom.hom

@[reassoc (attr := simp)]
lemma id_hom {X Y : WithPrePartialMaps C} (f : X ⟶ Y) : (𝟙 f : f ⟶ f).hom = 𝟙 (f.domain) := rfl

@[reassoc (attr := simp)]
lemma comp_hom {X Y : WithPrePartialMaps C} {f g h : X ⟶ Y} (x : f ⟶ g) (y : g ⟶ h) :
    (x ≫ y).hom = x.hom ≫ y.hom := rfl

/-- Create a morphism between partial map diagrams by providing a morphism `g : U₁ ⟶ U₂`
  which makes the obvious triangles commute -/
def homMk {X Y : WithPrePartialMaps C} {f₁ f₂ : X ⟶ Y} (g : f₁.domain ⟶ f₂.domain)
    (hgm : g ≫ f₂.fst = f₁.fst := by cat_disch)
    (hgf : g ≫ f₂.hom = f₁.hom := by cat_disch) :
    f₁ ⟶ f₂ := .mk <| ObjectProperty.homMk
  { hom := g
    w j := by
      match j with
      | .mk .left => exact hgm
      | .mk .right => exact hgf }

@[simp]
lemma homMk_hom {X Y : WithPrePartialMaps C} {f₁ f₂ : X ⟶ Y} (g : f₁.domain ⟶ f₂.domain)
    (hgm : g ≫ f₂.fst = f₁.fst) (hgf : g ≫ f₂.hom = f₁.hom) :
    (homMk g hgm hgf).hom = g := rfl

@[simp]
lemma hom_fst {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f ⟶ g) :
  h.hom ≫ g.fst = f.fst := h.hom'.hom.w (.mk .left)

instance {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f ⟶ g) : Mono h.hom :=
  mono_of_mono_fac (hom_fst h)

@[simp]
lemma hom_hom {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f ⟶ g) :
  h.hom ≫ g.hom = f.hom := h.hom'.hom.w (.mk .right)

/-- The category is thin, so all maps are equal. -/
@[ext]
lemma hom_ext {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h₁ h₂ : f ⟶ g) :
    h₁ = h₂ := by
  apply Subsingleton.elim

@[simp]
lemma eqToHom_hom {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f = g) :
    (eqToHom h).hom = eqToHom ((congr(($h).domain))) := by
  cases h; rfl

@[simp]
lemma homMk_eta {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f ⟶ g) :
    homMk (h.hom) (hom_fst _) (hom_hom _) = h := by
  ext

-- not too sure about the use of this
@[simp]
lemma homMk_id {X Y U₁ : C} {m₁ : U₁ ⟶ X} [Mono m₁] {f₁ : U₁ ⟶ Y} :
  homMk (𝟙 U₁) = 𝟙 (mk m₁ f₁) := rfl

@[simp]
lemma homMk_id_domain {X Y : C} (f : X ⇀' Y) :
  homMk (𝟙 f.domain) = 𝟙 f := rfl

@[reassoc (attr := simp)]
lemma homMk_comp {X Y : WithPrePartialMaps C} {f₁ f₂ f₃ : X ⟶ Y} (g₁ : f₁.domain ⟶ f₂.domain)
    (hgm₁ : g₁ ≫ f₂.fst = f₁.fst) (hgf₁ : g₁ ≫ f₂.hom = f₁.hom)
    (g₂ : f₂.domain ⟶ f₃.domain) (hgm₂ : g₂ ≫ f₃.fst = f₂.fst)
    (hgf₂ : g₂ ≫ f₃.hom = f₂.hom) :
    homMk g₁ hgm₁ hgf₁ ≫ homMk g₂ hgm₂ hgf₂ = homMk (g₁ ≫ g₂) := rfl

/-- The functor from the category of partial map diagrams to the category of subobject diagrams -/
def overMono {X Y : C} : X ⇀' Y ⥤ MonoOver X where
  obj f := ⟨(Over.mk f.fst),f.out.property⟩
  map g := ObjectProperty.homMk <| Over.homMk (g.hom) (hom_fst g)

/-- The functor from the category of partial map diagrams from `X` to `Y` to the
  over-category `C/Y`. -/
def over {X Y : C} : X ⇀' Y ⥤ Over Y where
  obj f := Over.mk f.hom
  map g := Over.homMk (g.hom) (hom_hom g)

variable [HasPullbacks C]
/-- Composition of partial map diagrams -/
noncomputable def comp {X Y Z : C} (f : X ⇀' Y) (g : Y ⇀' Z) : X ⇀' Z :=
  PrePartialMap.mk (pullback.fst f.hom g.fst ≫ f.fst) (pullback.snd _ _ ≫ g.hom)

noncomputable def mkCompMkIso {X Y Z : C} {U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y)
    {U₂ : C} (m₂ : U₂ ⟶ Y) [Mono m₂] (f₂ : U₂ ⟶ Z) {U₃ : C} {m₃ : U₃ ⟶ U₁} {f₃ : U₃ ⟶ U₂}
    (h : IsPullback m₃ f₃ f₁ m₂) :
    letI : Mono m₃ := h.mono_fst_of_mono
    comp (mk m₁ f₁) (mk m₂ f₂) ≅ mk (m₃ ≫ m₁) (f₃ ≫ f₂) where
  hom := homMk (h.isoPullback.inv) (by simp [comp]) (by simp [comp])
  inv := homMk (h.isoPullback.hom) (by simp [comp]) (by simp [comp])
  hom_inv_id := by ext
  inv_hom_id := by ext

noncomputable def mkOfHomCompIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mkOfHom (f ≫ g) ≅ comp (mkOfHom f) (mkOfHom g) :=
  eqToIso (by simpa using refl (mkOfHom (f ≫ g))) ≪≫
    (mkCompMkIso (𝟙 X) f (𝟙 Y) g (IsPullback.id_horiz f)).symm

noncomputable def mkOfMonoCompIso {X Y Z : C} (m₁ : Y ⟶ X) [Mono m₁] (m₂ : Z ⟶ Y) [Mono m₂] :
    mkOfMono (m₂ ≫ m₁) ≅ comp (mkOfMono m₁) (mkOfMono m₂) :=
  eqToIso (by simpa using refl (mkOfMono (m₂ ≫ m₁))) ≪≫
    (mkCompMkIso m₁ (𝟙 Y) m₂ (𝟙 Z) (IsPullback.id_vert m₂)).symm

noncomputable def mkOfMonoCompMkOfHomIso {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    comp (mkOfMono m) (mkOfHom f) ≅ mk m f :=
  mkCompMkIso m (𝟙 U) (𝟙 U) f (IsPullback.id_vert (𝟙 U)) ≪≫
    eqToIso (by simp)

/-- The associator iso in the bicategory of partial map diagrams -/
noncomputable def associator {W X Y Z : WithPrePartialMaps C}
    (f₁ : W ⟶ X) (f₂ : X ⟶ Y) (f₃ : Y ⟶ Z) :
    comp (comp f₁ f₂) f₃ ≅ comp f₁ (comp f₂ f₃) where
  hom := homMk
    (pullbackAssoc f₁.hom f₂.fst f₂.hom f₃.fst).hom (by simp [comp]) (by simp [comp])
  inv := homMk
    (pullbackAssoc f₁.hom f₂.fst f₂.hom f₃.fst).inv (by simp [comp]) (by simp [comp])
  hom_inv_id := by ext
  inv_hom_id := by ext

/-- left whiskering in the bicategory of partial map diagrams -/
noncomputable def whiskerLeft {X Y Z : WithPrePartialMaps C} (f : X ⟶ Y) {g₁ g₂ : Y ⟶ Z}
    (h : g₁ ⟶ g₂) : comp f g₁ ⟶ comp f g₂ :=
  homMk (pullback.map (f.hom) g₁.fst f.hom g₂.fst (𝟙 f.domain) h.hom (𝟙 Y.out) (by simp) (by simp))
    (by simp [comp, pullback.lift_fst_assoc]) (by simp [comp,pullback.lift_snd_assoc])

-- set_option backward.isDefEq.respectTransparency false in
/-- right whiskering in the bicategory of partial map diagrams -/
noncomputable def whiskerRight {X Y Z : WithPrePartialMaps C} {f₁ f₂ : X ⟶ Y}
    (h : f₁ ⟶ f₂) (g : Y ⟶ Z) : comp f₁ g ⟶ comp f₂ g :=
  homMk (pullback.map f₁.hom g.fst f₂.hom g.fst h.hom (𝟙 g.domain) (𝟙 Y.out) (by simp) (by simp))
    (by simp [comp, pullback.lift_fst_assoc]) (by simp [comp, pullback.lift_snd_assoc])

-- set_option backward.isDefEq.respectTransparency false in
/-- the left unitor in the bicategory of partial map diagrams. -/
noncomputable def leftUnitor {X Y : C} (f : X ⇀' Y) : comp (mkOfHom (𝟙 X)) f ≅ f where
  hom := homMk (pullback.snd _ _) (pullback.condition.symm) rfl
  inv := homMk (pullback.lift f.fst (𝟙 f.domain) (by simp))
    (by simp [comp, pullback.lift_fst]) (by simp [comp, pullback.lift_snd_assoc])
  hom_inv_id := by ext
  inv_hom_id := by ext

/-- the right unitor in the bicategory of partial map diagrams. -/
noncomputable def rightUnitor {X Y : C} (f : X ⇀' Y) : comp f (mkOfHom (𝟙 Y)) ≅ f where
  hom := homMk (pullback.fst _ _) (rfl) (pullback.condition)
  inv := homMk (pullback.lift (𝟙 f.domain) f.hom)
    (by simp [comp, pullback.lift_fst_assoc]) (by simp [comp, pullback.lift_snd])
  hom_inv_id := by ext
  inv_hom_id := by ext

@[simp]
lemma id_whiskerLeft {X Y : C} {f₁ f₂ : X ⇀' Y} (h : f₁ ⟶ f₂) :
    whiskerLeft (mkOfHom (𝟙 X)) h = (leftUnitor f₁).hom ≫ h ≫ (leftUnitor f₂).inv := by
  ext

@[simp]
lemma whiskerLeft_id {X Y Z : C} (f : X ⇀' Y) (g : Y ⇀' Z) :
    whiskerLeft f (𝟙 g) = 𝟙 (comp f g) := by
  ext

@[simp]
lemma whiskerLeft_comp {X Y Z : C} (f : X ⇀' Y) {g₁ g₂ g₃ : Y ⇀' Z}
    (h₁ : g₁ ⟶ g₂) (h₂ : g₂ ⟶ g₃) :
    whiskerLeft f (h₁ ≫ h₂) = whiskerLeft f h₁ ≫ whiskerLeft f h₂ := by
  ext

@[simp]
lemma comp_whiskerLeft {W X Y Z : C} (f₁ : W ⇀' X) (f₂ : X ⇀' Y) {g₁ g₂ : Y ⇀' Z}
    (h : g₁ ⟶ g₂) : whiskerLeft (comp f₁ f₂) h = (associator f₁ f₂ g₁).hom ≫
      whiskerLeft f₁ (whiskerLeft f₂ h) ≫ (associator f₁ f₂ g₂).inv := by
  ext

lemma whiskerRight_id {X Y : C} {f₁ f₂ : X ⇀' Y} (h : f₁ ⟶ f₂) :
    whiskerRight h (mkOfHom (𝟙 Y)) = (rightUnitor f₁).hom ≫ h ≫ (rightUnitor f₂).inv := by
  ext

@[simp]
lemma id_whiskerRight {X Y Z : C} (f : X ⇀' Y) (g : Y ⇀' Z) :
    whiskerRight (𝟙 f) g = 𝟙 (comp f g) := by
  ext

@[simp]
lemma comp_whiskerRight {X Y Z : C} {f₁ f₂ f₃ : X ⇀' Y} (h₁ : f₁ ⟶ f₂) (h₂ : f₂ ⟶ f₃)
    (g : Y ⇀' Z) : whiskerRight (h₁ ≫ h₂) g = whiskerRight h₁ g ≫ whiskerRight h₂ g := by
  ext

@[simp]
lemma whiskerRight_comp {W X Y Z : C} {f₁ f₂ : W ⇀' X} (h : f₁ ⟶ f₂) (g₁ : X ⇀' Y)
    (g₂ : Y ⇀' Z) : whiskerRight h (comp g₁ g₂) = (associator f₁ g₁ g₂).inv ≫
      whiskerRight (whiskerRight h g₁) g₂ ≫ (associator f₂ g₁ g₂).hom := by
  ext

lemma whisker_assoc {W X Y Z : C} (f₁ : W ⇀' X) {g₁ g₂ : X ⇀' Y} (h : g₁ ⟶ g₂)
    (f₂ : Y ⇀' Z) : whiskerRight (whiskerLeft f₁ h) f₂ = (associator f₁ g₁ f₂).hom ≫
    whiskerLeft f₁ (whiskerRight h f₂) ≫ (associator f₁ g₂ f₂).inv := by
  ext

lemma whisker_exchange {X Y Z : C} {f₁ f₂ : X ⇀' Y} (f : f₁ ⟶ f₂)
    {g₁ g₂ : Y ⇀' Z} (g : g₁ ⟶ g₂) : whiskerLeft f₁ g ≫ (whiskerRight f g₂) =
    whiskerRight f g₁ ≫ whiskerLeft f₂ g := by
  ext

lemma pentagon {A B D E F : C} (f : A ⇀' B) (g : B ⇀' D) (h : D ⇀' E) (i : E ⇀' F) :
    whiskerRight (associator f g h).hom i ≫ (associator f (comp g h) i).hom ≫
      whiskerLeft f (associator g h i).hom =
      (associator (comp f g) h i).hom ≫ (associator f g (comp h i)).hom := by
  ext

lemma triangle {X Y Z : C} (f : X ⇀' Y) (g : Y ⇀' Z) :
    (associator f (mkOfHom (𝟙 Y)) g).hom ≫ whiskerLeft f (leftUnitor g).hom =
      whiskerRight (rightUnitor f).hom g := by
  ext

noncomputable instance : Bicategory (WithPrePartialMaps C) where
  id X := mkOfHom (𝟙 X.out)
  comp {X Y Z} f g := comp f g
  whiskerLeft {X Y Z} f g₁ g₂ h := whiskerLeft f h
  whiskerRight {X Y Z} f₁ f₂ h g := whiskerRight h g
  associator {W X Y Z} f g h := associator f g h
  leftUnitor {X Y} f := leftUnitor f
  rightUnitor {X Y} f := rightUnitor f
  whiskerLeft_id := whiskerLeft_id
  whiskerLeft_comp := whiskerLeft_comp
  id_whiskerLeft := id_whiskerLeft
  comp_whiskerLeft := comp_whiskerLeft
  id_whiskerRight := id_whiskerRight
  comp_whiskerRight := comp_whiskerRight
  whiskerRight_id := whiskerRight_id
  whiskerRight_comp := whiskerRight_comp
  whisker_assoc := whisker_assoc
  whisker_exchange {X Y Z} f₁ f₂ g₁ g₂ f g := whisker_exchange f g
  pentagon := pentagon
  triangle := triangle

end PrePartialMap

/-- The skeleton category of partially defined maps, where given `f g : X ⇀ Y`,
  the map `f ⟶ g` exists iff the support of `g` contains the support of `f` and
  the maps agree on the support of `f` -/
def PartialMap (X Y : C) := ThinSkeleton (X ⇀' Y)
namespace PartialMap

variable (C) in
/-- The 2-category `C` with partial maps in `C` as morphisms. -/
structure _root_.CategoryTheory.WithPartialMaps : Type u where
  mk :: (out : C)

attribute [pp_nodot] WithPartialMaps.mk

@[app_unexpander WithPartialMaps.mk]
protected meta def WithPartialMaps.unexpander_mk : Lean.PrettyPrinter.Unexpander
  | s => pure s

instance : Quiver (WithPartialMaps C) where
  Hom X Y := PartialMap X.out Y.out

-- not sure if this is the right precedence yet. it should be more than 40, in order to parse
-- correctly w/r/t "=". see also the notation "⇀'"
notation:40 X:41 " ⇀ " Y:41 => WithPartialMaps.mk X ⟶ WithPartialMaps.mk Y

def mk {U X Y : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) : X ⇀ Y :=
  ThinSkeleton.mk (.mk m f)

instance {X Y : WithPartialMaps C} : PartialOrder (X ⟶ Y) :=
  inferInstanceAs% (PartialOrder (ThinSkeleton (X.out ⇀' Y.out)))

lemma le_iff {X Y U₁ : C} {m₁ : U₁ ⟶ X} [Mono m₁] {f₁ : U₁ ⟶ Y}
    {U₂ : C} {m₂ : U₂ ⟶ X} [Mono m₂] {f₂ : U₂ ⟶ Y} : mk m₁ f₁ ≤ mk m₂ f₂ ↔
    ∃ f : U₁ ⟶ U₂, f ≫ m₂ = m₁ ∧ f ≫ f₂ = f₁ := by
  dsimp [(· ≤ ·)]
  dsimp [mk, ThinSkeleton.mk, Quotient.mk']
  constructor
  · rintro ⟨z⟩
    use z.hom, PrePartialMap.hom_fst z
    exact PrePartialMap.hom_hom z
  · rintro ⟨f,hf₁,hf₂⟩
    exact ⟨PrePartialMap.homMk f hf₁ hf₂⟩

@[simp]
lemma mk_obj {X Y : C} (x : PrePartialMap X Y) :
  PartialMap.mk x.fst x.hom = ⟦x⟧ := by
  dsimp [mk]
  congr
  exact PrePartialMap.mk_obj x

lemma mk_eq {U₁ U₂ X Y : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y)
    (m₂ : U₂ ⟶ X) [Mono m₂] (f₂ : U₂ ⟶ Y) : mk m₁ f₁ = mk m₂ f₂ ↔
    ∃ e : U₁ ≅ U₂, e.hom ≫ m₂ = m₁ ∧ e.hom ≫ f₂ = f₁ := by
  constructor
  · intro h
    have := Quotient.eq.mp h
    rw [isIsomorphicSetoid] at this
    simp only [IsIsomorphic] at this
    obtain ⟨e'⟩ := this
    use ⟨e'.hom.hom,e'.inv.hom, congr($(e'.hom_inv_id).hom),
      congr($(e'.inv_hom_id).hom)⟩
    simp only
    constructor
    · simpa using PrePartialMap.hom_fst e'.hom
    · simpa using PrePartialMap.hom_hom e'.hom
  · rintro ⟨e,he₁, he₂⟩
    apply Quotient.sound
    constructor
    exact Iso.mk (PrePartialMap.homMk e.hom) (PrePartialMap.homMk e.inv)

def rec {X Y : C} {motive : X ⇀ Y → Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y), motive (.mk m f))
    (ofMk_sound : ∀ {U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y),
      ∀ {U₂ : C} (m₂ : U₂ ⟶ X) [Mono m₂] (f₂ : U₂ ⟶ Y),
      (h : mk m₁ f₁ = mk m₂ f₂) → cast congr(motive $h) (ofMk m₁ f₁) = ofMk m₂ f₂) :
    ∀ (f : X ⇀ Y), motive f :=
  Quotient.rec (fun a => ((PartialMap.mk_obj (C := C) a).symm) ▸ ofMk (a.fst) (a.hom)) (by
    intro a b _
    generalize_proofs _ _ h₁ hab _ _ h₂
    rw [← ofMk_sound a.fst a.hom b.fst b.hom ((h₁.trans hab).trans (h₂.symm))]
    congr 1
    · rw [h₂, hab]
    · simp only [heq_cast_iff_heq, eqRec_heq_iff_heq, heq_eq_eq]
    · exact proof_irrel_heq hab h₂)

    -- convert rfl <;> simp_all)

def rec' {X Y : C} {motive : X ⇀ Y → Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y), motive (.mk m f))
    [∀ (f : X ⇀ Y), Subsingleton (motive f)] :
    ∀ (f : X ⇀ Y), motive f := PartialMap.rec ofMk (by intros; apply Subsingleton.elim)

lemma rec'_mk {X Y : C} {motive : X ⇀ Y → Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y), motive (.mk m f))
    [∀ (f : X ⇀ Y), Subsingleton (motive f)]
    {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  PartialMap.rec' ofMk (mk m f) = ofMk m f := rfl

def lift {X Y : C} {motive : Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (_f : U ⟶ Y), motive)
    (ofMk_sound : ∀ {U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y),
      ∀ {U₂ : C} (m₂ : U₂ ⟶ X) [Mono m₂] (f₂ : U₂ ⟶ Y),
      (h : mk m₁ f₁ = mk m₂ f₂) → ofMk m₁ f₁ = ofMk m₂ f₂) :
    X ⇀ Y → motive :=
  PartialMap.rec ofMk (fun {U₁} m₁ _ f₁ {U₂} m₂ _ f₂ h =>
    (by simp [ofMk_sound m₁ f₁ m₂ f₂ h]))

@[simp]
lemma rec_mk {X Y : C} {motive : X ⇀ Y → Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y), motive (.mk m f))
    (ofMk_sound : ∀ {U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y),
      ∀ {U₂ : C} (m₂ : U₂ ⟶ X) [Mono m₂] (f₂ : U₂ ⟶ Y),
      (h : mk m₁ f₁ = mk m₂ f₂) → cast congr(motive $h) (ofMk m₁ f₁) = ofMk m₂ f₂)
    {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    PartialMap.rec ofMk ofMk_sound (mk m f) = ofMk m f := rfl

@[simp]
lemma lift_mk {X Y : C} {motive : Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (_f : U ⟶ Y), motive)
    (ofMk_sound : ∀ {U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y),
      ∀ {U₂ : C} (m₂ : U₂ ⟶ X) [Mono m₂] (f₂ : U₂ ⟶ Y),
      (h : mk m₁ f₁ = mk m₂ f₂) → ofMk m₁ f₁ = ofMk m₂ f₂)
    {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    PartialMap.lift ofMk ofMk_sound (mk m f) = ofMk m f :=
  rfl

@[cases_eliminator, induction_eliminator]
lemma induction {X Y : C} {motive : (X ⇀ Y) → Prop}
    (h_mk : ∀ {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y), motive (.mk m f)) :
    ∀ f, motive f :=
  PartialMap.rec h_mk (by simp)

lemma induction₂ {X Y : C} {motive : (X ⇀ Y) → (X ⇀ Y) → Prop}
    (h_mk : ∀ {U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y),
      ∀ {U₂ : C} (m₂ : U₂ ⟶ X) [Mono m₂] (f₂ : U₂ ⟶ Y),
      motive (.mk m₁ f₁) (.mk m₂ f₂)) :
    ∀ f₁ f₂, motive f₁ f₂ := by
  intro f₁ f₂
  induction f₁ with
  | h_mk m₁ f₁ =>
    induction f₂ with
    | h_mk m₂ f₂ =>
      exact h_mk m₁ f₁ m₂ f₂

/-- The domain of a partial map -/
protected def support {X Y : C} : X ⇀ Y ⥤ Subobject X :=
  ThinSkeleton.map PrePartialMap.overMono

lemma support.obj_mk {X Y : C} {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  PartialMap.support.obj (mk m f) = Subobject.mk m := rfl

variable [HasPullbacks C]

noncomputable def comp {X Y Z : C} : X ⇀ Y ⥤ Y ⇀ Z ⥤ X ⇀ Z :=
  ThinSkeleton.map₂ (Bicategory.precomposing
    (WithPrePartialMaps.mk X) (WithPrePartialMaps.mk Y) (WithPrePartialMaps.mk Z))

def ofHom {X Y : C} (f : X ⟶ Y) : X ⇀ Y := mk (𝟙 _) f

omit [HasPullbacks C] in
lemma ofHom_eq_mk {X Y : C} (f : X ⟶ Y) : ofHom f = mk (𝟙 _) f := rfl


def ofMono {X Y : C} (m : Y ⟶ X) [Mono m] : X ⇀ Y := mk m (𝟙 _)

omit [HasPullbacks C] in
lemma ofMono_eq_mk {X Y : C} (m : Y ⟶ X) [Mono m] : ofMono m = mk m (𝟙 _) := rfl


def id (X : C) : X ⇀ X := ofHom (𝟙 X)

omit [HasPullbacks C] in
lemma id_eq (X : C) : id X = mk (𝟙 X) (𝟙 X) :=
  rfl

end PartialMap

namespace WithPartialMaps
/-- all this to say, `WithPartialMaps C` is a 2-category -/
noncomputable instance [HasPullbacks C] : Bicategory (WithPartialMaps C) where
  id {X} := PartialMap.id X.out
  comp {X Y Z} f g := (PartialMap.comp.obj f).obj g
  whiskerLeft {X Y Z} f {g₁ g₂} h := (PartialMap.comp.obj f).map h
  whiskerRight {X Y Z} {f₁ f₂} h g := (PartialMap.comp.map h).app g
  associator {W X Y Z} := PartialMap.rec'
    (fun m₁ _ f₁ => PartialMap.rec'
      (fun m₂ _ f₂ => PartialMap.rec'
        (fun m₃ _ f₃ =>
          eqToIso (Quotient.sound ⟨
            (PrePartialMap.associator
            (PrePartialMap.mk m₁ f₁)
            (PrePartialMap.mk m₂ f₂)
            (PrePartialMap.mk m₃ f₃))⟩))))
  leftUnitor {X Y} := PartialMap.rec'
    (fun m₁ _ f₁ => eqToIso (Quotient.sound ⟨PrePartialMap.leftUnitor (PrePartialMap.mk m₁ f₁)⟩))
  rightUnitor {X Y} := PartialMap.rec'
    (fun m₁ _ f₁ => eqToIso (Quotient.sound ⟨PrePartialMap.rightUnitor (PrePartialMap.mk m₁ f₁)⟩))

instance [HasPullbacks C] : Bicategory.Strict (WithPartialMaps C) where
  id_comp := PartialMap.induction (fun m _ f =>
      Quotient.sound ⟨PrePartialMap.leftUnitor (.mk m f)⟩)
  comp_id := PartialMap.induction (fun m _ f =>
    Quotient.sound ⟨PrePartialMap.rightUnitor (.mk m f)⟩)
  assoc := PartialMap.induction (fun m₁ _ f₁ =>
    PartialMap.induction (fun m₂ _ f₂ =>
      PartialMap.induction (fun m₃ _ f₃ =>
        Quotient.sound ⟨PrePartialMap.associator (.mk m₁ f₁) (.mk m₂ f₂) (.mk m₃ f₃)⟩)))
  leftUnitor_eqToIso := PartialMap.induction (fun _ _ _ => rfl)
  rightUnitor_eqToIso := PartialMap.induction (fun _ _ _ => rfl)
  associator_eqToIso := PartialMap.induction (fun _ _ _ => PartialMap.induction
    (fun _ _ _ => PartialMap.induction (fun _ _ _ => rfl)))

end WithPartialMaps
namespace PartialMap
variable [HasPullbacks C]

lemma mk_comp_mk_of_isPullback {X Y Z U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y)
    {U₂ : C} (m₂ : U₂ ⟶ Y) [Mono m₂] (f₂ : U₂ ⟶ Z) {U₃ : C} {m₃ : U₃ ⟶ U₁} {f₃ : U₃ ⟶ U₂}
    (h : IsPullback m₃ f₃ f₁ m₂) :
    letI : Mono m₃ := h.mono_fst_of_mono
    mk m₁ f₁ ≫ mk m₂ f₂ = mk (m₃ ≫ m₁) (f₃ ≫ f₂) :=
  Quotient.sound ⟨PrePartialMap.mkCompMkIso m₁ f₁ m₂ f₂ h⟩

@[reassoc (attr := simp)]
lemma ofHom_comp_ofHom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (ofHom f) ≫ (ofHom g) = ofHom (f ≫ g) :=
  Quotient.sound ⟨(PrePartialMap.mkOfHomCompIso f g).symm⟩

@[reassoc (attr := simp)]
lemma ofMono_comp_ofMono {X Y Z : C} (m₁ : Y ⟶ X) [Mono m₁] (m₂ : Z ⟶ Y) [Mono m₂] :
    (ofMono m₁) ≫ (ofMono m₂) = ofMono (m₂ ≫ m₁) :=
  Quotient.sound ⟨(PrePartialMap.mkOfMonoCompIso m₁ m₂).symm⟩

@[reassoc (attr := simp)]
lemma ofMono_comp_ofHom {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    (ofMono m) ≫ (ofHom f) = mk m f :=
  Quotient.sound ⟨PrePartialMap.mkOfMonoCompMkOfHomIso m f⟩

@[reassoc (attr := simp)]
lemma mk_comp_ofHom {X Y Z : C} {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) (g : Y ⟶ Z) :
    (mk m f) ≫ (ofHom g) = (mk m (f ≫ g)) := by
  rw [← ofMono_comp_ofHom,Category.assoc,ofHom_comp_ofHom, ofMono_comp_ofHom]

@[reassoc (attr := simp)]
lemma ofMono_comp_mk {X Y Z U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) (m' : X ⟶ Z) [Mono m'] :
    (ofMono m') ≫ (mk m f) = mk (m ≫ m') f := by
  rw [← ofMono_comp_ofHom,← Category.assoc, ofMono_comp_ofMono, ofMono_comp_ofHom]

end PartialMap
namespace WithPartialMaps

variable (C) in
noncomputable abbrev withPartialMapsPreCore [HasPullbacks C] : StrictPseudofunctorPreCore
    (LocallyDiscrete C) (WithPartialMaps C) where
  obj X := .mk X.as
  map f := PartialMap.ofHom f.as
  map₂ g := eqToHom (by rw [LocallyDiscrete.eq_of_hom g])
  map_comp {X Y Z} f₁ f₂ := Quotient.sound ⟨PrePartialMap.mkOfHomCompIso f₁.as f₂.as⟩


variable (C) in
-- @[simp]
noncomputable def _root_.CategoryTheory.withPartialMaps [HasPullbacks C] :
    StrictPseudofunctor (LocallyDiscrete C) (WithPartialMaps C) :=
  .mk'' (withPartialMapsPreCore C)

variable (C) in
@[simps]
def toLocallyDiscrete : C ⥤ LocallyDiscrete C where
  obj X := .mk X
  map f := f.toLoc

variable (C) in
@[simps]
def ofLocallyDiscrete : LocallyDiscrete C ⥤ C where
  obj X := X.as
  map f := f.as

@[simps]
def locallyDiscreteEquivalence : LocallyDiscrete C ≌ C where
  functor := ofLocallyDiscrete C
  inverse := toLocallyDiscrete C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
lemma _root_.CategoryTheory.withPartialMaps_obj [HasPullbacks C] (X : LocallyDiscrete C) :
    (withPartialMaps C).obj X = .mk X.as := rfl

@[simp]
lemma _root_.CategoryTheory.withPartialMaps_map [HasPullbacks C] {X Y : LocallyDiscrete C}
    (f : X ⟶ Y) : (withPartialMaps C).map f = PartialMap.ofHom f.as := rfl

lemma ofHom_injective [HasPullbacks C] {X Y : C} :
    Function.Injective (PartialMap.ofHom (X := X) (Y := Y)) := by
  intro f g h
  simp_rw [PartialMap.ofHom_eq_mk] at h
  rw [PartialMap.mk_eq] at h
  obtain ⟨e,hid,hf⟩ := h
  simp only [Category.comp_id] at hid
  rw [hid] at hf
  simpa using hf.symm

instance [HasPullbacks C] : (toLocallyDiscrete C ⋙ (withPartialMaps C).toFunctor).Faithful where
  map_injective {_ _} := ofHom_injective

lemma mono_of_mono_ofHom [HasPullbacks C] {X Y : C} {f : X ⟶ Y} :
    Mono (PartialMap.ofHom f) → Mono f := by
  intro h
  change Mono ((toLocallyDiscrete C ⋙ ((withPartialMaps C).toFunctor)).map f) at h
  exact Functor.ReflectsMonomorphisms.reflects _ h

lemma eq_ofHom_of_mono [HasPullbacks C] {X Y : C} (f : X ⇀ Y) [Mono f] :
    ∃ f', f = PartialMap.ofHom f' ∧ Mono f' := by
  have := ‹Mono f›
  induction f with
  | h_mk m f =>
    rename_i U
    have : PartialMap.ofHom (𝟙 X) ≫ PartialMap.mk m f = PartialMap.mk m m ≫ PartialMap.mk m f := by
      rw [PartialMap.ofHom_eq_mk,
        PartialMap.mk_comp_mk_of_isPullback _ _ _ _ (IsPullback.id_vert _),
        PartialMap.mk_comp_mk_of_isPullback _ _ _ _ (.of_horiz_isIso_mono (fst := 𝟙 _) (snd := 𝟙 _)
          (by simp))]
      simp
    rw [cancel_mono, PartialMap.ofHom_eq_mk, PartialMap.mk_eq] at this
    obtain ⟨e,he₁,_⟩ := this
    use e.hom ≫ f
    have : PartialMap.mk m f = PartialMap.ofHom (e.hom ≫ f) := by
      rw [PartialMap.ofHom_eq_mk, PartialMap.mk_eq]
      use e.symm
      rw [← he₁]
      simp
    use this
    have : Mono (PartialMap.ofHom (e.hom ≫ f)) := by
      rwa [← this]
    exact mono_of_mono_ofHom this


instance mono_ofHom [HasPullbacks C] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (C := WithPartialMaps C) (PartialMap.ofHom f) where
  right_cancellation {Z} g₁ g₂ h := by
    induction g₁, g₂ using PartialMap.induction₂ with
    | h_mk m₁ f₁ m₂ f₂ =>
      simp_rw [PartialMap.mk_comp_ofHom] at h
      rw [PartialMap.mk_eq] at h ⊢
      apply h.imp
      intro e he
      use he.left
      rw [← Category.assoc] at he
      exact Mono.right_cancellation _ _ he.right

/-- Partial maps are monomorphisms in a category C with partial maps iff they are
  total monomorphisms -/
theorem mono_iff_exists_eq_ofHom_and_mono [HasPullbacks C] {X Y : C} (f : X ⇀ Y) :
  Mono f ↔ ∃ f', (f = PartialMap.ofHom f' ∧ Mono f') := by
  refine ⟨fun _ => eq_ofHom_of_mono f, by
    rintro ⟨f,rfl,h⟩
    infer_instance⟩

-- variable (C) in
-- @[simps]
-- def _root_.CategoryTheory.withPartialMaps [HasPullbacks C] : C ⥤ (WithPartialMaps C) where
--   obj X := .mk X
--   map f := PartialMap.ofHom f
--   map_id _ := rfl
--   map_comp f₁ f₂ := Quotient.sound ⟨PrePartialMap.mkOfHomCompIso f₁ f₂⟩

open Bicategory
variable (C) in
noncomputable def coyoneda [HasPullbacks C] :
    (WithPartialMaps C)ᵒᵖ ⥤ (WithPartialMaps C) ⥤ Cat where
  obj X := {
    obj Y := Cat.of <| (X.unop) ⟶ Y
    map {Y Z} g := (Bicategory.postcomp (X.unop) g).toCatHom
    map_id Y := by
      apply Cat.Hom.ext <| Functor.ext (by intro f; exact Category.comp_id f)
    map_comp {Y Z W} g₁ g₂ := by
      apply Cat.Hom.ext <| Functor.ext (by intro f; simp)
  }
  map {X₁ X₂} f := {
    app Y := Functor.toCatHom {
      obj g := f.unop ≫ g
      map {g₁ g₂} h := f.unop ◁ h
      map_id g := whiskerLeft_id f.unop g
      map_comp {g₁ g₂ g₂} h₁ h₂ := whiskerLeft_comp f.unop h₁ h₂
    }
    naturality {Y Z} g := Cat.Hom.ext <| Functor.ext (by simp)
  }
  map_id X := by
    ext Y
    exact Functor.ext (by simp)
  map_comp {X Y Z} f g := by
    ext W
    exact Functor.ext (by simp)

/-- the presheaf of partial map functors. -/
noncomputable def _root_.CategoryTheory.partialMaps
  [HasPullbacks C] : Cᵒᵖ ⥤ C ⥤ Type _ :=
  (((Functor.whiskeringLeft₂ (Type _)).obj (toLocallyDiscrete C ⋙
    (withPartialMaps C).toFunctor).op).obj
    (toLocallyDiscrete C ⋙ (withPartialMaps C).toFunctor)).obj
    ((Functor.postcompose₂.obj (Cat.objects)).obj (WithPartialMaps.coyoneda C))

@[simp]
lemma _root_.CategoryTheory.partialMaps_obj_obj [HasPullbacks C] (X : Cᵒᵖ) (Y : C) :
    (partialMaps.obj X).obj Y = ((WithPartialMaps.mk X.unop) ⟶ (WithPartialMaps.mk Y)) := rfl

@[simp]
lemma _root_.CategoryTheory.partialMaps_obj_map [HasPullbacks C] (X : Cᵒᵖ) {Y Z : C} (g : Y ⟶ Z) :
    (partialMaps.obj X).map g = (· ≫ (PartialMap.ofHom g)) := rfl

@[simp]
lemma _root_.CategoryTheory.partialMaps_map_app [HasPullbacks C] {X Y : Cᵒᵖ} {f : Y ⟶ X} (Z : C) :
    (partialMaps.map f).app Z = (PartialMap.ofHom f.unop ≫ ·) := rfl

/-- the presheaf of partial maps into X -/
noncomputable def _root_.CategoryTheory.partialMapsTo [HasPullbacks C] (X : C) :
  Cᵒᵖ ⥤ Type _ := partialMaps.flip.obj X

@[simp]
lemma _root_.CategoryTheory.partialMapsTo_obj [HasPullbacks C] (X : C) (Y : Cᵒᵖ) :
  (partialMapsTo X).obj Y = ((WithPartialMaps.mk Y.unop) ⟶ (WithPartialMaps.mk X)) := rfl

@[simp]
lemma _root_.CategoryTheory.partialMapsTo_map [HasPullbacks C] (X : C) {Y Z : Cᵒᵖ} (g : Y ⟶ Z) :
  (partialMapsTo X).map g = (PartialMap.ofHom g.unop ≫ ·) := rfl

noncomputable def _root_.CategoryTheory.partialMapsFrom [HasPullbacks C] (X : C) :
  C ⥤ Type _ := partialMaps.obj (.op X)

@[simp]
lemma _root_.CategoryTheory.partialMapsFrom_obj [HasPullbacks C] (X Y : C) :
  (partialMapsFrom X).obj Y = ((WithPartialMaps.mk X) ⟶ (WithPartialMaps.mk Y)) := rfl

@[simp]
lemma _root_.CategoryTheory.partialMapsFrom_map [HasPullbacks C] (X : C) {Y Z : C} (g : Y ⟶ Z) :
  (partialMapsFrom X).map g = (· ≫ PartialMap.ofHom g) := rfl


end CategoryTheory.WithPartialMaps
