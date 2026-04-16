/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# Partial Map Diagrams
As preparation for defining `PartialMap X Y`, we set up the theory for
`PrePartialMap X Y ≃ {s : BinaryFan X Y // Mono s.fst}`.

Here `PrePartialMap X Y` is a thin category (a pair of objects has at most one morphism between
them), so we can think of it as a preorder. However as it is not skeletal, it is not a partial
order.

`PartialMap X Y` will be defined as the skeleton of `PrePartialMap X`.

-/
@[expose] public section
universe v u
namespace CategoryTheory
open Limits
variable {C : Type u} [Category.{v} C]

/-- A partial map diagram in a category `C` from `X` to `Y` is a binary fan into `X` and
  `Y` such that the map into `X` is mono. -/
def ObjectProperty.IsPrePartialMap (X Y : C) : ObjectProperty (Limits.BinaryFan X Y) :=
  (Mono ·.fst)

/--
The category of partial map diagrams in the category `C` with domain `X : C` and codomain `Y : C`.
This should usually be written as `X ⟶ Y` with `WithPrePartialMaps C`, or using
the notation `X ⇀' Y` for objects `X Y : C`.
-/
@[ext]
structure PrePartialMap (X Y : C) where mk' ::
  /-- Interpret a partial map diagram as an actual diagram. -/
  out : (ObjectProperty.IsPrePartialMap X Y).FullSubcategory

variable (C) in
/-- The bicategory `WithPrePartialMaps C` has all objects in `C` as objects,
1-morphisms between `X` and `Y` are partial map diagrams from `X` to `Y`, and 2-morphisms are
given by expanding the support (and therefore unique). -/
structure WithPrePartialMaps where mk ::
  /-- Interpret an object in `WithPrePartialMaps C` as an object in `C`. -/
  out : C

attribute [pp_nodot] WithPrePartialMaps.mk

/-- We want to see `WithPrePartialMaps.mk X` instead of `{out := X}` -/
@[app_unexpander WithPrePartialMaps.mk]
protected meta def WithPrePartialMaps.unexpander_mk : Lean.PrettyPrinter.Unexpander
  | s => pure s

instance : Quiver (WithPrePartialMaps C) where
  Hom X Y := PrePartialMap X.out Y.out

@[inherit_doc PrePartialMap]
scoped[CategoryTheory.PrePartialMap] notation:40 x:41 " ⇀' " y:41 =>
  (WithPrePartialMaps.mk x) ⟶ (WithPrePartialMaps.mk y)

/-- The support object of a partial map diagram. -/
def PrePartialMap.support {X Y : WithPrePartialMaps C} (f : X ⟶ Y) : C := f.out.obj.pt

/-- The inclusion of the support into the domain of a partial map diagram. -/
def PrePartialMap.fst {X Y : WithPrePartialMaps C} (f : X ⟶ Y) : f.support ⟶ X.out := f.out.obj.fst

/-- The underlying (total) map of a partial map diagram. -/
def PrePartialMap.hom {X Y : WithPrePartialMaps C} (f : X ⟶ Y) : f.support ⟶ Y.out := f.out.obj.snd

instance {X Y : WithPrePartialMaps C} (f : X ⟶ Y) : Mono (f.fst) := f.out.property

namespace PrePartialMap

/--
A partial map diagram consists of a monomorphism `m : U ⟶ X` and a morphism `f : U ⟶ Y`.
-/
def mk {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    X ⇀' Y where
  out.obj := BinaryFan.mk m f
  out.property := inferInstanceAs (Mono m)

lemma mk_eta {X Y : WithPrePartialMaps C} (x : X ⟶ Y) :
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
lemma mk_support {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  (mk m f).support = U := rfl

@[simp]
lemma mk_fst {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  (mk m f).fst = m := rfl

@[simp]
lemma mk_hom {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  (mk m f).hom = f := rfl

/-- A morphism in `C` naturally lifts to a partial map diagram -/
def mkOfHom {X Y : C} (f : X ⟶ Y) : X ⇀' Y := mk (𝟙 X) f

lemma mkOfHom_def {X Y : C} (f : X ⟶ Y) : mkOfHom f = mk (𝟙 X) f := rfl

@[simp]
lemma mkOfHom_support {X Y : C} (f : X ⟶ Y) : (mkOfHom f).support = X := rfl

@[simp]
lemma mkOfHom_fst {X Y : C} (f : X ⟶ Y) : (mkOfHom f).fst = 𝟙 X := rfl

@[simp]
lemma mkOfHom_hom {X Y : C} (f : X ⟶ Y) : (mkOfHom f).hom = f := rfl

/-- Any monomorphism `Y ⟶ X` induces a partial map diagram `X ⇀' Y` with support `Y` acting like
the identity. -/
def mkOfMono {X Y : C} (m : Y ⟶ X) [Mono m] : X ⇀' Y := mk m (𝟙 Y)

lemma mkOfMono_def {X Y : C} (m : Y ⟶ X) [Mono m] : mkOfMono m = mk m (𝟙 Y) := rfl

@[simp]
lemma mkOfMono_support {X Y : C} (m : Y ⟶ X) [Mono m] : (mkOfMono m).support = Y := rfl

@[simp]
lemma mkOfMono_fst {X Y : C} (m : Y ⟶ X) [Mono m] : (mkOfMono m).fst = m := rfl

@[simp]
lemma mkOfMono_hom {X Y : C} (m : Y ⟶ X) [Mono m] : (mkOfMono m).hom = 𝟙 Y := rfl

/--
Given `f g : X ⇀' Y`, a morphism `f ⟶ g` is a witness that `g` is a functional extension of `f`.
-/
structure Hom {X Y : WithPrePartialMaps C} (f g : X ⟶ Y) where mk ::
  /-- The morphism of cones underlying a morphism of partial map diagrams. -/
  hom' : f.out ⟶ g.out

instance {X Y : WithPrePartialMaps C} : Category (X ⟶ Y) where
  Hom := Hom
  id f := ⟨𝟙 f.out⟩
  comp f g := ⟨f.hom' ≫ g.hom'⟩

instance {X Y : WithPrePartialMaps C} : Quiver.IsThin (X ⟶ Y) := fun
  a b => { allEq f₁ f₂ :=
    congrArg PrePartialMap.Hom.mk <| ObjectProperty.hom_ext _ <| ConeMorphism.ext _ _ <|
      b.out.property.right_cancellation f₁.hom'.hom.hom f₂.hom'.hom.hom (by
        simp [dsimp% f₁.hom'.hom.w ⟨.left⟩, dsimp% f₂.hom'.hom.w ⟨.left⟩])}

/-- The morphism in `C` underlying a morphism between partial maps `f ⟶ g`. -/
def Hom.hom {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f ⟶ g) : f.support ⟶ g.support :=
  h.hom'.hom.hom

@[simp, reassoc]
lemma id_hom {X Y : WithPrePartialMaps C} (f : X ⟶ Y) : (𝟙 f : f ⟶ f).hom = 𝟙 (f.support) := rfl

@[simp, reassoc]
lemma comp_hom {X Y : WithPrePartialMaps C} {f g h : X ⟶ Y} (x : f ⟶ g) (y : g ⟶ h) :
    (x ≫ y).hom = x.hom ≫ y.hom := rfl

/-- A morphism between partial map diagrams is a morphism `g : U₁ ⟶ U₂` between supports which makes
the obvious triangles commute. -/
def homMk {X Y : WithPrePartialMaps C} {f₁ f₂ : X ⟶ Y} (g : f₁.support ⟶ f₂.support)
    (hgm : g ≫ f₂.fst = f₁.fst := by cat_disch)
    (hgf : g ≫ f₂.hom = f₁.hom := by cat_disch) :
    f₁ ⟶ f₂ := .mk <| ObjectProperty.homMk
  { hom := g
    w j := by
      match j with
      | .mk .left => exact hgm
      | .mk .right => exact hgf }

@[simp]
lemma homMk_hom {X Y : WithPrePartialMaps C} {f₁ f₂ : X ⟶ Y} (g : f₁.support ⟶ f₂.support)
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

/-- The category of partial map diagrams between two objects is thin, so all maps between diagrams
are equal. -/
@[ext]
lemma hom_ext {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h₁ h₂ : f ⟶ g) :
    h₁ = h₂ := by
  apply Subsingleton.elim

@[simp]
lemma eqToHom_hom {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f = g) :
    (eqToHom h).hom = eqToHom ((congr(($h).support))) := by
  cases h; rfl

@[simp]
lemma homMk_eta {X Y : WithPrePartialMaps C} {f g : X ⟶ Y} (h : f ⟶ g) :
    homMk (h.hom) (hom_fst _) (hom_hom _) = h := by
  ext

@[simp]
lemma homMk_id {X Y U₁ : C} {m₁ : U₁ ⟶ X} [Mono m₁] {f₁ : U₁ ⟶ Y} :
  homMk (𝟙 U₁) = 𝟙 (mk m₁ f₁) := rfl

@[simp]
lemma homMk_id_support {X Y : C} (f : X ⇀' Y) :
  homMk (𝟙 f.support) = 𝟙 f := rfl

@[reassoc (attr := simp)]
lemma homMk_comp {X Y : WithPrePartialMaps C} {f₁ f₂ f₃ : X ⟶ Y} (g₁ : f₁.support ⟶ f₂.support)
    (hgm₁ : g₁ ≫ f₂.fst = f₁.fst) (hgf₁ : g₁ ≫ f₂.hom = f₁.hom)
    (g₂ : f₂.support ⟶ f₃.support) (hgm₂ : g₂ ≫ f₃.fst = f₂.fst)
    (hgf₂ : g₂ ≫ f₃.hom = f₂.hom) :
    homMk g₁ hgm₁ hgf₁ ≫ homMk g₂ hgm₂ hgf₂ = homMk (g₁ ≫ g₂) := rfl

/-- The functor from the category of partial map diagrams to the category of subobject diagrams. -/
def overMono {X Y : C} : X ⇀' Y ⥤ MonoOver X where
  obj f := ⟨(Over.mk f.fst),f.out.property⟩
  map g := ObjectProperty.homMk <| Over.homMk (g.hom) (hom_fst g)

/-- The functor from the category of partial map diagrams from `X` to `Y` to the
  over-category `C/Y`. -/
def over {X Y : C} : X ⇀' Y ⥤ Over Y where
  obj f := Over.mk f.hom
  map g := Over.homMk (g.hom) (hom_hom g)

variable [HasPullbacks C]
/-- Composition of partial map diagrams. -/
noncomputable def comp {X Y Z : C} (f : X ⇀' Y) (g : Y ⇀' Z) : X ⇀' Z :=
  PrePartialMap.mk (pullback.fst f.hom g.fst ≫ f.fst) (pullback.snd _ _ ≫ g.hom)

/-- In the category of partial map diagrams, `mk m₁ f₁ ≫ mk m₂ f₂` is isomorphic to
  `mk (m₃ ≫ m₁) (f₃ ≫ f₂)` if we have `IsPullback m₃ f₃ f₁ m₂`. -/
noncomputable def mkCompMkIso {X Y Z : C} {U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y)
    {U₂ : C} (m₂ : U₂ ⟶ Y) [Mono m₂] (f₂ : U₂ ⟶ Z) {U₃ : C} {m₃ : U₃ ⟶ U₁} {f₃ : U₃ ⟶ U₂}
    (h : IsPullback m₃ f₃ f₁ m₂) :
    letI : Mono m₃ := h.mono_fst_of_mono
    comp (mk m₁ f₁) (mk m₂ f₂) ≅ mk (m₃ ≫ m₁) (f₃ ≫ f₂) where
  hom := homMk (h.isoPullback.inv) (by simp [comp]) (by simp [comp])
  inv := homMk (h.isoPullback.hom) (by simp [comp]) (by simp [comp])

/-- Given total morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, we have an isomorphism of partial map
  diagrams between `↑(f ≫ g)` and `↑f ≫ ↑g`. -/
noncomputable def mkOfHomCompIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mkOfHom (f ≫ g) ≅ comp (mkOfHom f) (mkOfHom g) :=
  eqToIso (by simpa using refl (mkOfHom (f ≫ g))) ≪≫
    (mkCompMkIso (𝟙 X) f (𝟙 Y) g (IsPullback.id_horiz f)).symm

/-- Given monomorphisms `m₁ : Y ⟶ X` and `m₂ : Z ⟶ Y`, there is an isomorphism of partial map
  diagrams between `↑(m₂ ≫ m₁)` and `↑m₁ ≫ ↑m₂`, where the coersion `↑(m : X ⟶ Y)` is taking the
  partial map diagram given by inclusion `m` and map `𝟙 X`. -/
noncomputable def mkOfMonoCompIso {X Y Z : C} (m₁ : Y ⟶ X) [Mono m₁] (m₂ : Z ⟶ Y) [Mono m₂] :
    mkOfMono (m₂ ≫ m₁) ≅ comp (mkOfMono m₁) (mkOfMono m₂) :=
  eqToIso (by simp [mkOfMono_def]) ≪≫
    (mkCompMkIso m₁ (𝟙 Y) m₂ (𝟙 Z) (IsPullback.id_vert m₂)).symm

/-- Given a monomorphism `m : U ⟶ X` and morphism `f : U ⟶ Y`, the composition of the
  "support" partial map diagram induced by `m` and the "total map" partial map diagram induced by
  `f` is isomorophic to the partial map diagram given by `m` and `f`. -/
noncomputable def mkOfMonoCompMkOfHomIso {X Y U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    comp (mkOfMono m) (mkOfHom f) ≅ mk m f :=
  mkCompMkIso m (𝟙 U) (𝟙 U) f (IsPullback.id_vert (𝟙 U)) ≪≫
    eqToIso (by simp)

/-- The associator isomorphism in the bicategory of partial map diagrams. -/
noncomputable def associator {W X Y Z : WithPrePartialMaps C}
    (f₁ : W ⟶ X) (f₂ : X ⟶ Y) (f₃ : Y ⟶ Z) :
    comp (comp f₁ f₂) f₃ ≅ comp f₁ (comp f₂ f₃) where
  hom := homMk
    (pullbackAssoc f₁.hom f₂.fst f₂.hom f₃.fst).hom (by simp [comp]) (by simp [comp])
  inv := homMk
    (pullbackAssoc f₁.hom f₂.fst f₂.hom f₃.fst).inv (by simp [comp]) (by simp [comp])

/-- Left whiskering in the bicategory of partial map diagrams. -/
noncomputable def whiskerLeft {X Y Z : WithPrePartialMaps C} (f : X ⟶ Y) {g₁ g₂ : Y ⟶ Z}
    (h : g₁ ⟶ g₂) : comp f g₁ ⟶ comp f g₂ :=
  homMk (pullback.map (f.hom) g₁.fst f.hom g₂.fst (𝟙 f.support) h.hom (𝟙 Y.out) (by simp) (by simp))
    (by simp [comp, pullback.lift_fst_assoc]) (by simp [comp,pullback.lift_snd_assoc])

/-- Right whiskering in the bicategory of partial map diagrams. -/
noncomputable def whiskerRight {X Y Z : WithPrePartialMaps C} {f₁ f₂ : X ⟶ Y}
    (h : f₁ ⟶ f₂) (g : Y ⟶ Z) : comp f₁ g ⟶ comp f₂ g :=
  homMk (pullback.map f₁.hom g.fst f₂.hom g.fst h.hom (𝟙 g.support) (𝟙 Y.out) (by simp) (by simp))
    (by simp [comp, pullback.lift_fst_assoc]) (by simp [comp, pullback.lift_snd_assoc])

/-- The left unitor in the bicategory of partial map diagrams. -/
noncomputable def leftUnitor {X Y : C} (f : X ⇀' Y) : comp (mkOfHom (𝟙 X)) f ≅ f where
  hom := homMk (pullback.snd _ _) (pullback.condition.symm) rfl
  inv := homMk (pullback.lift f.fst (𝟙 f.support) (by simp))
    (by simp [comp, pullback.lift_fst]) (by simp [comp, pullback.lift_snd_assoc])

/-- The right unitor in the bicategory of partial map diagrams. -/
noncomputable def rightUnitor {X Y : C} (f : X ⇀' Y) : comp f (mkOfHom (𝟙 Y)) ≅ f where
  hom := homMk (pullback.fst _ _) (rfl) (pullback.condition)
  inv := homMk (pullback.lift (𝟙 f.support) f.hom)
    (by simp [comp, pullback.lift_fst_assoc]) (by simp [comp, pullback.lift_snd])

noncomputable instance : Bicategory (WithPrePartialMaps C) where
  id X := mkOfHom (𝟙 X.out)
  comp {X Y Z} f g := comp f g
  whiskerLeft {X Y Z} f g₁ g₂ h := whiskerLeft f h
  whiskerRight {X Y Z} f₁ f₂ h g := whiskerRight h g
  associator {W X Y Z} f g h := associator f g h
  leftUnitor {X Y} f := leftUnitor f
  rightUnitor {X Y} f := rightUnitor f

end PrePartialMap
end CategoryTheory

end
