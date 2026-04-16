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

A partial map (in usual parlance, i.e. set theory) from `X` to `Y` is a function from some
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
  map diagrams in `C`.

- `WithPartialMaps C` is the strict bicategory with objects in `C` where morphisms are partial maps
  in `C`.


-/
@[expose] public section

universe v u
namespace CategoryTheory
open Limits
variable {C : Type u} [Category.{v} C]

/-- A (concrete) partial map diagram in a category `C` from `X` to `Y` is a binary fan into `X` and
  `Y` such that the map into `X` is mono. -/
def ObjectProperty.IsPrePartialMap (X Y : C) : ObjectProperty (Limits.BinaryFan X Y) :=
  (Mono ·.fst)

/-- The category of concrete partial map diagrams in the category `C` with domain `X` and
  codomain `X` -/
@[ext]
structure PrePartialMap (X Y : C) where mk' ::
  /-- interpret a partial map diagram as an actual diagram -/
  out : (ObjectProperty.IsPrePartialMap X Y).FullSubcategory

/-- The support of definition of a partial map diagram -/
def PrePartialMap.support {X Y : C} (f : PrePartialMap X Y) : C := f.out.obj.pt

/-- The inclusion of the support into the domain of a partial map diagram -/
def PrePartialMap.fst {X Y : C} (f : PrePartialMap X Y) : f.support ⟶ X := f.out.obj.fst

/-- The underlying (total) map of a partial map diagram -/
def PrePartialMap.hom {X Y : C} (f : PrePartialMap X Y) : f.support ⟶ Y := f.out.obj.snd

variable (C) in
/-- The bicategory `WithPrePartialMaps C` has all objects in `C` as objects,
1-morphisms between `X` and `Y` are partial map diagrams from `X` to `Y`, and 2-morphisms are
given by expanding the support (and therefore unique). -/
structure WithPrePartialMaps where mk ::
  /-- Interpret an object in `WithPrePartialMaps C` as an object in `C` -/
  out : C

attribute [pp_nodot] WithPrePartialMaps.mk

/-- We want to see `WithPrePartialMaps.mk X` instead of `{out := X}` -/
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
A partial map diagram consists of a monomorphism `m : U ⟶ X` and a morphism `f : U ⟶ Y`.
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

/-- Any monomorphism `Y ⟶ X` induces a partial map diagram `X ⇀' Y` with support `Y`. -/
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
structure Hom {X Y : C} (f g : X ⇀' Y) where mk ::
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
lemma homMk_comp {X Y : C} {f₁ f₂ f₃ : X ⇀' Y} (g₁ : f₁.support ⟶ f₂.support)
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
  hom_inv_id := by ext
  inv_hom_id := by ext

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
  hom_inv_id := by ext
  inv_hom_id := by ext

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
  hom_inv_id := by ext
  inv_hom_id := by ext

/-- The right unitor in the bicategory of partial map diagrams. -/
noncomputable def rightUnitor {X Y : C} (f : X ⇀' Y) : comp f (mkOfHom (𝟙 Y)) ≅ f where
  hom := homMk (pullback.fst _ _) (rfl) (pullback.condition)
  inv := homMk (pullback.lift (𝟙 f.support) f.hom)
    (by simp [comp, pullback.lift_fst_assoc]) (by simp [comp, pullback.lift_snd])
  hom_inv_id := by ext
  inv_hom_id := by ext

noncomputable instance : Bicategory (WithPrePartialMaps C) := by
  refine {
    id X := mkOfHom (𝟙 X.out)
    comp {X Y Z} f g := comp f g
    whiskerLeft {X Y Z} f g₁ g₂ h := whiskerLeft f h
    whiskerRight {X Y Z} f₁ f₂ h g := whiskerRight h g
    associator {W X Y Z} f g h := associator f g h
    leftUnitor {X Y} f := leftUnitor f
    rightUnitor {X Y} f := rightUnitor f
    whiskerLeft_id := ?_
    whiskerLeft_comp := ?_
    id_whiskerLeft := ?_
    comp_whiskerLeft := ?_
    id_whiskerRight := ?_
    comp_whiskerRight := ?_
    whiskerRight_id := ?_
    whiskerRight_comp := ?_
    whisker_assoc := ?_
    whisker_exchange := ?_
    pentagon := ?_
    triangle := ?_ } <;> intros <;> ext

end PrePartialMap

/-- The skeleton category of partially defined maps, where given `f g : X ⇀ Y`,
  the map `f ⟶ g` exists iff the support of `g` contains the support of `f` and
  the maps agree on the support of `f` -/
abbrev PartialMap (X Y : C) := ThinSkeleton (X ⇀' Y)
namespace PartialMap

variable (C) in
/-- The 2-category `C` with partial maps in `C` as morphisms. -/
structure _root_.CategoryTheory.WithPartialMaps : Type u where
  mk ::
  /-- interpret an object in `WithPartialMaps C` as an object in `C` -/
  out : C

attribute [pp_nodot] WithPartialMaps.mk

/-- We want to see `WithPartialMaps.mk X` instead of `{out := X}` -/
@[app_unexpander WithPartialMaps.mk]
protected meta def WithPartialMaps.unexpander_mk : Lean.PrettyPrinter.Unexpander
  | s => pure s

instance : Quiver (WithPartialMaps C) where
  Hom X Y := PartialMap X.out Y.out

/-- A partial map between objects `X Y : C` is an object `U : C` with a monomorphism `m : U ⟶ X` and
a morphism `f : U ⟶ Y`, up to isomorphism `U ≅ U'` -/
notation:40 X:41 " ⇀ " Y:41 => WithPartialMaps.mk X ⟶ WithPartialMaps.mk Y

/-- An object `U : C` with a monomorphism `m : U ⟶ X` and a morphism `f : U ⟶ Y` induces a partial
map `X ⇀ Y` by taking the equivalence class of the partial map diagram -/
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

/-- A general recursion principle for partial maps: Every partial map is induced by some
partial map diagram. -/
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

/-- A recursion principle for partial maps: Every partial map is induced by some
partial map diagram. If the motive is always subsingleton, we don't need to prove coherence. -/
def recSubsingleton {X Y : C} {motive : X ⇀ Y → Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y), motive (.mk m f))
    [∀ (f : X ⇀ Y), Subsingleton (motive f)] :
    ∀ (f : X ⇀ Y), motive f := PartialMap.rec ofMk (by intros; apply Subsingleton.elim)

@[simp]
lemma recSubsingleton_mk {X Y : C} {motive : X ⇀ Y → Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y), motive (.mk m f))
    [∀ (f : X ⇀ Y), Subsingleton (motive f)]
    {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  recSubsingleton ofMk (mk m f) = ofMk m f := rfl

@[simp]
lemma rec_mk {X Y : C} {motive : X ⇀ Y → Sort*}
    (ofMk : ∀ {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y), motive (.mk m f))
    (ofMk_sound : ∀ {U₁ : C} (m₁ : U₁ ⟶ X) [Mono m₁] (f₁ : U₁ ⟶ Y),
      ∀ {U₂ : C} (m₂ : U₂ ⟶ X) [Mono m₂] (f₂ : U₂ ⟶ Y),
      (h : mk m₁ f₁ = mk m₂ f₂) → cast congr(motive $h) (ofMk m₁ f₁) = ofMk m₂ f₂)
    {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    PartialMap.rec ofMk ofMk_sound (mk m f) = ofMk m f := rfl

/-- Induction on partial maps. -/
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

/-- The support of a partial map. -/
protected def support {X Y : C} : X ⇀ Y ⥤ Subobject X :=
  ThinSkeleton.map PrePartialMap.overMono

lemma support.obj_mk {X Y : C} {U : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
  PartialMap.support.obj (mk m f) = Subobject.mk m := rfl

variable [HasPullbacks C]
/-- The composition of partial maps. -/
noncomputable def comp {X Y Z : C} : X ⇀ Y ⥤ Y ⇀ Z ⥤ X ⇀ Z :=
  ThinSkeleton.map₂ (Bicategory.precomposing
    (WithPrePartialMaps.mk X) (WithPrePartialMaps.mk Y) (WithPrePartialMaps.mk Z))

/-- Any map in `C` induces a total partial map. -/
def ofHom {X Y : C} (f : X ⟶ Y) : X ⇀ Y := mk (𝟙 _) f

omit [HasPullbacks C] in
lemma ofHom_eq_mk {X Y : C} (f : X ⟶ Y) : ofHom f = mk (𝟙 _) f := rfl

/-- A monomorphism `m : Y ⟶ X` induces a partial map `X ⇀ Y` which acts as the identity on
its support `Y` -/
def ofMono {X Y : C} (m : Y ⟶ X) [Mono m] : X ⇀ Y := mk m (𝟙 _)

omit [HasPullbacks C] in
lemma ofMono_eq_mk {X Y : C} (m : Y ⟶ X) [Mono m] : ofMono m = mk m (𝟙 _) := rfl

/-- The identity partial map -/
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
  associator {W X Y Z} := PartialMap.recSubsingleton
    (fun m₁ _ f₁ => PartialMap.recSubsingleton
      (fun m₂ _ f₂ => PartialMap.recSubsingleton
        (fun m₃ _ f₃ =>
          eqToIso (Quotient.sound ⟨
            (PrePartialMap.associator
            (PrePartialMap.mk m₁ f₁)
            (PrePartialMap.mk m₂ f₂)
            (PrePartialMap.mk m₃ f₃))⟩))))
  leftUnitor {X Y} := PartialMap.recSubsingleton
    (fun m₁ _ f₁ => eqToIso (Quotient.sound ⟨PrePartialMap.leftUnitor (PrePartialMap.mk m₁ f₁)⟩))
  rightUnitor {X Y} := PartialMap.recSubsingleton
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
/-- The essential data of the embedding of a category into its category of partial maps. -/
noncomputable abbrev withPartialMapsPreCore [HasPullbacks C] : StrictPseudofunctorPreCore
    (LocallyDiscrete C) (WithPartialMaps C) where
  obj X := .mk X.as
  map f := PartialMap.ofHom f.as
  map₂ g := eqToHom (by rw [LocallyDiscrete.eq_of_hom g])
  map_comp {X Y Z} f₁ f₂ := Quotient.sound ⟨PrePartialMap.mkOfHomCompIso f₁.as f₂.as⟩

variable (C) in
/-- The embedding of a category into its category of partial maps. -/
noncomputable def _root_.CategoryTheory.withPartialMaps [HasPullbacks C] :
    StrictPseudofunctor (LocallyDiscrete C) (WithPartialMaps C) :=
  .mk'' (withPartialMapsPreCore C)

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

instance [HasPullbacks C] : ((withPartialMaps C).toFunctor).Faithful where
  map_injective {_ _} _ _ h := congr($(ofHom_injective h).toLoc)

lemma mono_of_mono_ofHom [HasPullbacks C] {X Y : C} {f : X ⟶ Y} :
    Mono (PartialMap.ofHom f) → Mono f := by
  intro h
  change Mono ((toLocallyDiscreteFunc C ⋙ (withPartialMaps C).toFunctor).map f) at h
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

instance [HasPullbacks C] {X U Y : C} (m : U ⟶ X) [IsIso m] (f : U ⟶ Y) [Mono f] :
    Mono (PartialMap.mk m f) := by
  rw [mono_iff_exists_eq_ofHom_and_mono]
  use (inv m ≫ f), Quotient.sound
    ⟨⟨PrePartialMap.homMk m, PrePartialMap.homMk (inv m : X ⟶ U), by ext, by ext⟩⟩
  infer_instance

open Bicategory
variable (C) in
/-- The coyoneda 1-functor for the bicategory of partial maps in some category. -/
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

/-- The presheaf of partial map functors. -/
noncomputable def _root_.CategoryTheory.partialMaps
  [HasPullbacks C] : Cᵒᵖ ⥤ C ⥤ Type _ :=
  (((Functor.whiskeringLeft₂ (Type _)).obj (toLocallyDiscreteFunc C ⋙
    (withPartialMaps C).toFunctor).op).obj
    (toLocallyDiscreteFunc C ⋙ (withPartialMaps C).toFunctor)).obj
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

/-- The presheaf of partial maps into the object `X : C`. -/
noncomputable def _root_.CategoryTheory.partialMapsTo [HasPullbacks C] (X : C) :
  Cᵒᵖ ⥤ Type _ := partialMaps.flip.obj X

@[simp]
lemma _root_.CategoryTheory.partialMapsTo_obj [HasPullbacks C] (X : C) (Y : Cᵒᵖ) :
  (partialMapsTo X).obj Y = ((WithPartialMaps.mk Y.unop) ⟶ (WithPartialMaps.mk X)) := rfl

@[simp]
lemma _root_.CategoryTheory.partialMapsTo_map [HasPullbacks C] (X : C) {Y Z : Cᵒᵖ} (g : Y ⟶ Z) :
  (partialMapsTo X).map g = (PartialMap.ofHom g.unop ≫ ·) := rfl

/-- The copresheaf of partial maps from the object `X : C` -/
noncomputable def _root_.CategoryTheory.partialMapsFrom [HasPullbacks C] (X : C) :
  C ⥤ Type _ := partialMaps.obj (.op X)

@[simp]
lemma _root_.CategoryTheory.partialMapsFrom_obj [HasPullbacks C] (X Y : C) :
  (partialMapsFrom X).obj Y = ((WithPartialMaps.mk X) ⟶ (WithPartialMaps.mk Y)) := rfl

@[simp]
lemma _root_.CategoryTheory.partialMapsFrom_map [HasPullbacks C] (X : C) {Y Z : C} (g : Y ⟶ Z) :
  (partialMapsFrom X).map g = (· ≫ PartialMap.ofHom g) := rfl


end CategoryTheory.WithPartialMaps
