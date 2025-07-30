/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.CatCommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.CatCospanTransform

/-! # Categorical pullbacks

This file defines the basic properties of categorical pullbacks.

Given a pair of functors `(F : A ⥤ B, G : C ⥤ B)`, we define the category
`CategoricalPullback F G` as the category of triples
`(a : A, c : C, e : F.obj a ≅ G.obj b)`.

The category `CategoricalPullback F G` sits in a canonical `CatCommSq`, and we formalize that
this square is a "limit" in the following sense: functors `X ⥤ CategoricalPullback F G` are
equivalent to pairs of functors `(L : X ⥤ A, R : X ⥤ C)` equipped with a natural isomorphism
`L ⋙ F ≅ R ⋙ G`.

We formalize this by introducing a category `CatCommSqOver F G X` that encodes
exactly this data, and we prove that the category of functors `X ⥤ CategoricalPullback F G` is
equivalent to `CatCommSqOver F G X`.

## Main declarations

* `CategoricalPullback F G`: the type of the categorical pullback.
* `π₁ F G : CategoricalPullback F G` and `π₂ F G : CategoricalPullback F G`: the canonical
  projections.
* `CategoricalPullback.catCommSq`: the canonical `CatCommSq (π₁ F G) (π₂ F G) F G` which exhibits
  `CategoricalPullback F G` as the pullback (in the (2,1)-categorical sense)
  of the cospan of `F` and `G`.
* `CategoricalPullback.functorEquiv F G X`: the equivalence of categories between functors
  `X ⥤ CategoricalPullback F G` and `CatCommSqOver F G X`, where the latter is an abbrev for
  `CategoricalPullback (whiskeringRight X A B|>.obj F) (whiskeringRight X C B|>.obj G)`.

## References
* [Kerodon: section 1.4.5.2](https://kerodon.net/tag/032Y)
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
  example 5.3.9, although we take a slightly different (equivalent) model of the object.

## TODOs:
* Define the "categorical fiber" of a functor at an object of the target category.
* Pasting calculus for categorical pullback squares.
* Categorical pullback squares attached to Grothendieck constructions of pseudofunctors.
* Stability of (co)fibered categories under categorical pullbacks.

-/

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃

namespace CategoryTheory.Limits

attribute [local simp] CatCommSq.iso_hom_naturality  CatCommSq.iso_inv_naturality

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  (F : A ⥤ B) (G : C ⥤ B)

/-- The `CategoricalPullback F G` is the category of triples
`(a : A, c : C, F a ≅ G c)`.
Morphisms `(a, c, e) ⟶ (a', c', e')` are pairs of morphisms
`(f₁ : a ⟶ a', f₂ : c ⟶ c')` compatible with the specified
isomorphisms. -/
@[kerodon 032Z]
structure CategoricalPullback where
  /-- the first component element -/
  fst : A
  /-- the second component element -/
  snd : C
  /-- the structural isomorphism `F.obj fst ≅ G.obj snd` -/
  iso : F.obj fst ≅ G.obj snd

namespace CategoricalPullback

/-- A notation for the categorical pullback. -/
scoped notation:max L:max " ⊡ " R:max => CategoricalPullback L R

variable {F G}

/-- The Hom types for the categorical pullback are given by pairs of maps compatible with the
structural isomorphisms. -/
@[ext]
structure Hom (x y : F ⊡ G) where
  /-- the first component of `f : Hom x y` is a morphism `x.fst ⟶ y.fst` -/
  fst : x.fst ⟶ y.fst
  /-- the second component of `f : Hom x y` is a morphism `x.snd ⟶ y.snd` -/
  snd : x.snd ⟶ y.snd
  /-- the compatibility condition on `fst` and `snd` with respect to the structure
  isompophisms -/
  w : F.map fst ≫ y.iso.hom = x.iso.hom ≫ G.map snd := by aesop_cat

attribute [reassoc (attr := simp)] Hom.w

@[simps! id_fst id_snd comp_fst comp_snd]
instance : Category (CategoricalPullback F G) where
  Hom x y := CategoricalPullback.Hom x y
  id x :=
    { fst := 𝟙 x.fst
      snd := 𝟙 x.snd }
  comp f g :=
    { fst := f.fst ≫ g.fst
      snd := f.snd ≫ g.snd }

attribute [reassoc] comp_fst comp_snd

/-- Naturality square for morphisms in the inverse direction. -/
@[reassoc (attr := simp)]
lemma Hom.w' {x y : F ⊡ G} (f : x ⟶ y) :
    G.map f.snd ≫ y.iso.inv = x.iso.inv ≫ F.map f.fst := by
  rw [Iso.comp_inv_eq, Category.assoc, Eq.comm, Iso.inv_comp_eq, f.w]

/-- Extensionnality principle for morphisms in `CategoricalPullback F G`. -/
@[ext]
theorem hom_ext {x y : F ⊡ G} {f g : x ⟶ y}
    (hₗ : f.fst = g.fst) (hᵣ : f.snd = g.snd) : f = g := by
  apply Hom.ext <;> assumption

section

variable (F G)

/-- `CategoricalPullback.π₁ F G` is the first projection `CategoricalPullback F G ⥤ A`. -/
@[simps]
def π₁ : F ⊡ G ⥤ A where
  obj x := x.fst
  map f := f.fst

/-- `CategoricalPullback.π₂ F G` is the second projection `CategoricalPullback F G ⥤ C`. -/
@[simps]
def π₂ : F ⊡ G ⥤ C where
  obj x := x.snd
  map f := f.snd

/-- The canonical categorical commutative square in which `CategoricalPullback F G` sits. -/
@[simps!]
instance catCommSq : CatCommSq (π₁ F G) (π₂ F G) F G where
  iso := NatIso.ofComponents (fun x ↦ x.iso)

variable {F G} in
/-- Constructor for isomorphisms in `CategoricalPullback F G`. -/
@[simps!]
def mkIso {x y : F ⊡ G}
    (eₗ : x.fst ≅ y.fst) (eᵣ : x.snd ≅ y.snd)
    (w : F.map eₗ.hom ≫ y.iso.hom = x.iso.hom ≫ G.map eᵣ.hom := by aesop_cat) :
    x ≅ y where
  hom := ⟨eₗ.hom, eᵣ.hom, w⟩
  inv := ⟨eₗ.inv, eᵣ.inv, by simpa using F.map eₗ.inv ≫= w.symm =≫ G.map eᵣ.inv⟩

section

variable {x y : F ⊡ G} (f : x ⟶ y) [IsIso f]

instance : IsIso f.fst :=
  inferInstanceAs (IsIso ((π₁ _ _).mapIso (asIso f)).hom)

instance : IsIso f.snd :=
  inferInstanceAs (IsIso ((π₂ _ _).mapIso (asIso f)).hom)

@[simp]
lemma inv_fst : (inv f).fst = inv f.fst := by
  symm
  apply IsIso.inv_eq_of_hom_inv_id
  simpa [-IsIso.hom_inv_id] using congrArg (fun t ↦ t.fst) (IsIso.hom_inv_id f)

@[simp]
lemma inv_snd : (inv f).snd = inv f.snd := by
  symm
  apply IsIso.inv_eq_of_hom_inv_id
  simpa [-IsIso.hom_inv_id] using congrArg (fun t ↦ t.snd) (IsIso.hom_inv_id f)

end

lemma isIso_iff {x y : F ⊡ G} (f : x ⟶ y) :
    IsIso f ↔ (IsIso f.fst ∧ IsIso f.snd) where
  mp h := ⟨inferInstance, inferInstance⟩
  mpr | ⟨h₁, h₂⟩ => ⟨⟨inv f.fst, inv f.snd, by aesop_cat⟩, by aesop_cat⟩

end

section

open Functor

variable (X : Type u₄) [Category.{v₄} X]

variable (F G) in
/-- The data of a categorical commutative square over a cospan `F, G` with cone point `X` is
that of a functor `T : X ⥤ A`, a functor `L : X ⥤ C`, and a `CatCommSqOver T L F G`.
Note that this is *exactly* what an object of
`((whiskeringRight X A B).obj F) ⊡ ((whiskeringRight X C B).obj G)` is,
so `CatCommSqOver F G X` is in fact an abbreviation for
`((whiskeringRight X A B).obj F) ⊡ ((whiskeringRight X C B).obj G)`. -/
abbrev CatCommSqOver :=
  (whiskeringRight X A B|>.obj F) ⊡ (whiskeringRight X C B|>.obj G)

namespace CatCommSqOver

/-- Interpret a `CatCommSqOver F G X` as a `CatCommSq`. -/
@[simps]
instance asSquare (S : CatCommSqOver F G X) : CatCommSq S.fst S.snd F G where
  iso := S.iso

@[reassoc (attr := simp)]
lemma iso_hom_naturality (S : CatCommSqOver F G X) {x x' : X} (f : x ⟶ x') :
   F.map (S.fst.map f) ≫ S.iso.hom.app x' =
   S.iso.hom.app x ≫ G.map (S.snd.map f) :=
  S.iso.hom.naturality f

@[reassoc (attr := simp)]
lemma w_app {S S' : CatCommSqOver F G X} (φ : S ⟶ S') (x : X) :
    F.map (φ.fst.app x) ≫ S'.iso.hom.app x =
    S.iso.hom.app x ≫ G.map (φ.snd.app x) :=
  NatTrans.congr_app φ.w x

@[reassoc (attr := simp)]
lemma Iso.hom_inv_id_fst_app {S S' : CatCommSqOver F G X} (e : S ≅ S') (x : X) :
    e.hom.fst.app x ≫ e.inv.fst.app x = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← comp_fst]

@[reassoc (attr := simp)]
lemma Iso.hom_inv_id_snd_app {S S' : CatCommSqOver F G X} (e : S ≅ S') (x : X) :
    e.hom.snd.app x ≫ e.inv.snd.app x = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← comp_snd]

@[reassoc (attr := simp)]
lemma Iso.inv_hom_id_fst_app {S S' : CatCommSqOver F G X} (e : S ≅ S') (x : X) :
    e.inv.fst.app x ≫ e.hom.fst.app x = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← comp_fst]

@[reassoc (attr := simp)]
lemma Iso.inv_hom_id_snd_app {S S' : CatCommSqOver F G X} (e : S ≅ S') (x : X) :
    e.inv.snd.app x ≫ e.hom.snd.app x = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← comp_snd]

@[reassoc (attr := simp)]
lemma Iso.hom_inv_id_app_fst_app {J : Type*} [Category J]
    {S S' : J ⥤ CatCommSqOver F G X} (e : S ≅ S') (j : J) (x : X) :
    (e.hom.app j).fst.app x ≫ (e.inv.app j).fst.app x = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← comp_fst]

@[reassoc (attr := simp)]
lemma Iso.hom_inv_id_app_snd_app {J : Type*} [Category J]
    {S S' : J ⥤ CatCommSqOver F G X} (e : S ≅ S') (j : J) (x : X) :
    (e.hom.app j).snd.app x ≫ (e.inv.app j).snd.app x = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← comp_snd]

@[reassoc (attr := simp)]
lemma Iso.inv_hom_id_app_fst_app {J : Type*} [Category J]
    {S S' : J ⥤ CatCommSqOver F G X} (e : S ≅ S') (j : J) (x : X) :
    (e.inv.app j).fst.app x ≫ (e.hom.app j).fst.app x = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← comp_fst]

@[reassoc (attr := simp)]
lemma Iso.inv_hom_id_app_snd_app {J : Type*} [Category J]
    {S S' : J ⥤ CatCommSqOver F G X} (e : S ≅ S') (j : J) (x : X) :
    (e.inv.app j).snd.app x ≫ (e.hom.app j).snd.app x = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← comp_snd]

variable {X} in
/-- Interpret a `CatCommSq` as a `CatCommSqOver`. -/
@[simps]
def ofSquare (T : A ⥤ B) (L : A ⥤ C) (R : B ⥤ X) (B_ : C ⥤ X)
    [CatCommSq T L R B_] : CatCommSqOver R B_ A where
  fst := T
  snd := L
  iso := CatCommSq.iso T L R B_

variable (F G)

/-- The "first projection" of a CatCommSqOver as a functor. -/
abbrev fstFunctor : CatCommSqOver F G X ⥤ X ⥤ A := π₁ _ _

/-- The "second projection" of a CatCommSqOver as a functor. -/
abbrev sndFunctor : CatCommSqOver F G X ⥤ X ⥤ C := π₂ _ _

/-- The structure isompophism of a `CatCommSqOver` as a natural transformation. -/
abbrev e :
    fstFunctor F G X ⋙ (whiskeringRight X A B).obj F ≅
    sndFunctor F G X ⋙ (whiskeringRight X C B).obj G :=
  NatIso.ofComponents (fun S ↦ S.iso)

/-- There is a canonical inhabitant of
`CatCommSqOver F G (CategoricalPullback F G)` corresponding to the
canonical square `catCommSq` -/
@[simps]
instance : Inhabited (CatCommSqOver F G <| F ⊡ G) where
  default := ofSquare (π₁ F G) (π₂ F G) F G

-- this is a non-diamond
example : (default : CatCommSqOver F G <| F ⊡ G).asSquare = catCommSq F G := rfl

end CatCommSqOver

section functorEquiv

variable (F G)

-- We need to split up the definition of `functorEquiv` to avoid timeouts.

/-- Interpret a functor to the categorical pullback as a `CatCommSqOver`. -/
@[simps!]
def toCatCommSqOver : (X ⥤ F ⊡ G) ⥤ CatCommSqOver F G X where
  obj J :=
    { fst := J ⋙ π₁ F G
      snd := J ⋙ π₂ F G
      iso :=
        associator _ _ _ ≪≫
          isoWhiskerLeft J (catCommSq F G).iso ≪≫
          (associator _ _ _).symm }
  map {J J'} F :=
    { fst := whiskerRight F (π₁ _ _)
      snd := whiskerRight F (π₂ _ _) }

/-- Interpret a `CatCommSqOver` as a functor to the categorical pullback. -/
@[simps!]
def CatCommSqOver.toFunctorToCategoricalPullback :
    (CatCommSqOver F G X) ⥤ X ⥤ F ⊡ G where
  obj S :=
    { obj x :=
        { fst := S.fst.obj x
          snd := S.snd.obj x
          iso := S.iso.app x }
      map {x y} f :=
        { fst := S.fst.map f
          snd := S.snd.map f } }
  map {S S'} φ :=
    { app x :=
        { fst := φ.fst.app x
          snd := φ.snd.app x } }

/-- The universal property of categorical pullbacks, stated as an equivalence
of categories between functors `X ⥤ (F ⊡ G)` and categorical commutative
squares over X.
Note that this equivalence should be considered as an
implementation detail. Should you want to use the universal property, you should
use the equivalence `CatPullbackSquare.functorEquiv` defined in
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Categorical/Square.lean` instead,
which provides a similar equivalence thanks to a
`CatPullbackSquare (π₁ F G) (π₂ F G) F G` instance. -/
@[simps]
def functorEquiv : (X ⥤ F ⊡ G) ≌ CatCommSqOver F G X where
  functor := toCatCommSqOver F G X
  inverse := CatCommSqOver.toFunctorToCategoricalPullback F G X
  unitIso :=
    NatIso.ofComponents
      (fun _ ↦ NatIso.ofComponents
        (fun _ ↦ CategoricalPullback.mkIso (.refl _) (.refl _)))
  counitIso :=
    NatIso.ofComponents
      (fun _ ↦ CategoricalPullback.mkIso
        (NatIso.ofComponents (fun _ ↦ .refl _)) (NatIso.ofComponents (fun _ ↦ .refl _)))

end functorEquiv

end

section Bifunctoriality

namespace CatCommSqOver
open Functor

section transform

variable {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
  [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
  {F' : A' ⥤ B'} {G' : C' ⥤ B'}

/-- Functorially transform a `CatCommSqOver F G X` by whiskering it with a
`CatCospanTransform`. -/
@[simps]
def transform (X : Type u₇) [Category.{v₇} X] :
    CatCospanTransform F G F' G' ⥤
      CatCommSqOver F G X ⥤ CatCommSqOver F' G' X where
  obj ψ :=
    { obj S :=
        { fst := S.fst ⋙ ψ.left
          snd := S.snd ⋙ ψ.right
          iso :=
            (Functor.associator _ _ _) ≪≫
              isoWhiskerLeft S.fst (ψ.squareLeft.iso.symm) ≪≫
              (Functor.associator _ _ _).symm ≪≫
              isoWhiskerRight S.iso _ ≪≫
              isoWhiskerLeft S.snd (ψ.squareRight.iso) ≪≫
              (Functor.associator _ _ _).symm }
      map {x y} f :=
        { fst := whiskerRight f.fst ψ.left
          snd := whiskerRight f.snd ψ.right
          w := by
            ext x
            dsimp
            simp only [Category.comp_id, Category.id_comp,
              CatCommSq.iso_inv_naturality_assoc, Category.assoc,
              NatIso.cancel_natIso_inv_left, Functor.comp_obj]
            simp [← Functor.map_comp_assoc] } }
  map {ψ ψ'} η :=
    { app S :=
      { fst := { app y := η.left.app (S.fst.obj y) }
        snd := { app y := η.right.app (S.snd.obj y) }
        w := by
          ext t
          dsimp
          simp only [Category.comp_id, Category.id_comp, Category.assoc,
            CatCospanTransformMorphism.right_coherence_app, Functor.comp_obj,
            NatTrans.naturality_assoc]
          haveI := ψ.squareLeft.iso.inv.app (S.fst.obj t) ≫=
            η.left_coherence_app (S.fst.obj t)
          simp only [Iso.inv_hom_id_app_assoc] at this
          simp [this] } }

variable {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
  [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
  {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}

/-- The construction `CatCommSqOver.transform` respects vertical composition
of `CatCospanTransform`s. -/
@[simps!]
def transformObjComp (X : Type u₁₀) [Category.{v₁₀} X]
    (ψ : CatCospanTransform F G F' G') (ψ' : CatCospanTransform F' G' F'' G'') :
    (transform X).obj (ψ.comp ψ') ≅ (transform X).obj ψ ⋙ (transform X).obj ψ' :=
  NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.associator _ _ _).symm
      (Functor.associator _ _ _).symm

/-- The construction `CatCommSqOver.transform` respects the identity
`CatCospanTransform`s. -/
@[simps!]
def transformObjId (X : Type u₄) [Category.{v₄} X]
    (F : A ⥤ B) (G : C ⥤ B) :
    (transform X).obj (CatCospanTransform.id F G) ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.rightUnitor _)
      (Functor.rightUnitor _)

open scoped CatCospanTransform

lemma transform_map_whiskerLeft
    (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F' G')
    {φ φ' : CatCospanTransform F' G' F'' G''} (α : φ ⟶ φ') :
    (transform X).map (ψ ◁ α) =
    (transformObjComp X ψ φ).hom ≫
      whiskerLeft (transform X|>.obj ψ) (transform X|>.map α) ≫
      (transformObjComp X ψ φ').inv := by
  aesop_cat

lemma transform_map_whiskerRight
    (X : Type u₇) [Category.{v₇} X]
    {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ')
    (φ : CatCospanTransform F' G' F'' G'') :
    (transform X).map (α ▷ φ) =
    (transformObjComp X ψ φ).hom ≫
      whiskerRight (transform X|>.map α) (transform X|>.obj φ) ≫
      (transformObjComp X ψ' φ).inv := by
  aesop_cat

lemma transform_map_associator
    {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂}
    [Category.{v₁₀} A'''] [Category.{v₁₁} B'''] [Category.{v₁₂} C''']
    {F''' : A''' ⥤ B'''} {G''' : C''' ⥤ B'''}
    (X : Type u₁₃) [Category.{v₁₃} X]
    (ψ : CatCospanTransform F G F' G') (φ : CatCospanTransform F' G' F'' G'')
    (τ : CatCospanTransform F'' G'' F''' G''') :
    (transform X).map (α_ ψ φ τ).hom =
    (transformObjComp X (ψ.comp φ) τ).hom ≫
      whiskerRight (transformObjComp X ψ φ).hom (transform X|>.obj τ) ≫
      ((transform X|>.obj ψ).associator
        (transform X|>.obj φ) (transform X|>.obj τ)).hom ≫
      whiskerLeft (transform X|>.obj ψ) (transformObjComp X φ τ).inv ≫
      (transformObjComp X ψ (φ.comp τ)).inv := by
  aesop_cat

lemma transform_map_leftUnitor (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F' G') :
    (transform X).map (λ_ ψ).hom =
    (transformObjComp X (.id F G) ψ).hom ≫
      whiskerRight (transformObjId X F G).hom (transform X|>.obj ψ) ≫
      (transform X|>.obj ψ).leftUnitor.hom := by
  aesop_cat

lemma transform_map_rightUnitor (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F' G') :
    (transform X).map (ρ_ ψ).hom =
    (transformObjComp X ψ (.id F' G')).hom ≫
      whiskerLeft (transform X|>.obj ψ) (transformObjId X F' G').hom ≫
      (transform X|>.obj ψ).rightUnitor.hom := by
  aesop_cat

end transform

section precompose

variable (F G)

variable
    {X : Type u₄} {Y : Type u₅} {Z : Type u₆}
    [Category.{v₄} X] [Category.{v₅} Y] [Category.{v₆} Z]

/-- A functor `U : X ⥤ Y` (functorially) induces a functor
`CatCommSqOver F G Y ⥤ CatCommSqOver F G X` by whiskering left the underlying
categorical commutative square by U. -/
@[simps]
def precompose :
    (X ⥤ Y) ⥤ CatCommSqOver F G Y ⥤ CatCommSqOver F G X where
  obj U :=
    { obj S :=
        { fst := U ⋙ S.fst
          snd := U ⋙ S.snd
          iso :=
            (Functor.associator _ _ _) ≪≫
              isoWhiskerLeft U S.iso ≪≫
              (Functor.associator _ _ _).symm }
      map {S S'} φ :=
        { fst := whiskerLeft U φ.fst
          snd := whiskerLeft U φ.snd } }
  map {U V} α :=
    { app x :=
      { fst := whiskerRight α x.fst
        snd := whiskerRight α x.snd } }

variable (X) in
/-- The construction `precompose` respects functor identities. -/
@[simps!]
def precomposeObjId :
    (precompose F G).obj (𝟭 X) ≅ 𝟭 (CatCommSqOver F G X) :=
  NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso (Functor.leftUnitor _) (Functor.leftUnitor _)

/-- The construction `precompose` respects functor composition. -/
@[simps!]
def precomposeObjComp (U : X ⥤ Y) (V : Y ⥤ Z) :
    (precompose F G).obj (U ⋙ V) ≅
    (precompose F G).obj V ⋙ (precompose F G).obj U :=
  NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.associator _ _ _)
      (Functor.associator _ _ _)

lemma precompose_map_whiskerLeft (U : X ⥤ Y) {V W : Y ⥤ Z} (α : V ⟶ W) :
    (precompose F G).map (whiskerLeft U α) =
    (precomposeObjComp F G U V).hom ≫
      whiskerRight (precompose F G|>.map α) (precompose F G|>.obj U) ≫
      (precomposeObjComp F G U W).inv := by
  aesop_cat

lemma precompose_map_whiskerRight {U V : X ⥤ Y} (α : U ⟶ V) (W : Y ⥤ Z) :
    (precompose F G).map (whiskerRight α W) =
    (precomposeObjComp F G U W).hom ≫
      whiskerLeft (precompose F G|>.obj W) (precompose F G|>.map α) ≫
      (precomposeObjComp F G V W).inv := by
  aesop_cat

lemma precompose_map_associator {T : Type u₇} [Category.{v₇} T]
    (U : X ⥤ Y) (V : Y ⥤ Z) (W : Z ⥤ T) :
    (precompose F G).map (U.associator V W).hom =
    (precomposeObjComp F G (U ⋙ V) W).hom ≫
      whiskerLeft (precompose F G|>.obj W) (precomposeObjComp F G U V).hom ≫
      ((precompose F G|>.obj W).associator _ _).inv ≫
      whiskerRight (precomposeObjComp F G V W).inv (precompose F G|>.obj U) ≫
      (precomposeObjComp F G _ _).inv := by
  aesop_cat

lemma precompose_map_leftUnitor (U : X ⥤ Y) :
    (precompose F G).map U.leftUnitor.hom =
    (precomposeObjComp F G (𝟭 _) U).hom ≫
      whiskerLeft (precompose F G|>.obj U) (precomposeObjId F G X).hom ≫
      (Functor.rightUnitor _).hom := by
  aesop_cat

lemma precompose_map_rightUnitor (U : X ⥤ Y) :
    (precompose F G).map U.rightUnitor.hom =
    (precomposeObjComp F G U (𝟭 _)).hom ≫
      whiskerRight (precomposeObjId F G Y).hom (precompose F G|>.obj U) ≫
      (Functor.leftUnitor _).hom := by
  aesop_cat

end precompose

section compatibility

variable {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
  [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
  {F' : A' ⥤ B'} {G' : C' ⥤ B'}

/-- The canonical compatibility square between (the object components of)
`precompose` and `transform`.
This is a "naturality square" if we think as `transform _|>.obj _` as the
(app component of the) map component of a pseudofunctor from the bicategory of
categorical cospans with value in pseudofunctors
(its value on the categorical cospan `F, G` being the pseudofunctor
`precompose F G|>.obj _`). -/
@[simps!]
instance precomposeObjTransformObjSquare
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (ψ : CatCospanTransform F G F' G') (U : X ⥤ Y) :
    CatCommSq
      (precompose F G|>.obj U) (transform Y|>.obj ψ)
      (transform X|>.obj ψ) (precompose F' G'|>.obj U) where
  iso := NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.associator _ _ _)
      (Functor.associator _ _ _)

-- Compare the next 3 lemmas with the components of a strong natural transform
-- of pseudofunctors

/-- The square `precomposeObjTransformObjSquare` is itself natural. -/
lemma precomposeObjTransformObjSquare_iso_hom_naturality₂
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (ψ : CatCospanTransform F G F' G')
    {U V : X ⥤ Y} (α : U ⟶ V) :
    whiskerRight (precompose F G|>.map α) (transform X|>.obj ψ) ≫
      (CatCommSq.iso _ (transform Y|>.obj ψ) _ (precompose F' G'|>.obj V)).hom =
    (CatCommSq.iso _ (transform Y|>.obj ψ) _ (precompose F' G'|>.obj U)).hom ≫
      whiskerLeft (transform Y|>.obj ψ) (precompose F' G'|>.map α) := by
  aesop_cat

/-- The square `precomposeObjTransformOBjSquare` respects identities. -/
lemma precomposeObjTransformObjSquare_iso_hom_id
    (ψ : CatCospanTransform F G F' G') (X : Type u₇) [Category.{v₇} X] :
    (CatCommSq.iso (precompose F G|>.obj <| 𝟭 X) (transform X|>.obj ψ)
      (transform X|>.obj ψ) (precompose F' G'|>.obj <| 𝟭 X)).hom ≫
      whiskerLeft (transform X|>.obj ψ) (precomposeObjId F' G' X).hom =
    whiskerRight (precomposeObjId F G X).hom (transform X|>.obj ψ) ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv := by
  aesop_cat

/-- The square `precomposeTransformSquare` respects compositions. -/
lemma precomposeObjTransformObjSquare_iso_hom_comp
    {X : Type u₇} {Y : Type u₈} {Z : Type u₉}
    [Category.{v₇} X] [Category.{v₈} Y] [Category.{v₉} Z]
    (ψ : CatCospanTransform F G F' G')
    (U : X ⥤ Y) (V : Y ⥤ Z) :
    (CatCommSq.iso (precompose F G|>.obj <| U ⋙ V) (transform Z|>.obj ψ)
      (transform X|>.obj ψ) (precompose F' G'|>.obj <| U ⋙ V)).hom ≫
      whiskerLeft (transform Z|>.obj ψ) (precomposeObjComp F' G' U V).hom =
    whiskerRight (precomposeObjComp F G U V).hom (transform X|>.obj ψ) ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (precompose F G|>.obj V)
        (CatCommSq.iso _ (transform _|>.obj ψ) _ _).hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (CatCommSq.iso _ _ _ _).hom
        (precompose F' G'|>.obj U) ≫
      (Functor.associator _ _ _).hom := by
  aesop_cat

/-- The canonical compatibility square between (the object components of)
`transform` and `precompose`.
This is a "naturality square" if we think as `precompose` as the
(app component of the) map component of a pseudofunctor from the opposite
bicategory of categories to pseudofunctors of categorical cospans
(its value on `X` being the pseudofunctor `transform X _`). -/
@[simps!]
instance transformObjPrecomposeObjSquare
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) (ψ : CatCospanTransform F G F' G') :
    CatCommSq
      (transform Y|>.obj ψ) (precompose F G|>.obj U)
      (precompose F' G'|>.obj U) (transform X|>.obj ψ) where
  iso := NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.associator _ _ _).symm
      (Functor.associator _ _ _).symm

-- Compare the next 3 lemmas with the components of a strong natural transform
-- of pseudofunctors

/-- The square `transformObjPrecomposeObjSquare` is itself natural. -/
lemma transformObjPrecomposeObjSquare_iso_hom_naturality₂
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) {ψ ψ' : CatCospanTransform F G F' G'} (η : ψ ⟶ ψ') :
    whiskerRight (transform Y|>.map η) (precompose F' G'|>.obj U) ≫
      (CatCommSq.iso _ (precompose F G|>.obj U) _ (transform X|>.obj ψ')).hom =
    (CatCommSq.iso _ (precompose F G|>.obj U) _ (transform X|>.obj ψ)).hom ≫
      whiskerLeft (precompose F G|>.obj U) (transform X|>.map η) := by
  aesop_cat

/-- The square `transformObjPrecomposeObjSquare` respects identities. -/
lemma transformObjPrecomposeObjSquare_iso_hom_id
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) (F : A ⥤ B) (G : C ⥤ B) :
    (CatCommSq.iso (transform Y|>.obj <| .id F G) (precompose F G|>.obj U)
      (precompose F G|>.obj U) (transform X|>.obj <| .id F G)).hom ≫
      whiskerLeft (precompose F G|>.obj U) (transformObjId X F G).hom =
    whiskerRight (transformObjId Y F G).hom (precompose F G|>.obj U) ≫
      (precompose F G|>.obj U).leftUnitor.hom ≫
      (precompose F G|>.obj U).rightUnitor.inv := by
  aesop_cat

/-- The square `transformPrecomposeSquare` respects compositions. -/
lemma transformPrecomposeObjSquare_iso_hom_comp
    {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
    [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
    {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}
    {X : Type u₁₀} {Y : Type u₁₁} [Category.{v₁₀} X] [Category.{v₁₁} Y]
    (U : X ⥤ Y) (ψ : CatCospanTransform F G F' G')
    (ψ' : CatCospanTransform F' G' F'' G'') :
    (CatCommSq.iso (transform Y|>.obj <| ψ.comp ψ') (precompose F G|>.obj U)
      (precompose F'' G''|>.obj U) (transform X|>.obj <| ψ.comp ψ')).hom ≫
      whiskerLeft (precompose F G|>.obj U) (transformObjComp X ψ ψ').hom =
    whiskerRight (transformObjComp Y ψ ψ').hom (precompose F'' G''|>.obj U) ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (transform Y|>.obj ψ)
        (CatCommSq.iso _ (precompose F' G'|>.obj U)
          _ (transform X|>.obj ψ')).hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (CatCommSq.iso _ _ _ _).hom (transform X|>.obj ψ') ≫
      (Functor.associator _ _ _).hom := by
  aesop_cat

end compatibility

end CatCommSqOver

end Bifunctoriality

end CategoricalPullback

end

end CategoryTheory.Limits
