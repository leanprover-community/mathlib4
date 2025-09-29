/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.CatCommSq

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
* 2-functoriality of the construction with respect to "transformation of categorical
  cospans".
* Full equivalence-invariance of the notion (follows from suitable 2-functoriality).
* Define a `CatPullbackSquare` typeclass extending `CatCommSq`that encodes the
  fact that a given `CatCommSq` defines an equivalence between the top left
  corner and the categorical pullback of its legs.
* Define a `IsCatPullbackSquare` propclass.
* Define the "categorical fiber" of a functor at an object of the target category.
* Pasting calculus for categorical pullback squares.
* Categorical pullback squares attached to Grothendieck constructions of pseudofunctors.
* Stability of (co)fibered categories under categorical pullbacks.

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Limits

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
  isomorphisms -/
  w : F.map fst ≫ y.iso.hom = x.iso.hom ≫ G.map snd := by cat_disch

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
    (w : F.map eₗ.hom ≫ y.iso.hom = x.iso.hom ≫ G.map eᵣ.hom := by cat_disch) :
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
  mpr | ⟨h₁, h₂⟩ => ⟨⟨inv f.fst, inv f.snd, by cat_disch⟩, by cat_disch⟩

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

variable (F G)

/-- The "first projection" of a CatCommSqOver as a functor. -/
abbrev fstFunctor : CatCommSqOver F G X ⥤ X ⥤ A := π₁ _ _

/-- The "second projection" of a CatCommSqOver as a functor. -/
abbrev sndFunctor : CatCommSqOver F G X ⥤ X ⥤ C := π₂ _ _

/-- The structure isomorphism of a `CatCommSqOver` as a natural transformation. -/
abbrev e :
    fstFunctor F G X ⋙ (whiskeringRight X A B).obj F ≅
    sndFunctor F G X ⋙ (whiskeringRight X C B).obj G :=
  NatIso.ofComponents (fun S ↦ S.iso)

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
of categories between functors `X ⥤ (F ⊡ G)` and categorical commutative squares
over X. -/
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

variable {F G X}

/-- A constructor for natural isomorphisms of functors `X ⥤ CategoricalPullback`: to
construct such an isomorphism, it suffices to produce isomorphisms after whiskering with
the projections, and compatible with the canonical 2-commutative square . -/
@[simps!]
def mkNatIso {J K : X ⥤ F ⊡ G}
    (e₁ : J ⋙ π₁ F G ≅ K ⋙ π₁ F G) (e₂ : J ⋙ π₂ F G ≅ K ⋙ π₂ F G)
    (coh :
      whiskerRight e₁.hom F ≫ (associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv =
      (associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight e₂.hom G := by cat_disch) :
    J ≅ K :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso (e₁.app x) (e₂.app x)
      (by simpa using NatTrans.congr_app coh x))
    (fun {_ _} f ↦ by
      ext
      · exact e₁.hom.naturality f
      · exact e₂.hom.naturality f)

/-- To check equality of two natural transformations of functors to a `CategoricalPullback`, it
suffices to do so after whiskering with the projections. -/
@[ext]
lemma natTrans_ext
    {J K : X ⥤ F ⊡ G} {α β : J ⟶ K}
    (e₁ : whiskerRight α (π₁ F G) = whiskerRight β (π₁ F G))
    (e₂ : whiskerRight α (π₂ F G) = whiskerRight β (π₂ F G)) :
    α = β := by
  ext x
  · exact congrArg (fun t ↦ t.app x) e₁
  · exact congrArg (fun t ↦ t.app x) e₂

section

variable {J K : X ⥤ F ⊡ G}
    (e₁ : J ⋙ π₁ F G ≅ K ⋙ π₁ F G) (e₂ : J ⋙ π₂ F G ≅ K ⋙ π₂ F G)
    (coh :
      whiskerRight e₁.hom F ≫ (associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv =
      (associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight e₂.hom G := by cat_disch)

@[simp]
lemma toCatCommSqOver_mapIso_mkNatIso_eq_mkIso :
    (toCatCommSqOver F G X).mapIso (mkNatIso e₁ e₂ coh) =
    CategoricalPullback.mkIso e₁ e₂
      (by simpa [functorEquiv, toCatCommSqOver] using coh) := by
  aesop

/-- Comparing mkNatIso with the corresponding construction one can deduce from
`functorEquiv`. -/
lemma mkNatIso_eq :
    mkNatIso e₁ e₂ coh =
    (functorEquiv F G X).fullyFaithfulFunctor.preimageIso
      (CategoricalPullback.mkIso e₁ e₂
        (by simpa [functorEquiv, toCatCommSqOver] using coh)) := by
  rw [← toCatCommSqOver_mapIso_mkNatIso_eq_mkIso e₁ e₂ coh]
  dsimp [Equivalence.fullyFaithfulFunctor]
  cat_disch

end

end functorEquiv

end

end CategoricalPullback

end

end CategoryTheory.Limits
