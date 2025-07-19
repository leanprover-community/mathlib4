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

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃

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
  default :=
    { fst := CategoricalPullback.π₁ F G
      snd := CategoricalPullback.π₂ F G
      iso := (catCommSq F G).iso }

-- this is a non-diamond
example : (default : CatCommSqOver F G <| F ⊡ G).asSquare = catCommSq F G := rfl

end CatCommSqOver

section functorEquiv

variable (F G)

-- We need to split up the definition of `functorEquiv` to avoid timeouts.

/-- Interpret a functor to the categorical pullback as a `CatCommSqOver`. -/
@[simps]
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
@[simps]
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

/-- The default `CatCommSqOver F G (CategoricalPullback F G)` corresponds to
the identity functor through `functorEquiv`. -/
@[simps!]
def functorEquivFunctorIdIsoDefault :
    (functorEquiv F G <| F ⊡ G).functor.obj (𝟭 _) ≅ default :=
  CategoricalPullback.mkIso (Functor.leftUnitor _) (Functor.leftUnitor _)

/-- The default `CatCommSqOver F G (CategoricalPullback F G)` corresponds to
the identity functor through `functorEquiv`. -/
@[simps!]
def functorEquivInverseDefaultIso :
    (functorEquiv F G <| F ⊡ G).inverse.obj (default) ≅ 𝟭 (F ⊡ G) :=
  .refl _

/-- The isomorphisms `functorEquivInverseDefaultIso` is the one induced
by `functorEquivFunctorIdIsoDefault` through the equivalence `functorEquiv`. -/
lemma functorEquivInverseDefaultIso_eq :
    (functorEquivInverseDefaultIso F G) =
    (functorEquiv F G <| F ⊡ G).inverse.mapIso
      (functorEquivFunctorIdIsoDefault F G).symm ≪≫
      (functorEquiv F G F ⊡ G).unitIso.symm.app _ := by
  aesop_cat

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
        whiskerRight e₂.hom G := by aesop_cat) :
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
        whiskerRight e₂.hom G := by aesop_cat)

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
  aesop_cat

end

end functorEquiv

end

section Pseudofunctoriality

namespace CatCommSqOver
open Functor

section transform

variable {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
  [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
  {F' : A' ⥤ B'} {G' : C' ⥤ B'}

/-- Transform a `CatCommSqOver F G X` by "whiskering it" with a
`CatCospanTransform`. -/
@[simps]
def transform (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F' G') :
    CatCommSqOver F G X ⥤ CatCommSqOver F' G' X where
  obj S :=
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
        simp [← Functor.map_comp_assoc] }

/-- A morphism of `CatCospanTransform` induce a natural transformation of
the functor they induce on `CatCommSqOver`. -/
@[simps]
def transform₂ (X : Type u₇) [Category.{v₇} X]
    {ψ ψ' : CatCospanTransform F G F' G'} (η : ψ ⟶ ψ') :
    transform X ψ ⟶ transform X ψ' where
  app S :=
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
        simp [this] }

section transform₂

variable (X : Type u₇) [Category.{v₇} X]

@[simp]
lemma transform₂_id (ψ : CatCospanTransform F G F' G') :
    transform₂ X (𝟙 ψ) = 𝟙 _ := by aesop_cat

@[reassoc, simp]
lemma transform₂_comp {ψ ψ' ψ'' : CatCospanTransform F G F' G'}
    (α : ψ ⟶ ψ') (β : ψ' ⟶ ψ'') :
    transform₂ X (α ≫ β) = transform₂ X α ≫ transform₂ X β := by
  aesop_cat

/-- Extend `transform₂` to isomorphisms. -/
@[simps]
def transform₂Iso {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ≅ ψ') :
    transform X ψ ≅ transform X ψ' where
  hom := transform₂ X α.hom
  inv := transform₂ X α.inv
  hom_inv_id := by simp [← transform₂_comp]
  inv_hom_id := by simp [← transform₂_comp]

end transform₂

variable {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
  [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
  {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}

/-- The construction `CatCommSqOver.transform` respects vertical composition
of `CatCospanTransform`. -/
@[simps!]
def transformComp (X : Type u₁₀) [Category.{v₁₀} X]
    (ψ : CatCospanTransform F G F' G') (ψ' : CatCospanTransform F' G' F'' G'') :
    transform X (ψ.comp ψ') ≅ (transform X ψ) ⋙ (transform X ψ') :=
  NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.associator _ _ _).symm
      (Functor.associator _ _ _).symm

/-- The construction `CatCommSqOver.transform` respects the identity
`CatCospanTransform`. -/
@[simps!]
def transformId (X : Type u₄) [Category.{v₄} X]
    (F : A ⥤ B) (G : C ⥤ B) :
    transform X (CatCospanTransform.id F G) ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.rightUnitor _)
      (Functor.rightUnitor _)

open scoped CatCospanTransform

lemma transform₂_whiskerLeft
    (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F' G')
    {φ φ' : CatCospanTransform F' G' F'' G''} (α : φ ⟶ φ') :
    transform₂ X (ψ ◁ α) =
    (transformComp X ψ φ).hom ≫
      whiskerLeft (transform X ψ) (transform₂ X α) ≫
      (transformComp X ψ φ').inv := by
  aesop_cat

lemma transform₂_whiskerRight
    (X : Type u₇) [Category.{v₇} X]
    {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ')
    (φ : CatCospanTransform F' G' F'' G'') :
    transform₂ X (α ▷ φ) =
    (transformComp X ψ φ).hom ≫
      whiskerRight (transform₂ X α) (transform X φ) ≫
      (transformComp X ψ' φ).inv := by
  aesop_cat

lemma transform₂_associator
    {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂}
    [Category.{v₁₀} A'''] [Category.{v₁₁} B'''] [Category.{v₁₂} C''']
    {F''' : A''' ⥤ B'''} {G''' : C''' ⥤ B'''}
    (X : Type u₁₃) [Category.{v₁₃} X]
    (ψ : CatCospanTransform F G F' G') (φ : CatCospanTransform F' G' F'' G'')
    (τ : CatCospanTransform F'' G'' F''' G''') :
    transform₂ X (α_ ψ φ τ).hom =
    (transformComp X (ψ.comp φ) τ).hom ≫
      whiskerRight (transformComp X ψ φ).hom (transform X τ) ≫
      ((transform X ψ).associator (transform X φ) (transform X τ)).hom ≫
      whiskerLeft (transform X ψ) (transformComp X φ τ).inv ≫
      (transformComp X ψ (φ.comp τ)).inv := by
  aesop_cat

lemma transform₂_leftUnitor (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F' G') :
    transform₂ X (λ_ ψ).hom =
    (transformComp X (.id F G) ψ).hom ≫
      whiskerRight (transformId X F G).hom (transform X ψ) ≫
      (transform X ψ).leftUnitor.hom := by
  aesop_cat

lemma transform₂_rightUnitor (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F' G') :
    transform₂ X (ρ_ ψ).hom =
    (transformComp X ψ (.id F' G')).hom ≫
      whiskerLeft  (transform X ψ) (transformId X F' G').hom ≫
      (transform X ψ).rightUnitor.hom := by
  aesop_cat

end transform

section precompose

variable (F G)

variable
    {X : Type u₄} {Y : Type u₅} {Z : Type u₆}
    [Category.{v₄} X] [Category.{v₅} Y] [Category.{v₆} Z]

/-- A functor `U : X ⥤ Y` induces a functor
`CatCommSqOver F G Y ⥤ CatCommSqOver F G X` by whiskering left the underlying
categorical commutative square by U. -/
@[simps]
def precompose (U : X ⥤ Y) : CatCommSqOver F G Y ⥤ CatCommSqOver F G X where
  obj S :=
    { fst := U ⋙ S.fst
      snd := U ⋙ S.snd
      iso :=
        (Functor.associator _ _ _) ≪≫
          isoWhiskerLeft U S.iso ≪≫
          (Functor.associator _ _ _).symm }
  map {S S'} φ :=
    { fst := whiskerLeft U φ.fst
      snd := whiskerLeft U φ.snd }

variable (X) in
/-- The construction `precompose` respects functor identities. -/
@[simps!]
def precomposeId :
    precompose F G (𝟭 X) ≅ 𝟭 (CatCommSqOver F G X) :=
  NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso (Functor.leftUnitor _) (Functor.leftUnitor _)

/-- The construction `precompose` respects functor composition. -/
@[simps!]
def precomposeComp (U : X ⥤ Y) (V : Y ⥤ Z) :
    precompose F G (U ⋙ V) ≅ precompose F G V ⋙ precompose F G U :=
  NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.associator _ _ _)
      (Functor.associator _ _ _)

/-- The construction `precompose` acts on natural transformations. -/
@[simps]
def precompose₂ {U V : X ⥤ Y} (α : U ⟶ V) :
    precompose F G U ⟶ precompose F G V where
  app x :=
    { fst := whiskerRight α x.fst
      snd := whiskerRight α x.snd }

@[simp]
lemma precompose₂_id (U : X ⥤ Y) : precompose₂ F G (𝟙 U) = 𝟙 _ := by aesop_cat

@[simp]
lemma precompose₂_comp {U V W: X ⥤ Y} (α : U ⟶ V) (β : V ⟶ W) :
    precompose₂ F G (α ≫ β) = precompose₂ F G α ≫ precompose₂ F G β := by
  aesop_cat

/-- Extend `precompose₂` to isomorphisms. -/
@[simps]
def precompose₂Iso {U V : X ⥤ Y} (α : U ≅ V) :
    precompose F G U ≅ precompose F G V where
  hom := precompose₂ F G α.hom
  inv := precompose₂ F G α.inv
  hom_inv_id := by simp [← precompose₂_comp]
  inv_hom_id := by simp [← precompose₂_comp]

lemma precompose₂_whiskerLeft (U : X ⥤ Y) {V W : Y ⥤ Z} (α : V ⟶ W) :
    precompose₂ F G (whiskerLeft U α) =
    (precomposeComp F G U V).hom ≫
      whiskerRight (precompose₂ F G α) (precompose F G U) ≫
      (precomposeComp F G U W).inv := by
  aesop_cat

lemma precompose₂_whiskerRight {U V : X ⥤ Y} (α : U ⟶ V) (W : Y ⥤ Z) :
    precompose₂ F G (whiskerRight α W) =
    (precomposeComp F G U W).hom ≫
      whiskerLeft (precompose F G W) (precompose₂ F G α) ≫
      (precomposeComp F G V W).inv := by
  aesop_cat

lemma precompose₂_associator {T : Type u₇} [Category.{v₇} T]
    (U : X ⥤ Y) (V : Y ⥤ Z) (W : Z ⥤ T) :
    precompose₂ F G (U.associator V W).hom =
    (precomposeComp F G (U ⋙ V) W).hom ≫
      whiskerLeft (precompose F G W) (precomposeComp F G U V).hom ≫
      ((precompose F G W).associator _ _).inv ≫
      whiskerRight (precomposeComp F G V W).inv (precompose F G U) ≫
      (precomposeComp F G _ _).inv := by
  aesop_cat

lemma precompose₂_leftUnitor (U : X ⥤ Y) :
    precompose₂ F G U.leftUnitor.hom =
    (precomposeComp F G (𝟭 _) U).hom ≫
      whiskerLeft (precompose F G U) (precomposeId F G X).hom ≫
      (Functor.rightUnitor _).hom := by
  aesop_cat

lemma precompose₂_rightUnitor (U : X ⥤ Y) :
    precompose₂ F G U.rightUnitor.hom =
    (precomposeComp F G U (𝟭 _)).hom ≫
      whiskerRight (precomposeId F G Y).hom (precompose F G U) ≫
      (Functor.leftUnitor _).hom := by
  aesop_cat

end precompose

section compatibility

variable {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
  [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
  {F' : A' ⥤ B'} {G' : C' ⥤ B'}

/-- The canonical compatibility square between `precompose` and `transform`.
This is a "naturality square" if we think as `transform _` as the
(app component of the) map component of a pseudofunctor from the bicategory of
categorical cospans with value in pseudofunctors
(its value on the categorical cospan `F, G` being the pseudofunctor
`precompose F G _`). -/
@[simps!]
instance precomposeTransformSquare
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (ψ : CatCospanTransform F G F' G') (U : X ⥤ Y) :
    CatCommSq
      (precompose F G U) (transform Y ψ)
      (transform X ψ) (precompose F' G' U) where
  iso := NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.associator _ _ _)
      (Functor.associator _ _ _)

-- Compare the next 3 lemmas with the components of a strong natural transform
-- of pseudofunctors

/-- The naturality square `precomposeTransformSquare` is itself natural. -/
lemma precomposeTransformSquare_iso_hom_naturality₂
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (ψ : CatCospanTransform F G F' G')
    {U V : X ⥤ Y} (α : U ⟶ V) :
    whiskerRight (precompose₂ F G α) (transform X ψ) ≫
      (CatCommSq.iso _ (transform Y ψ) _ (precompose F' G' V)).hom =
    (CatCommSq.iso _ (transform Y ψ) _ (precompose F' G' U)).hom ≫
      whiskerLeft (transform _ _) (precompose₂ F' G' α) := by
  aesop_cat

/-- The naturality square `precomposeTransformSquare` respects identities. -/
lemma precomposeTransformSquare_iso_hom_id
    (ψ : CatCospanTransform F G F' G') (X : Type u₇) [Category.{v₇} X] :
    (CatCommSq.iso (precompose F G <| 𝟭 X) (transform X ψ)
      (transform X ψ) (precompose F' G' <| 𝟭 X)).hom ≫
      whiskerLeft (transform X ψ) (precomposeId F' G' X).hom =
    whiskerRight (precomposeId F G X).hom (transform X ψ) ≫
    (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv := by
  aesop_cat

/-- The naturality square `precomposeTransformSquare` respects compositions. -/
lemma precomposeTransformSquare_iso_hom_comp
    {X : Type u₇} {Y : Type u₈} {Z : Type u₉}
    [Category.{v₇} X] [Category.{v₈} Y] [Category.{v₉} Z]
    (ψ : CatCospanTransform F G F' G')
    (U : X ⥤ Y) (V : Y ⥤ Z) :
    (CatCommSq.iso (precompose F G <| U ⋙ V) (transform Z ψ)
      (transform X ψ) (precompose F' G' <| U ⋙ V)).hom ≫
      whiskerLeft (transform Z ψ) (precomposeComp F' G' U V).hom =
    whiskerRight (precomposeComp F G U V).hom (transform X ψ) ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (precompose F G V)
        (CatCommSq.iso _ (transform _ ψ) _ _).hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (CatCommSq.iso _ _ _ _).hom
        (precompose F' G' U) ≫
      (Functor.associator _ _ _).hom := by
  aesop_cat

/-- The canonical compatibility square between `transform` and `precompose`.
This is a "naturality square" if we think as `precompose` as the
(app component of the) map component of a pseudofunctor from the opposite
bicategory of categories to pseudofunctors of categorical cospans
(its value on `X` being the pseudofunctor `transform X _`). -/
@[simps!]
instance transformPrecomposeSquare
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) (ψ : CatCospanTransform F G F' G') :
    CatCommSq
      (transform Y ψ) (precompose F G U)
      (precompose F' G' U) (transform X ψ) where
  iso := NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (Functor.associator _ _ _).symm
      (Functor.associator _ _ _).symm

-- Compare the next 3 lemmas with the components of a strong natural transform
-- of pseudofunctors

/-- The naturality square `transformPrecomposeSquare` is itself natural. -/
lemma transformPrecomposeSquare_iso_hom_naturality₂
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) {ψ ψ' : CatCospanTransform F G F' G'} (η : ψ ⟶ ψ') :
    whiskerRight (transform₂ Y η) (precompose F' G' U) ≫
      (CatCommSq.iso _ (precompose F G U) _ (transform X ψ')).hom =
    (CatCommSq.iso _ (precompose F G U) _ (transform X ψ)).hom ≫
      whiskerLeft (precompose F G U) (transform₂ X η) := by
  aesop_cat

/-- The naturality square `transformPrecomposeSquare` respects identities. -/
lemma transformPrecomposeSquare_iso_hom_id
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) (F : A ⥤ B) (G : C ⥤ B) :
    (CatCommSq.iso (transform Y (.id F G)) (precompose F G U)
      (precompose F G U) (transform X (.id F G))).hom ≫
      whiskerLeft (precompose F G U) (transformId X F G).hom =
    whiskerRight (transformId Y F G).hom (precompose F G U) ≫
      (precompose F G U).leftUnitor.hom ≫
      (precompose F G U).rightUnitor.inv := by
  aesop_cat

/-- The naturality square `transformPrecomposeSquare` respects compositions. -/
lemma transformPrecomposeSquare_iso_hom_comp
    {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
    [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
    {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}
    {X : Type u₁₀} {Y : Type u₁₁} [Category.{v₁₀} X] [Category.{v₁₁} Y]
    (U : X ⥤ Y) (ψ : CatCospanTransform F G F' G')
    (ψ' : CatCospanTransform F' G' F'' G'') :
    (CatCommSq.iso (transform Y (ψ.comp ψ')) (precompose F G U)
      (precompose F'' G'' U) (transform X (ψ.comp ψ'))).hom ≫
      whiskerLeft (precompose F G U) (transformComp X ψ ψ').hom =
    whiskerRight (transformComp Y ψ ψ').hom (precompose F'' G'' U) ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (transform Y ψ)
        (CatCommSq.iso _ (precompose F' G' U) _ (transform X ψ')).hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (CatCommSq.iso _ _ _ _).hom (transform X ψ') ≫
      (Functor.associator _ _ _).hom := by
  aesop_cat

end compatibility

end CatCommSqOver

open CatCommSqOver

-- Note that as `functorEquiv` has @[simps], it’s better in terms of confluence
-- to state the CatCommSq below in terms of `toCatCommSqOver` and
-- `toFunctorToCategoricalPullback` rather than in terms of
-- `functorEquiv _ _ _|>.functor` and `functorEquiv _ _ _|>.inverse`

/-- The equivalence `functorEquiv` identifies the functoriality
on `X` of `X ⥤ F ⊡ G` and `CatCommSqOver F G X`. -/
@[simps!]
instance whiskeringLeftToCatCommSqOverSquare
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) :
    CatCommSq
      ((Functor.whiskeringLeft X Y (F ⊡ G)).obj U)
      (toCatCommSqOver F G Y)
      (toCatCommSqOver F G X)
      (precompose F G U) where
  iso :=
    NatIso.ofComponents fun _ =>
      CategoricalPullback.mkIso
        (Functor.associator _ _ _)
        (Functor.associator _ _ _)

/-- The equivalence `functorEquiv` identifies the functoriality
on `X` of `X ⥤ F ⊡ G` and `CatCommSqOver F G X` (inverse direction). -/
@[simps!]
instance precomposeToFunctorToCategoricalPullbackSquare
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) :
    CatCommSq
      (precompose F G U)
      (toFunctorToCategoricalPullback F G Y)
      (toFunctorToCategoricalPullback F G X)
      (Functor.whiskeringLeft X Y (F ⊡ G)|>.obj U) :=
  CatCommSq.vInv _ (functorEquiv F G _) (functorEquiv F G _) _
    (whiskeringLeftToCatCommSqOverSquare _)

variable {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
  [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
  {F' : A' ⥤ B'} {G' : C' ⥤ B'}
  {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
  [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
  {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}

/-- A `CatCospanTransform` induces a functor between the categorical pullbacks. -/
@[simps!]
def functorOfTransform (ψ : CatCospanTransform F G F' G') : F ⊡ G ⥤ F' ⊡ G' :=
  functorEquiv F' G' F ⊡ G|>.inverse.obj <|
    (CatCommSqOver.transform _ ψ).obj default

/-- The canonical square that expresses that `toCatCommSqOver` maps
(postcomposition by) `functorOfTransform` to `CatCommSqOver.transform`. -/
@[simps!]
instance toCatCommSqOverWhiskeringFunctorOfTransformSquare
    (X : Type u₁₀) [Category.{v₁₀} X]
    (ψ : CatCospanTransform F G F' G') :
    CatCommSq
      (toCatCommSqOver F G X)
      (Functor.whiskeringRight X _ _|>.obj <| functorOfTransform ψ)
      (transform _ ψ)
      (toCatCommSqOver F' G' X) where
  iso := NatIso.ofComponents fun _ =>
    CategoricalPullback.mkIso
      (NatIso.ofComponents fun _ ↦ .refl _)
      (NatIso.ofComponents fun _ ↦ .refl _)

/-- The horizontal inverse of `toCatCommSqOverWhiskeringFunctorOfTransformSquare` -/
@[simps!]
instance toFunctorToCategoricalPullbackTransformSquare
    (X : Type u₁₀) [Category.{v₁₀} X]
    (ψ : CatCospanTransform F G F' G') :
    CatCommSq
      (toFunctorToCategoricalPullback F G X)
      (transform _ ψ)
      ((Functor.whiskeringRight X _ _).obj (functorOfTransform ψ))
      (toFunctorToCategoricalPullback F' G' X) :=
  CatCommSq.hInv (functorEquiv F G X) _ _ (functorEquiv F' G' X)
    (toCatCommSqOverWhiskeringFunctorOfTransformSquare X _)

@[simps!]
instance functorOfTransformFstSquare (ψ : CatCospanTransform F G F' G') :
    CatCommSq (π₁ F G) (functorOfTransform ψ) ψ.left (π₁ F' G') where
  iso := .refl _

@[simps!]
instance functorOfTransformSndSquare (ψ : CatCospanTransform F G F' G') :
    CatCommSq (π₂ F G) (functorOfTransform ψ) ψ.right (π₂ F' G') where
  iso := .refl _

/-- A morphism of `CatCospanTransform` induces a natural transformations of
the functor between the categorical pullbacks induced by its source and target. -/
@[simps!]
def functorOfTransform₂
    {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ') :
    functorOfTransform ψ ⟶ functorOfTransform ψ' :=
  functorEquiv F' G' F ⊡ G|>.inverse.map <|
    (transform₂ _ α).app default

section functorOfTransform₂

@[simp]
lemma functorOfTransform₂_id (ψ : CatCospanTransform F G F' G') :
    functorOfTransform₂ (𝟙 ψ) = 𝟙 _ := by
  aesop_cat

@[simp]
lemma functorOfTransform₂_comp {ψ ψ' ψ'' : CatCospanTransform F G F' G'}
    (α : ψ ⟶ ψ') (β : ψ' ⟶ ψ'') :
    functorOfTransform₂ (α ≫ β) =
    functorOfTransform₂ α ≫ functorOfTransform₂ β := by
  aesop_cat

/-- An isomorphism of `CatCospanTransform` induces an isomorphism of the
corresponding `functorOfTransform`. -/
@[simps]
def functorOfTransform₂Iso {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ≅ ψ') :
    functorOfTransform ψ ≅ functorOfTransform ψ' where
  hom := functorOfTransform₂ α.hom
  inv := functorOfTransform₂ α.inv
  hom_inv_id := by simp [← functorOfTransform₂_comp]
  inv_hom_id := by simp [← functorOfTransform₂_comp]

end functorOfTransform₂

variable (F G) in
/-- `functorOfTransform` repects identities up to isomorphism. -/
@[simps!]
def functorOfTransformId :
    functorOfTransform (.id F G) ≅ 𝟭 (F ⊡ G) :=
  (functorEquiv F G F ⊡ G|>.inverse.mapIso <|
    (transformId _ F G).app default) ≪≫
    (functorEquivInverseDefaultIso F G)

/-- `functorOfTransform` repects compositions up to isomorphism. -/
@[simps!]
def functorOfTransformComp
    (ψ : CatCospanTransform F G F' G') (ψ' : CatCospanTransform F' G' F'' G'') :
    functorOfTransform (ψ.comp ψ') ≅
    functorOfTransform ψ ⋙ functorOfTransform ψ' :=
  (functorEquiv F'' G'' F ⊡ G|>.inverse.mapIso <|
    (transformComp _ ψ ψ').app default) ≪≫
    (toFunctorToCategoricalPullbackTransformSquare _ ψ').iso.symm.app
      (transform (F ⊡ G) ψ|>.obj default)

section

open scoped CatCospanTransform
open Functor

lemma functorOfTransform₂_whiskerLeft
    (ψ : CatCospanTransform F G F' G')
    {φ φ' : CatCospanTransform F' G' F'' G''} (α : φ ⟶ φ') :
    functorOfTransform₂ (ψ ◁ α) =
    (functorOfTransformComp ψ φ).hom ≫
      whiskerLeft (functorOfTransform ψ) (functorOfTransform₂ α) ≫
      (functorOfTransformComp ψ φ').inv := by
  aesop_cat

lemma functorOfTransform₂_whiskerRight
    {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ')
    (φ : CatCospanTransform F' G' F'' G'') :
    functorOfTransform₂ (α ▷ φ) =
    (functorOfTransformComp ψ φ).hom ≫
      whiskerRight (functorOfTransform₂ α) (functorOfTransform φ) ≫
      (functorOfTransformComp ψ' φ).inv := by
  aesop_cat

lemma functorOfTransform₂_associator
    {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂}
    [Category.{v₁₀} A'''] [Category.{v₁₁} B'''] [Category.{v₁₂} C''']
    {F''' : A''' ⥤ B'''} {G''' : C''' ⥤ B'''}
    (ψ : CatCospanTransform F G F' G') (φ : CatCospanTransform F' G' F'' G'')
    (τ : CatCospanTransform F'' G'' F''' G''') :
    functorOfTransform₂ (α_ ψ φ τ).hom =
    (functorOfTransformComp (ψ.comp φ) τ).hom ≫
      whiskerRight (functorOfTransformComp ψ φ).hom (functorOfTransform τ) ≫
      ((functorOfTransform ψ).associator
        (functorOfTransform φ) (functorOfTransform τ)).hom ≫
      whiskerLeft (functorOfTransform ψ) (functorOfTransformComp φ τ).inv ≫
      (functorOfTransformComp ψ (φ.comp τ)).inv := by
  aesop_cat

lemma functorOfTransform₂_leftUnitor
    (ψ : CatCospanTransform F G F' G') :
    functorOfTransform₂ (λ_ ψ).hom =
    (functorOfTransformComp (.id F G) ψ).hom ≫
      whiskerRight (functorOfTransformId F G).hom (functorOfTransform ψ) ≫
      (functorOfTransform ψ).leftUnitor.hom := by
  aesop_cat

lemma functorOfTransform₂_rightUnitor
    (ψ : CatCospanTransform F G F' G') :
    functorOfTransform₂ (ρ_ ψ).hom =
    (functorOfTransformComp ψ (.id F' G')).hom ≫
      whiskerLeft  (functorOfTransform ψ) (functorOfTransformId F' G').hom ≫
      (functorOfTransform ψ).rightUnitor.hom := by
  aesop_cat

end

open Functor in

/-- Picturing the data of `ψ : CatCospanTransform F G F' G'` and
`functorOfTransform ψ` as a "categorical cube" from
`CategoricalPullback.catCommSq F G` to `CategoricalPullback.catCommSq F' G'`,
this is asserting that the cube is fully coherent, i.e that pasting the
front and right face of the cube is, up to the isomorphisms of the top and bottom
faces, the same as pasting the left and back faces. -/
lemma cube_coherence (ψ : CatCospanTransform F G F' G') :
    (catCommSq F G|>.hComp' ψ.squareLeft.flip).iso ≪≫
      isoWhiskerLeft _ ψ.squareRight.iso =
    isoWhiskerRight (functorOfTransformFstSquare ψ).iso _ ≪≫
      ((functorOfTransformSndSquare ψ).flip.hComp' (catCommSq F' G')).iso := by
  ext x
  simp [CatCommSq.flip]

end Pseudofunctoriality

end CategoricalPullback

end

end CategoryTheory.Limits
