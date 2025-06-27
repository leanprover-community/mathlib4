/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.CatCommSq

/-! # Categorical pullback squares

This file defines the basic properties of categorical pullback squares.

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
* `πₗ F G : CategoricalPullback F G` and `πᵣ F G : CategoricalPullback F G`: the canonical
  projections.
* `CategoricalPullback.catCommSq`: the canonical `CatCommSq (πₗ F G) (πᵣ F G) F G` which exhibits
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
  /-- the left element -/
  left : A
  /-- the right element -/
  right : C
  /-- the structural isomorphism `F.obj left ≅ G.obj right` -/
  iso : F.obj left ≅ G.obj right

namespace CategoricalPullback

/-- A notation for the categorical pullback. -/
scoped notation:max L:max " ⊡ " R:max => CategoricalPullback L R

variable {F G}

/-- The Hom types for the categorical pullback are given by pairs of maps compatible with the
structural isomorphisms. -/
@[ext]
structure Hom (x y : F ⊡ G) where
  /-- the left component of `f : Hom x y` is a morphism `x.left ⟶ y.left` -/
  left : x.left ⟶ y.left
  /-- the right component of `f : Hom x y` is a morphism `x.right ⟶ y.right` -/
  right : x.right ⟶ y.right
  /-- the compatibility condition on `left` and `right` with respect to the structure
  isompophisms -/
  w : F.map left ≫ y.iso.hom = x.iso.hom ≫ G.map right := by aesop_cat

attribute [reassoc (attr := simp)] Hom.w

@[simps! id_left id_right comp_left comp_right]
instance : Category (CategoricalPullback F G) where
  Hom x y := CategoricalPullback.Hom x y
  id x :=
    { left := 𝟙 x.left
      right := 𝟙 x.right }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }

attribute [reassoc] comp_left comp_right

/-- Naturality square for morphisms in the inverse direction. -/
@[reassoc (attr := simp)]
lemma Hom.w' {x y : F ⊡ G} (f : x ⟶ y) :
    G.map f.right ≫ y.iso.inv = x.iso.inv ≫ F.map f.left := by
  rw [Iso.comp_inv_eq, Category.assoc, Eq.comm, Iso.inv_comp_eq, f.w]

/-- Extensionnality principle for morphisms in `CategoricalPullback F G`. -/
@[ext]
theorem hom_ext {x y : F ⊡ G} {f g : x ⟶ y}
    (hₗ : f.left = g.left) (hᵣ : f.right = g.right) : f = g := by
  apply Hom.ext <;> assumption

section

variable (F G)

/-- `CategoricalPullback.πₗ F G` is the left projection `CategoricalPullback F G ⥤ A`. -/
@[simps]
def πₗ : F ⊡ G ⥤ A where
  obj x := x.left
  map f := f.left

/-- `CategoricalPullback.πᵣ F G` is the right projection `CategoricalPullback F G ⥤ C`. -/
@[simps]
def πᵣ : F ⊡ G ⥤ C where
  obj x := x.right
  map f := f.right

/-- The canonical categorical commutative square in which `CategoricalPullback F G` sits. -/
instance catCommSq : CatCommSq (πₗ F G) (πᵣ F G) F G where
  iso' := NatIso.ofComponents (fun x ↦ x.iso)

@[simp]
lemma catCommSq_iso_hom_app (x : F ⊡ G) :
    (CatCommSq.iso (πₗ F G) (πᵣ F G) F G).hom.app x = x.iso.hom := rfl

@[simp]
lemma catCommSq_iso_inv_app (x : F ⊡ G) :
    (CatCommSq.iso (πₗ F G) (πᵣ F G) F G).inv.app x = x.iso.inv := rfl

variable {F G} in
/-- Constructor for isomorphisms in `CategoricalPullback F G`. -/
@[simps!]
def mkIso {x y : F ⊡ G}
    (eₗ : x.left ≅ y.left) (eᵣ : x.right ≅ y.right)
    (w : F.map eₗ.hom ≫ y.iso.hom = x.iso.hom ≫ G.map eᵣ.hom := by aesop_cat) :
    x ≅ y where
  hom := ⟨eₗ.hom, eᵣ.hom, w⟩
  inv := ⟨eₗ.inv, eᵣ.inv, by simpa using F.map eₗ.inv ≫= w.symm =≫ G.map eᵣ.inv⟩

instance {x y : F ⊡ G} (f : x ⟶ y) [IsIso f] : IsIso f.left :=
  inferInstanceAs (IsIso ((πₗ _ _).mapIso (asIso f)).hom)

instance {x y : F ⊡ G} (f : x ⟶ y) [IsIso f] : IsIso f.right :=
  inferInstanceAs (IsIso ((πᵣ _ _).mapIso (asIso f)).hom)

end

section

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
@[simps!]
def asSquare (S : CatCommSqOver F G X) : CatCommSq S.left S.right F G where
  iso' := S.iso

@[reassoc (attr := simp)]
lemma iso_hom_naturality (S : CatCommSqOver F G X) {x x' : X} (f : x ⟶ x') :
   F.map (S.left.map f) ≫ S.iso.hom.app x' =
   S.iso.hom.app x ≫ G.map (S.right.map f) :=
  S.iso.hom.naturality f

@[reassoc (attr := simp)]
lemma w_app {S S' : CatCommSqOver F G X} (φ : S ⟶ S') (x : X) :
    F.map (φ.left.app x) ≫ S'.iso.hom.app x =
    S.iso.hom.app x ≫ G.map (φ.right.app x) :=
  NatTrans.congr_app φ.w x

variable (F G)

/-- The "left projection" of a CatCommSqOver as a functor. -/
abbrev L : CatCommSqOver F G X ⥤ X ⥤ A := πₗ _ _

/-- The "right projection" of a CatCommSqOver as a functor. -/
abbrev R : CatCommSqOver F G X ⥤ X ⥤ C := πᵣ _ _

/-- The structure isompophism of a `CatCommSqOver` as a natural transformation. -/
abbrev e :
    (L F G X) ⋙ (whiskeringRight X A B|>.obj F) ≅
    (R F G X) ⋙ (whiskeringRight X C B|>.obj G) :=
  NatIso.ofComponents
    (fun S ↦ S.iso)

end CatCommSqOver

section functorEquiv

variable (F G)

-- We need to split up the definition of `functorEquiv` to avoid timeouts.

/-- Interpret a functor to the categorical pullback as a `CatCommSqOver`. -/
@[simps!]
def toCatCommSqOver : (X ⥤ F ⊡ G) ⥤ CatCommSqOver F G X where
  obj J :=
    { left := J ⋙ πₗ F G
      right := J ⋙ πᵣ F G
      iso :=
        Functor.associator _ _ _ ≪≫
          isoWhiskerLeft J (catCommSq F G).iso ≪≫
          (Functor.associator _ _ _).symm }
  map {J J'} F :=
    { left := whiskerRight F (πₗ _ _)
      right := whiskerRight F (πᵣ _ _) }

/-- Interpret a `CatCommSqOver` as a functor to the categorical pullback. -/
@[simps!]
def CatCommSqOver.toFunctorToCategoricalPullback :
    (CatCommSqOver F G X) ⥤ X ⥤ F ⊡ G where
  obj S :=
    { obj x :=
        { left := S.left.obj x
          right := S.right.obj x
          iso := S.iso.app x }
      map {x y} f :=
        { left := S.left.map f
          right := S.right.map f } }
  map {S S'} φ :=
    { app x :=
        { left := φ.left.app x
          right := φ.right.app x } }

/-- The unit of `CategoricalPullback.functorEquiv`. -/
@[simps!]
def functorEquivUnitIso :
    𝟭 (X ⥤ F ⊡ G) ≅
    toCatCommSqOver F G X ⋙ CatCommSqOver.toFunctorToCategoricalPullback F G X :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents
      (fun _ ↦ CategoricalPullback.mkIso (.refl _) (.refl _)))

/-- The counit of `CategoricalPullback.functorEquiv`. -/
@[simps!]
def functorEquivCounitIso :
    CatCommSqOver.toFunctorToCategoricalPullback F G X ⋙ toCatCommSqOver F G X ≅
    𝟭 (CatCommSqOver F G X) :=
  NatIso.ofComponents
    (fun _ ↦ CategoricalPullback.mkIso
      (NatIso.ofComponents (fun _ ↦ .refl _)) (NatIso.ofComponents (fun _ ↦ .refl _)))

/-- The universal property of categorical pullbacks, stated as an equivalence
of categories between functors `X ⥤ (F ⊡ G)` and categorical commutative squares
over X. -/
@[simps!]
def functorEquiv : (X ⥤ F ⊡ G) ≌ CatCommSqOver F G X where
  functor := toCatCommSqOver F G X
  inverse := CatCommSqOver.toFunctorToCategoricalPullback F G X
  unitIso := functorEquivUnitIso F G X
  counitIso := functorEquivCounitIso F G X

variable {F G X}

/-- A constructor for natural isomorphisms of functors `X ⥤ CategoricalPullback`: to
construct such an isomorphism, it suffices to produce isomorphisms after whiskering with
the projections, and compatible with the canonical 2-commutative square . -/
@[simps!]
def mkNatIso {J K : X ⥤ F ⊡ G}
    (e₁ : J ⋙ πₗ F G ≅ K ⋙ πₗ F G) (e₂ : J ⋙ πᵣ F G ≅ K ⋙ πᵣ F G)
    (coh :
      whiskerRight e₁.hom F ≫ (Functor.associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso (πₗ F G) (πᵣ F G) F G).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso (πₗ F G) (πᵣ F G) F G).hom ≫
        (Functor.associator _ _ _).inv ≫
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
    (e₁ : whiskerRight α (πₗ F G) = whiskerRight β (πₗ F G))
    (e₂ : whiskerRight α (πᵣ F G) = whiskerRight β (πᵣ F G)) :
    α = β := by
  ext x
  · exact congrArg (fun t ↦ t.app x) e₁
  · exact congrArg (fun t ↦ t.app x) e₂

/-- Comparing mkNatIso with the corresponding construction one can deduce from
`functorEquiv`. -/
lemma mkNatIso_eq {J K : X ⥤ F ⊡ G}
    (e₁ : J ⋙ πₗ F G ≅ K ⋙ πₗ F G) (e₂ : J ⋙ πᵣ F G ≅ K ⋙ πᵣ F G)
    (coh :
      whiskerRight e₁.hom F ≫ (Functor.associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso (πₗ F G) (πᵣ F G) F G).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso (πₗ F G) (πᵣ F G) F G).hom ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight e₂.hom G := by aesop_cat) :
  mkNatIso e₁ e₂ coh =
    (functorEquiv F G X).fullyFaithfulFunctor.preimageIso
      (CategoricalPullback.mkIso e₁ e₂
        (by simpa [functorEquiv, toCatCommSqOver] using coh)) := by
  ext
  · simp [Equivalence.fullyFaithfulFunctor]
  · simp [Equivalence.fullyFaithfulFunctor]

end functorEquiv

end

end CategoricalPullback

end

end CategoryTheory.Limits
