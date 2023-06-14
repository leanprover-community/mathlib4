/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.comma
! leanprover-community/mathlib commit 8a318021995877a44630c898d0b2bc376fceef3b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

/-!
# Comma categories

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`Comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `Comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

```
L.obj left   ⟶   L.obj left'
      |               |
  hom |               | hom'
      ↓               ↓
R.obj right  ⟶   R.obj right',
```

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

## Main definitions

* `Comma L R`: the comma category of the functors `L` and `R`.
* `Over X`: the over category of the object `X` (developed in `Over.lean`).
* `Under X`: the under category of the object `X` (also developed in `Over.lean`).
* `Arrow T`: the arrow category of the category `T` (developed in `Arrow.lean`).

## References

* <https://ncatlab.org/nlab/show/comma+category>

## Tags

comma, slice, coslice, over, under, arrow
-/


namespace CategoryTheory

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

/-- The objects of the comma category are triples of an object `left : A`, an object
   `right : B` and a morphism `hom : L.obj left ⟶ R.obj right`.  -/
structure Comma (L : A ⥤ T) (R : B ⥤ T) : Type max u₁ u₂ v₃ where
  left : A
  right : B
  hom : L.obj left ⟶ R.obj right
#align category_theory.comma CategoryTheory.Comma

-- Satisfying the inhabited linter
instance Comma.inhabited [Inhabited T] : Inhabited (Comma (𝟭 T) (𝟭 T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 default }
#align category_theory.comma.inhabited CategoryTheory.Comma.inhabited

variable {L : A ⥤ T} {R : B ⥤ T}

/-- A morphism between two objects in the comma category is a commutative square connecting the
    morphisms coming from the two objects using morphisms in the image of the functors `L` and `R`.
-/
@[ext]
structure CommaMorphism (X Y : Comma L R) where
  left : X.left ⟶ Y.left
  right : X.right ⟶ Y.right
  w : L.map left ≫ Y.hom = X.hom ≫ R.map right := by aesop_cat
#align category_theory.comma_morphism CategoryTheory.CommaMorphism

-- Satisfying the inhabited linter
instance CommaMorphism.inhabited [Inhabited (Comma L R)] :
    Inhabited (CommaMorphism (default : Comma L R) default) :=
    ⟨{ left := 𝟙 _, right := 𝟙 _}⟩
#align category_theory.comma_morphism.inhabited CategoryTheory.CommaMorphism.inhabited

attribute [reassoc (attr := simp)] CommaMorphism.w

instance commaCategory : Category (Comma L R) where
  Hom X Y := CommaMorphism X Y
  id X :=
    { left := 𝟙 X.left
      right := 𝟙 X.right }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }
#align category_theory.comma_category CategoryTheory.commaCategory

namespace Comma

section

variable {X Y Z : Comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}

-- porting note: this lemma was added because `CommaMorphism.ext`
-- was not triggered automatically
@[ext]
lemma hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) : f = g :=
  CommaMorphism.ext _ _ h₁ h₂

@[simp]
theorem id_left : (𝟙 X : CommaMorphism X X).left = 𝟙 X.left :=
  rfl
#align category_theory.comma.id_left CategoryTheory.Comma.id_left

@[simp]
theorem id_right : (𝟙 X : CommaMorphism X X).right = 𝟙 X.right :=
  rfl
#align category_theory.comma.id_right CategoryTheory.Comma.id_right

@[simp]
theorem comp_left : (f ≫ g).left = f.left ≫ g.left :=
  rfl
#align category_theory.comma.comp_left CategoryTheory.Comma.comp_left

@[simp]
theorem comp_right : (f ≫ g).right = f.right ≫ g.right :=
  rfl
#align category_theory.comma.comp_right CategoryTheory.Comma.comp_right

end

variable (L) (R)

/-- The functor sending an object `X` in the comma category to `X.left`. -/
@[simps]
def fst : Comma L R ⥤ A where
  obj X := X.left
  map f := f.left
#align category_theory.comma.fst CategoryTheory.Comma.fst

/-- The functor sending an object `X` in the comma category to `X.right`. -/
@[simps]
def snd : Comma L R ⥤ B where
  obj X := X.right
  map f := f.right
#align category_theory.comma.snd CategoryTheory.Comma.snd

/-- We can interpret the commutative square constituting a morphism in the comma category as a
    natural transformation between the functors `fst ⋙ L` and `snd ⋙ R` from the comma category
    to `T`, where the components are given by the morphism that constitutes an object of the comma
    category. -/
@[simps]
def natTrans : fst L R ⋙ L ⟶ snd L R ⋙ R where app X := X.hom
#align category_theory.comma.nat_trans CategoryTheory.Comma.natTrans

@[simp]
theorem eqToHom_left (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.left (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl
#align category_theory.comma.eq_to_hom_left CategoryTheory.Comma.eqToHom_left

@[simp]
theorem eqToHom_right (X Y : Comma L R) (H : X = Y) : CommaMorphism.right (eqToHom H) = eqToHom (by
    cases H
    rfl) := by
  cases H
  rfl
#align category_theory.comma.eq_to_hom_right CategoryTheory.Comma.eqToHom_right

section

variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

/-- Construct an isomorphism in the comma category given isomorphisms of the objects whose forward
directions give a commutative square.
-/
@[simps]
def isoMk {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
    (h : L₁.map l.hom ≫ Y.hom = X.hom ≫ R₁.map r.hom := by aesop_cat) : X ≅ Y where
  hom :=
    { left := l.hom
      right := r.hom
      w := h }
  inv :=
    { left := l.inv
      right := r.inv
      w := by
        rw [← L₁.mapIso_inv l, Iso.inv_comp_eq, L₁.mapIso_hom, ← Category.assoc, h,
          Category.assoc, ← R₁.map_comp]
        simp }
#align category_theory.comma.iso_mk CategoryTheory.Comma.isoMk

/-- A natural transformation `L₁ ⟶ L₂` induces a functor `Comma L₂ R ⥤ Comma L₁ R`. -/
@[simps]
def mapLeft (l : L₁ ⟶ L₂) : Comma L₂ R ⥤ Comma L₁ R where
  obj X :=
    { left := X.left
      right := X.right
      hom := l.app X.left ≫ X.hom }
  map f :=
    { left := f.left
      right := f.right }
#align category_theory.comma.map_left CategoryTheory.Comma.mapLeft

/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `L` is
    naturally isomorphic to the identity functor. -/
@[simps]
def mapLeftId : mapLeft R (𝟙 L) ≅ 𝟭 _ where
  hom :=
    { app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
  inv :=
    { app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
#align category_theory.comma.map_left_id CategoryTheory.Comma.mapLeftId

/-- The functor `Comma L₁ R ⥤ Comma L₃ R` induced by the composition of two natural transformations
    `l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the two functors
    induced by these natural transformations. -/
@[simps]
def mapLeftComp (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) :
    mapLeft R (l ≫ l') ≅ mapLeft R l' ⋙ mapLeft R l where
  hom :=
    { app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
  inv :=
    { app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
#align category_theory.comma.map_left_comp CategoryTheory.Comma.mapLeftComp

/-- A natural transformation `R₁ ⟶ R₂` induces a functor `Comma L R₁ ⥤ Comma L R₂`. -/
@[simps]
def mapRight (r : R₁ ⟶ R₂) : Comma L R₁ ⥤ Comma L R₂ where
  obj X :=
    { left := X.left
      right := X.right
      hom := X.hom ≫ r.app X.right }
  map f :=
    { left := f.left
      right := f.right }
#align category_theory.comma.map_right CategoryTheory.Comma.mapRight

/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `R` is
    naturally isomorphic to the identity functor. -/
@[simps]
def mapRightId : mapRight L (𝟙 R) ≅ 𝟭 _ where
  hom :=
    { app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
  inv :=
    { app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
#align category_theory.comma.map_right_id CategoryTheory.Comma.mapRightId

/-- The functor `Comma L R₁ ⥤ Comma L R₃` induced by the composition of the natural transformations
    `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
    induced by these natural transformations. -/
@[simps]
def mapRightComp (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃) :
    mapRight L (r ≫ r') ≅ mapRight L r ⋙ mapRight L r' where
  hom :=
    { app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
  inv :=
    { app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
#align category_theory.comma.map_right_comp CategoryTheory.Comma.mapRightComp

end

section

variable {C : Type u₄} [Category.{v₄} C] {D : Type u₅} [Category.{v₅} D]

/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[simps]
def preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : Comma (F ⋙ L) R ⥤ Comma L R where
  obj X :=
    { left := F.obj X.left
      right := X.right
      hom := X.hom }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using f.w }
#align category_theory.comma.pre_left CategoryTheory.Comma.preLeft

/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[simps]
def preRight (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) : Comma L (F ⋙ R) ⥤ Comma L R where
  obj X :=
    { left := X.left
      right := F.obj X.right
      hom := X.hom }
  map f :=
    { left := f.left
      right := F.map f.right }
#align category_theory.comma.pre_right CategoryTheory.Comma.preRight

/-- The functor `(L, R) ⥤ (L ⋙ F, R ⋙ F)` -/
@[simps]
def post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : Comma L R ⥤ Comma (L ⋙ F) (R ⋙ F) where
  obj X :=
    { left := X.left
      right := X.right
      hom := F.map X.hom }
  map f :=
    { left := f.left
      right := f.right
      w := by simp only [Functor.comp_map, ← F.map_comp, f.w] }
#align category_theory.comma.post CategoryTheory.Comma.post

end

end Comma

end CategoryTheory
