/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Inserter categories

Let `F G : C ⥤ D` be a parallel pair of functors. In this file, we define a category `Inserter F G`.
Objects of `Inserter F G` correspond to pairs `(K : C) × (F.obj K ⟶ G.obj K)`.
Such categories can be used to encode data such as algebra for endofunctors. They are also a basic
building block for bicategorical limits of categories.

## Main constructions

* `Inserter F G`: the inserter category
* `Inserter.proj`: the projection functor `Inserter F G ⥤ C`
* `Inserter.τ`: the structure morphism of the inserter as a natural transformation
  `proj F G ⋙ F ⟶ proj F G ⋙ G`.

## References

* [nLab, *inserter*](https://ncatlab.org/nlab/show/inserter).

## Future work

* Link `Inserter F (𝟭 C)` with `Endofunctor.Algebra F` when `F` is an endofunctor.
* Link `Inserter (𝟭 C) F` with `Endofunctor.Coalgebra F` when `F` is an endofunctor.
* Show that `Inserter F G` is an accessible category when `F` `G` are accessible functors.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- The *inserter* of a pair of parallel functors `F G : C ⥤ D` is the
category of arrows `F.obj K ⟶ G.obj K`, with morphisms `K ⟶ K'` making the
obvious square commute as morphims. -/
structure Inserter (F G : C ⥤ D) where
  /-- the object of `C` underlying the object -/
  {obj : C}
  /-- the morphism `F.obj obj ⟶ G.obj obj` corresponding to the object -/
  hom : F.obj obj ⟶ G.obj obj

namespace Inserter

variable {F G : C ⥤ D}

/-- Morphisms in the inserter category are given by morphisms between the underlying objects
that make the obvious square commute. -/
structure Hom (x y : Inserter F G) where
  /-- The morphism between the underlying objects. -/
  hom : x.obj ⟶ y.obj
  comm : F.map hom ≫ y.hom = x.hom ≫ G.map hom := by cat_disch

set_option mathlib.tactic.category.grind true in
attribute [local ext, local grind ext] Hom in
@[simps id_hom]
instance : Category (Inserter F G) where
  Hom := Hom
  comp {_ _ _} f g := { hom := f.hom ≫ g.hom }
  id x := { hom := 𝟙 x.obj }

@[reassoc (attr := simp, grind _=_)]
lemma comp_hom {x y z : Inserter F G} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[reassoc (attr := simp, grind _=_)]
lemma comm {x y : Inserter F G} (f : x ⟶ y) :
    F.map f.hom ≫ y.hom = x.hom ≫ G.map f.hom :=
  f.comm

attribute [local ext] Hom in
@[ext, grind ext]
lemma hom_ext {x y : Inserter F G} {f g : x ⟶ y} (h : f.hom = g.hom) : f = g := Hom.ext h

variable (F G)

/-- The projection `Inserter F G ⥤ C` that sends an object to its underlying object of `C`. -/
@[implicit_reducible, simps (attr := grind =)]
def proj : Inserter F G ⥤ C where
  obj x := x.obj
  map f := f.hom

instance : Functor.Faithful (proj F G) where map_injective {X Y} := by cat_disch

/-- The structure morphisms of objects of the inserter assemble into a natural transformation
`proj ⋙ F ⟶ proj ⋙ G`. -/
@[simps!]
def τ : proj F G ⋙ F ⟶ proj F G ⋙ G where app x := x.hom

variable {F G} in
/-- Construct an isomorphism of inserters from an isomorphism of the underlying objects -/
@[simps!]
def mkIso {E E' : Inserter F G} (e : E.obj ≅ E'.obj)
    (he : F.map e.hom ≫ E'.hom = E.hom ≫ G.map e.hom := by cat_disch) : E ≅ E' where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, by simpa using F.map e.inv ≫= he.symm =≫ G.map e.inv⟩

instance {E E' : Inserter F G} (f : E ⟶ E') [IsIso f] : IsIso f.hom :=
  (proj F G).map_isIso f

@[simp, push ←]
lemma inv_hom {E E' : Inserter F G} (f : E ⟶ E') [IsIso f] :
    (inv f).hom = inv f.hom := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← comp_hom]

instance : (proj F G).ReflectsIsomorphisms where
  reflects k h := by
    dsimp at h
    exact (inferInstance : IsIso (mkIso (asIso k.hom) (by simp)|>.hom))

lemma isIso_iff {E E' : Inserter F G} (f : E ⟶ E') :
    IsIso f ↔ IsIso f.hom :=
  (isIso_iff_of_reflects_iso f (proj F G)).symm

end Inserter

end CategoryTheory

