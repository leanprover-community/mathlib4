/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
/-!

# The simplicial nerve of a simplicial category

This file defines the simplicial nerve (sometimes called homotopy coherent nerve) of a simplicial
category.

We define the *simplicial thickening* of a linear order `J` as the simplicial category whose hom
objects `i ⟶ j` are given by the nerve of the poset of "paths" from `i` to `j` in `J`. This is the
poset of subsets of the interval `[i, j]` in `J`, containing the endpoints.

The simplicial nerve of a simplicial category `C` is then defined as the simplicial set whose
`n`-simplices are given by the set of simplicial functors from the simplicial thickening of
the linear order `Fin (n + 1)` to `C`, in other words
`SimplicialNerve C _⦋n⦌ := EnrichedFunctor SSet (SimplicialThickening (Fin (n + 1))) C`.

## Projects

* Prove that the 0-simplices of `SimplicialNerve C` may be identified with the objects of `C`
* Prove that the 1-simplices of `SimplicialNerve C` may be identified with the morphisms of `C`
* Prove that the simplicial nerve of a simplicial category `C`, such that `sHom X Y` is a Kan
  complex for every pair of objects `X Y : C`, is a quasicategory.
* Define the quasicategory of anima as the simplicial nerve of the simplicial category of
  Kan complexes.
* Define the functor from topological spaces to anima.

## References
* [Jacob Lurie, *Higher Topos Theory*, Section 1.1.5][LurieHTT]
-/

universe v u

namespace CategoryTheory

open SimplicialCategory EnrichedCategory EnrichedOrdinaryCategory MonoidalCategory

open scoped Simplicial

section SimplicialNerve

/-- A type synonym for a linear order `J`, will be equipped with a simplicial category structure. -/
@[nolint unusedArguments]
def SimplicialThickening (J : Type*) [LinearOrder J] : Type _ := J

instance (J : Type*) [LinearOrder J] : LinearOrder (SimplicialThickening J) :=
  inferInstanceAs (LinearOrder J)

namespace SimplicialThickening

/--
A path from `i` to `j` in a linear order `J` is a subset of the interval `[i, j]` in `J` containing
the endpoints.
-/
@[ext]
structure Path {J : Type*} [LinearOrder J] (i j : J) where
  /-- The underlying subset -/
  I : Set J
  left : i ∈ I := by simp
  right : j ∈ I := by simp
  left_le (k : J) (_ : k ∈ I) : i ≤ k := by simp
  le_right (k : J) (_ : k ∈ I) : k ≤ j := by simp

lemma Path.le {J : Type*} [LinearOrder J] {i j : J} (f : Path i j) : i ≤ j :=
  f.left_le _ f.right

instance {J : Type*} [LinearOrder J] (i j : J) : Category (Path i j) :=
  inferInstanceAs (Category (InducedCategory _ (fun f : Path i j ↦ f.I)))

@[simps]
instance (J : Type*) [LinearOrder J] : CategoryStruct (SimplicialThickening J) where
  Hom i j := Path i j
  id i := { I := {i} }
  comp {i j k} f g := {
    I := f.I ∪ g.I
    left := Or.inl f.left
    right := Or.inr g.right
    left_le l := by
      rintro (h | h)
      exacts [(f.left_le l h), (Path.le f).trans (g.left_le l h)]
    le_right l := by
      rintro (h | h)
      exacts [(f.le_right _ h).trans (Path.le g), (g.le_right l h)] }

instance {J : Type*} [LinearOrder J] (i j : SimplicialThickening J) : Category (i ⟶ j) :=
  inferInstanceAs (Category (Path _ _))

@[ext]
lemma hom_ext {J : Type*} [LinearOrder J]
    (i j : SimplicialThickening J) (x y : i ⟶ j) (h : ∀ t, t ∈ x.I ↔ t ∈ y.I) : x = y := by
  apply Path.ext
  ext
  apply h

instance (J : Type*) [LinearOrder J] : Category (SimplicialThickening J) where
  id_comp f := by ext; simpa using fun h ↦ h ▸ f.left
  comp_id f := by ext; simpa using fun h ↦ h ▸ f.right

/--
Composition of morphisms in `SimplicialThickening J`, as a functor `(i ⟶ j) × (j ⟶ k) ⥤ (i ⟶ k)`
-/
@[simps]
def compFunctor {J : Type*} [LinearOrder J]
    (i j k : SimplicialThickening J) : (i ⟶ j) × (j ⟶ k) ⥤ (i ⟶ k) where
  obj x := x.1 ≫ x.2
  map f := ⟨⟨⟨Set.union_subset_union f.1.1.1.1 f.2.1.1.1⟩⟩⟩

namespace SimplicialCategory

variable {J : Type*} [LinearOrder J]

/-- The hom simplicial set of the simplicial category structure on `SimplicialThickening J` -/
abbrev Hom (i j : SimplicialThickening J) : SSet := (nerve (i ⟶ j))

/-- The identity of the simplicial category structure on `SimplicialThickening J` -/
abbrev id (i : SimplicialThickening J) : 𝟙_ SSet ⟶ Hom i i :=
  ⟨fun _ _ ↦ (Functor.const _).obj (𝟙 _), fun _ _ _ ↦ by simp; rfl⟩

/-- The composition of the simplicial category structure on `SimplicialThickening J` -/
abbrev comp (i j k : SimplicialThickening J) : Hom i j ⊗ Hom j k ⟶ Hom i k :=
  ⟨fun _ x ↦ x.1.prod' x.2 ⋙ compFunctor i j k, fun _ _ _ ↦ by simp; rfl⟩

attribute [local ext (iff := false)] Functor.ext

@[simp]
lemma id_comp (i j : SimplicialThickening J) :
    (λ_ (Hom i j)).inv ≫ id i ▷ Hom i j ≫ comp i i j = 𝟙 (Hom i j) := by
  cat_disch

@[simp]
lemma comp_id (i j : SimplicialThickening J) :
    (ρ_ (Hom i j)).inv ≫ Hom i j ◁ id j ≫ comp i j j = 𝟙 (Hom i j) := by
  cat_disch

@[simp]
lemma assoc (i j k l : SimplicialThickening J) :
    (α_ (Hom i j) (Hom j k) (Hom k l)).inv ≫ comp i j k ▷ Hom k l ≫ comp i k l =
      Hom i j ◁ comp j k l ≫ comp i j l := by
  cat_disch

end SimplicialCategory

open SimplicialThickening.SimplicialCategory

noncomputable instance (J : Type*) [LinearOrder J] :
    SimplicialCategory (SimplicialThickening J) where
  Hom := Hom
  id := id
  comp := comp
  homEquiv {i j} := (nerveEquiv _).symm.trans (SSet.unitHomEquiv _).symm

/-- Auxiliary definition for `SimplicialThickening.functorMap` -/
def orderHom {J K : Type*} [LinearOrder J] [LinearOrder K] (f : J →o K) :
    SimplicialThickening J →o SimplicialThickening K := f

/-- Auxiliary definition for `SimplicialThickening.functor` -/
noncomputable abbrev functorMap {J K : Type u} [LinearOrder J] [LinearOrder K]
    (f : J →o K) (i j : SimplicialThickening J) : (i ⟶ j) ⥤ ((orderHom f i) ⟶ (orderHom f j)) where
  obj I := ⟨f '' I.I, Set.mem_image_of_mem f I.left, Set.mem_image_of_mem f I.right,
    by rintro _ ⟨k, hk, rfl⟩; exact f.monotone (I.left_le k hk),
    by rintro _ ⟨k, hk, rfl⟩; exact f.monotone (I.le_right k hk)⟩
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/--
The simplicial thickening defines a functor from the category of linear orders to the category of
simplicial categories
-/
@[simps]
noncomputable def functor {J K : Type u} [LinearOrder J] [LinearOrder K]
    (f : J →o K) : EnrichedFunctor SSet (SimplicialThickening J) (SimplicialThickening K) where
  obj := f
  map i j := nerveMap ((functorMap f i j))
  map_id i := by
    ext
    simp only [eId, EnrichedCategory.id]
    exact Functor.ext (by cat_disch)
  map_comp i j k := by
    ext
    simp only [eComp, EnrichedCategory.comp]
    exact Functor.ext (by cat_disch)

lemma functor_id (J : Type u) [LinearOrder J] :
    (functor (OrderHom.id (α := J))) = EnrichedFunctor.id _ _ := by
  refine EnrichedFunctor.ext _ (fun _ ↦ rfl) fun i j ↦ ?_
  ext
  exact Functor.ext (by cat_disch)

lemma functor_comp {J K L : Type u} [LinearOrder J] [LinearOrder K]
    [LinearOrder L] (f : J →o K) (g : K →o L) :
    functor (g.comp f) =
      (functor f).comp _ (functor g) := by
  refine EnrichedFunctor.ext _ (fun _ ↦ rfl) fun i j ↦ ?_
  ext
  exact Functor.ext (by cat_disch)

end SimplicialThickening

/--
The simplicial nerve of a simplicial category `C` is defined as the simplicial set whose
`n`-simplices are given by the set of simplicial functors from the simplicial thickening of
the linear order `Fin (n + 1)` to `C`
-/
noncomputable def SimplicialNerve (C : Type u) [Category.{v} C] [SimplicialCategory C] :
    SSet.{max u v} where
  obj n := EnrichedFunctor SSet (SimplicialThickening (ULift (Fin (n.unop.len + 1)))) C
  map f := (SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp (E := C) SSet
  map_id i := by
    change EnrichedFunctor.comp SSet (SimplicialThickening.functor (OrderHom.id)) = _
    rw [SimplicialThickening.functor_id]
    rfl
  map_comp f g := by
    change EnrichedFunctor.comp SSet (SimplicialThickening.functor
      (f.unop.toOrderHom.uliftMap.comp g.unop.toOrderHom.uliftMap)) = _
    rw [SimplicialThickening.functor_comp]
    rfl

end SimplicialNerve

end CategoryTheory
