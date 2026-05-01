/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
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

@[expose] public section

universe v u

namespace CategoryTheory

open SimplicialCategory EnrichedCategory EnrichedOrdinaryCategory MonoidalCategory

open scoped Simplicial

section SimplicialNerve

/-- A type synonym for a linear order `J`, will be equipped with a simplicial category structure. -/
@[nolint unusedArguments]
structure SimplicialThickening (J : Type*) [LinearOrder J] : Type _ where
  /-- The underlying object of the linear order. -/
  as : J

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

@[simps -isSimp]
instance (J : Type*) [LinearOrder J] : CategoryStruct (SimplicialThickening J) where
  Hom i j := Path i.as j.as
  id i := { I := {i.as} }
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

attribute [local simp] SimplicialThickening.comp_I SimplicialThickening.id_I

instance {J : Type*} [LinearOrder J] (i j : SimplicialThickening J) : Category (i ⟶ j) :=
  inferInstanceAs (Category (Path i.as j.as))

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

attribute [local ext (iff := false)] Functor.ext in
attribute [local simp] types_tensorObj_def in
@[simps -isSimp]
instance (J : Type*) [LinearOrder J] :
    SimplicialCategory (SimplicialThickening J) where
  Hom i j := nerve (i ⟶ j)
  id _ := ⟨fun _ ↦ ↾fun _ ↦ (Functor.const _).obj (𝟙 _), fun _ _ _ ↦ by simp; rfl⟩
  comp i j k := ⟨fun _ ↦ ↾fun x ↦ x.1.prod' x.2 ⋙ compFunctor i j k,
    fun _ _ _ ↦ by simp; rfl⟩
  homEquiv {i j} := nerveEquiv.symm.trans (SSet.unitHomEquiv (nerve (i ⟶ j))).symm

attribute [local simp] SimplicialThickening.Hom_def

/-- Auxiliary definition for `SimplicialThickening.functor` -/
abbrev functorMap {J K : Type u} [LinearOrder J] [LinearOrder K]
    (f : J →o K) (i j : SimplicialThickening J) :
      (i ⟶ j) ⥤ ((SimplicialThickening.mk <| f i.as) ⟶ (SimplicialThickening.mk <| f j.as)) where
  obj I := ⟨f '' I.I, Set.mem_image_of_mem f I.left, Set.mem_image_of_mem f I.right,
    by rintro _ ⟨k, hk, rfl⟩; exact f.monotone (I.left_le k hk),
    by rintro _ ⟨k, hk, rfl⟩; exact f.monotone (I.le_right k hk)⟩
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

@[deprecated "No replacement, was using a bad instance" (since := "01-12-2026")]
alias orderHom := functorMap

attribute [local simp] nerveMap_app

attribute [local simp] types_tensorObj_def in
/--
The simplicial thickening defines a functor from the category of linear orders to the category of
simplicial categories
-/
@[simps]
def functor {J K : Type u} [LinearOrder J] [LinearOrder K]
    (f : J →o K) : EnrichedFunctor SSet (SimplicialThickening J) (SimplicialThickening K) where
  obj x := .mk (f x.as)
  map i j := nerveMap ((functorMap f i j))
  map_id i := by
    ext
    simp only [eId, EnrichedCategory.id]
    exact Functor.ext (by cat_disch)
  map_comp i j k := by
    ext
    simp only [eComp, EnrichedCategory.comp]
    exact Functor.ext (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
lemma functor_id (J : Type u) [LinearOrder J] :
    (functor (OrderHom.id (α := J))) = EnrichedFunctor.id _ _ := by
  refine EnrichedFunctor.ext _ (fun _ ↦ rfl) fun i j ↦ ?_
  ext
  exact Functor.ext (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
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
def SimplicialNerve (C : Type u) [Category.{v} C] [SimplicialCategory C] :
    SSet.{max u v} where
  obj n := EnrichedFunctor SSet (SimplicialThickening (ULift (Fin (n.unop.len + 1)))) C
  map f := ↾((SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp
    (E := C) SSet)
  map_id i := by
    ext
    change EnrichedFunctor.comp SSet (SimplicialThickening.functor OrderHom.id) _ = _
    rw [SimplicialThickening.functor_id]
    rfl
  map_comp f g := by
    ext
    change EnrichedFunctor.comp SSet (SimplicialThickening.functor
      (f.unop.toOrderHom.uliftMap.comp g.unop.toOrderHom.uliftMap)) _ = _
    rw [SimplicialThickening.functor_comp]
    rfl

end SimplicialNerve

end CategoryTheory
