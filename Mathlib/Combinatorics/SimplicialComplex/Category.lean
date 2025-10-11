/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.Combinatorics.SimplicialComplex.Hom
import Mathlib.CategoryTheory.Iso

/-!
# The category of simplicial complexes (with varying vertex types)

We build a category whose objects are pairs `(U, X)` with a type of vertices `U`
equipped with `[DecidableEq U]` and a simplicial complex `X : SimplicialComplex U`.
Morphisms are simplicial maps between the underlying complexes.

## Main definitions

* `SimplicialComplexCat` — objects of the category.
* `SimplicialComplexCat.Hom` — morphisms (simplicial maps).
* `Category SimplicialComplexCat` — the category instance.
* `SimplicialComplexCat.hom_ext` — extensionality for morphisms.
* `SimplicialComplexCat.Iso.isoOfEquiv` — build an iso from a vertex equivalence that
  preserves faces in both directions.

## Main lemmas

* Pointwise evaluation lemmas:
  `id_toFun`, `comp_toFun`, `id_apply`, `comp_apply`.

## Tags

simplicial complex, category, simplicial map
-/

open CategoryTheory SimplicialComplex

universe u

/-- Objects for the category of simpliclicial complexes:
a vertex type with `[DecidableEq]` and a simplicial complex on it. -/
structure SimplicialComplexCat where
  /-- The vertex type underlying the simplicial complex. -/
  U : Type u
  /-- Decidable equality on the vertex type `U`. -/
  [decU : DecidableEq U]
  /-- The simplicial complex on the vertex type `U`. -/
  X : SimplicialComplex U
attribute [instance] SimplicialComplexCat.decU

namespace SimplicialComplexCat

@[simp] lemma eta (A : SimplicialComplexCat) :
    SimplicialComplexCat.mk A.U A.X = A := by cases A; rfl

/-- Morphisms are simplicial maps between the underlying complexes. -/
abbrev Hom (A B : SimplicialComplexCat) :=
  SimplicialComplex.Hom A.X B.X

/-- Category structure on the big category. -/
instance : Category SimplicialComplexCat where
  Hom A B := Hom A B
  id A := SimplicialComplex.Hom.id A.X
  -- `f ≫ g` is `Hom.comp g f`
  comp f g := SimplicialComplex.Hom.comp g f
  id_comp := by
    intro A B f; simp
  comp_id := by
    intro A B f; simp
  assoc := by
    intro A B C D f g h; simp

/-- View a morphism as a function on vertices. -/
instance (A B : SimplicialComplexCat) :
    CoeFun (A ⟶ B) (fun _ ↦ A.U → B.U) :=
  ⟨fun φ => φ.toFun⟩

/-- Extensionality: `f g : A ⟶ B` are equal if `∀ x, f x = g x`. -/
@[ext] lemma hom_ext
  {A B : SimplicialComplexCat} {f g : A ⟶ B}
  (h : ∀ x, f x = g x) : f = g := by
  exact SimplicialComplex.Hom.ext (funext h)

/-- The identity morphism coerces to the identity function on vertices. -/
@[simp] lemma id_toFun (A : SimplicialComplexCat) :
    ((𝟙 A : A ⟶ A) : A.U → A.U) = id := rfl

/-- Composition of morphisms coerces to the usual composition of the underlying functions. -/
@[simp] lemma comp_toFun {A B C : SimplicialComplexCat}
    (f : B ⟶ C) (g : A ⟶ B) :
    ((g ≫ f : A ⟶ C) : A.U → C.U) = f.toFun ∘ g.toFun := rfl

/-- Pointwise identity. -/
@[simp] lemma id_apply (A : SimplicialComplexCat) (x : A.U) :
    ((𝟙 A : A ⟶ A) : A.U → A.U) x = x := rfl

/-- Pointwise composition. -/
@[simp] lemma comp_apply {A B C : SimplicialComplexCat}
    (f : B ⟶ C) (g : A ⟶ B) (x : A.U) :
    ((g ≫ f : A ⟶ C) : A.U → C.U) x = f (g x) := rfl

namespace Iso

variable {A B : SimplicialComplexCat}

/-- Build a categorical isomorphism from a vertex equivalence that preserves faces in both
directions. -/
def isoOfEquiv
    (e : A.U ≃ B.U)
    (h₁ : ∀ ⦃s : Finset A.U⦄, s ∈ A.X.faces → s.image e ∈ B.X.faces)
    (h₂ : ∀ ⦃t : Finset B.U⦄, t ∈ B.X.faces → t.image e.symm ∈ A.X.faces)
  : A ≅ B :=
{ hom :=
  { toFun := e
    map_faces := by intro s hs; simpa using h₁ hs },
  inv :=
  { toFun := e.symm
    map_faces := by intro t ht; simpa using h₂ ht },
  hom_inv_id := by
    ext x; simp,
  inv_hom_id := by
    ext y; simp }

@[simp] lemma isoOfEquiv_hom_toFun
  (e : A.U ≃ B.U) h₁ h₂ :
  (isoOfEquiv e h₁ h₂).hom.toFun = e := rfl

@[simp] lemma isoOfEquiv_inv_toFun
  (e : A.U ≃ B.U) h₁ h₂ :
  (isoOfEquiv e h₁ h₂).inv.toFun = e.symm := rfl

end Iso

end SimplicialComplexCat
