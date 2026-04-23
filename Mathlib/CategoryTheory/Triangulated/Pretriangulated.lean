/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Triangulated.TriangleShift
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.StacksAttribute

/-!
# Pretriangulated Categories

This file contains the definition of pretriangulated categories and triangulated functors
between them.

## Implementation Notes

We work under the assumption that pretriangulated categories are preadditive categories,
but not necessarily additive categories, as is assumed in some sources.

TODO: generalise this to n-angulated categories as in https://arxiv.org/abs/1006.4592
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

noncomputable section

open CategoryTheory Preadditive Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory

open Category Pretriangulated ZeroObject

/-
We work in a preadditive category `C` equipped with an additive shift.
-/
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]

/-- A preadditive category `C` with an additive shift, and a class of "distinguished triangles"
relative to that shift is called pretriangulated if the following hold:
* Any triangle that is isomorphic to a distinguished triangle is also distinguished.
* Any triangle of the form `(X,X,0,id,0,0)` is distinguished.
* For any morphism `f : X ⟶ Y` there exists a distinguished triangle of the form `(X,Y,Z,f,g,h)`.
* The triangle `(X,Y,Z,f,g,h)` is distinguished if and only if `(Y,Z,X⟦1⟧,g,h,-f⟦1⟧)` is.
* Given a diagram:
  ```
        f       g       h
    X  ───> Y  ───> Z  ───> X⟦1⟧
    │       │                │
    │a      │b               │a⟦1⟧'
    V       V                V
    X' ───> Y' ───> Z' ───> X'⟦1⟧
        f'      g'      h'
  ```
  where the left square commutes, and whose rows are distinguished triangles,
  there exists a morphism `c : Z ⟶ Z'` such that `(a,b,c)` is a triangle morphism.
-/
@[stacks 0145]
class Pretriangulated [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] where
  /-- a class of triangle which are called `distinguished` -/
  distinguishedTriangles : Set (Triangle C)
  /-- a triangle that is isomorphic to a distinguished triangle is distinguished -/
  isomorphic_distinguished :
    ∀ T₁ ∈ distinguishedTriangles, ∀ (T₂) (_ : T₂ ≅ T₁), T₂ ∈ distinguishedTriangles
  /-- obvious triangles `X ⟶ X ⟶ 0 ⟶ X⟦1⟧` are distinguished -/
  contractible_distinguished : ∀ X : C, contractibleTriangle X ∈ distinguishedTriangles
  /-- any morphism `X ⟶ Y` is part of a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` -/
  distinguished_cocone_triangle :
    ∀ {X Y : C} (f : X ⟶ Y),
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distinguishedTriangles
  /-- a triangle is distinguished iff it is so after rotating it -/
  rotate_distinguished_triangle :
    ∀ T : Triangle C, T ∈ distinguishedTriangles ↔ T.rotate ∈ distinguishedTriangles
  /-- given two distinguished triangle, a commutative square
  can be extended as morphism of triangles -/
  complete_distinguished_triangle_morphism :
    ∀ (T₁ T₂ : Triangle C) (_ : T₁ ∈ distinguishedTriangles) (_ : T₂ ∈ distinguishedTriangles)
      (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁),
      ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃


namespace Pretriangulated

variable [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor C n)] [hC : Pretriangulated C]

/-- distinguished triangles in a pretriangulated category -/
notation:60 "distTriang " C:60 => @distinguishedTriangles C _ _ _ _ _ _

variable {C}

lemma distinguished_iff_of_iso {T₁ T₂ : Triangle C} (e : T₁ ≅ T₂) :
    T₁ ∈ distTriang C ↔ T₂ ∈ distTriang C :=
  ⟨fun hT₁ => isomorphic_distinguished _ hT₁ _ e.symm,
    fun hT₂ => isomorphic_distinguished _ hT₂ _ e⟩

/-- Given any distinguished triangle `T`, then we know `T.rotate` is also distinguished.
-/
theorem rot_of_distTriang (T : Triangle C) (H : T ∈ distTriang C) : T.rotate ∈ distTriang C :=
  (rotate_distinguished_triangle T).mp H

/-- Given any distinguished triangle `T`, then we know `T.inv_rotate` is also distinguished.
-/
theorem inv_rot_of_distTriang (T : Triangle C) (H : T ∈ distTriang C) :
    T.invRotate ∈ distTriang C :=
  (rotate_distinguished_triangle T.invRotate).mpr
    (isomorphic_distinguished T H T.invRotate.rotate (invRotCompRot.app T))

set_option backward.isDefEq.respectTransparency false in
/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `f ≫ g = 0`. -/
@[reassoc, stacks 0146]
theorem comp_distTriang_mor_zero₁₂ (T) (H : T ∈ distTriang C) : T.mor₁ ≫ T.mor₂ = 0 := by
  obtain ⟨c, hc⟩ :=
    complete_distinguished_triangle_morphism _ _ (contractible_distinguished T.obj₁) H (𝟙 T.obj₁)
      T.mor₁ rfl
  simpa only [contractibleTriangle_mor₂, zero_comp] using hc.left.symm

/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `g ≫ h = 0`. -/
@[reassoc, stacks 0146]
theorem comp_distTriang_mor_zero₂₃ (T : Triangle C) (H : T ∈ distTriang C) :
    T.mor₂ ≫ T.mor₃ = 0 :=
  comp_distTriang_mor_zero₁₂ T.rotate (rot_of_distTriang T H)

set_option backward.isDefEq.respectTransparency false in
/-- Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `h ≫ f⟦1⟧ = 0`. -/
@[reassoc, stacks 0146]
theorem comp_distTriang_mor_zero₃₁ (T : Triangle C) (H : T ∈ distTriang C) :
    T.mor₃ ≫ T.mor₁⟦1⟧' = 0 := by
  have H₂ := rot_of_distTriang T.rotate (rot_of_distTriang T H)
  simpa using comp_distTriang_mor_zero₁₂ T.rotate.rotate H₂

/-- The short complex `T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃` attached to a distinguished triangle. -/
@[simps]
def shortComplexOfDistTriangle (T : Triangle C) (hT : T ∈ distTriang C) : ShortComplex C :=
  ShortComplex.mk T.mor₁ T.mor₂ (comp_distTriang_mor_zero₁₂ _ hT)

/-- The isomorphism between the short complex attached to
two isomorphic distinguished triangles. -/
@[simps!]
def shortComplexOfDistTriangleIsoOfIso {T T' : Triangle C} (e : T ≅ T') (hT : T ∈ distTriang C) :
    shortComplexOfDistTriangle T hT ≅ shortComplexOfDistTriangle T'
      (isomorphic_distinguished _ hT _ e.symm) :=
  ShortComplex.isoMk (Triangle.π₁.mapIso e) (Triangle.π₂.mapIso e) (Triangle.π₃.mapIso e)

/-- Any morphism `Y ⟶ Z` is part of a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` -/
lemma distinguished_cocone_triangle₁ {Y Z : C} (g : Y ⟶ Z) :
    ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X', f', g', mem⟩ := distinguished_cocone_triangle g
  exact ⟨_, _, _, inv_rot_of_distTriang _ mem⟩

set_option backward.isDefEq.respectTransparency false in
/-- Any morphism `Z ⟶ X⟦1⟧` is part of a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` -/
lemma distinguished_cocone_triangle₂ {Z X : C} (h : Z ⟶ X⟦(1 : ℤ)⟧) :
    ∃ (Y : C) (f : X ⟶ Y) (g : Y ⟶ Z), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨Y', f', g', mem⟩ := distinguished_cocone_triangle h
  let T' := (Triangle.mk h f' g').invRotate.invRotate
  refine ⟨T'.obj₂, ((shiftEquiv C (1 : ℤ)).unitIso.app X).hom ≫ T'.mor₁, T'.mor₂,
    isomorphic_distinguished _ (inv_rot_of_distTriang _ (inv_rot_of_distTriang _ mem)) _ ?_⟩
  exact Triangle.isoMk _ _ ((shiftEquiv C (1 : ℤ)).unitIso.app X) (Iso.refl _) (Iso.refl _)
    (by cat_disch) (by cat_disch)
    (by dsimp; simp only [shift_shiftFunctorCompIsoId_inv_app, id_comp])

/-- A commutative square involving the morphisms `mor₂` of two distinguished triangles
can be extended as morphism of triangles -/
lemma complete_distinguished_triangle_morphism₁ (T₁ T₂ : Triangle C)
    (hT₁ : T₁ ∈ distTriang C) (hT₂ : T₂ ∈ distTriang C) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (c : T₁.obj₃ ⟶ T₂.obj₃) (comm : T₁.mor₂ ≫ c = b ≫ T₂.mor₂) :
    ∃ (a : T₁.obj₁ ⟶ T₂.obj₁), T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := complete_distinguished_triangle_morphism _ _
    (rot_of_distTriang _ hT₁) (rot_of_distTriang _ hT₂) b c comm
  refine ⟨(shiftFunctor C (1 : ℤ)).preimage a, ⟨?_, ?_⟩⟩
  · apply (shiftFunctor C (1 : ℤ)).map_injective
    dsimp at ha₂
    rw [neg_comp, comp_neg, neg_inj] at ha₂
    simpa only [Functor.map_comp, Functor.map_preimage] using ha₂
  · simpa only [Functor.map_preimage] using ha₁

set_option backward.isDefEq.respectTransparency false in
/-- A commutative square involving the morphisms `mor₃` of two distinguished triangles
can be extended as morphism of triangles -/
lemma complete_distinguished_triangle_morphism₂ (T₁ T₂ : Triangle C)
    (hT₁ : T₁ ∈ distTriang C) (hT₂ : T₂ ∈ distTriang C) (a : T₁.obj₁ ⟶ T₂.obj₁)
    (c : T₁.obj₃ ⟶ T₂.obj₃) (comm : T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃) :
    ∃ (b : T₁.obj₂ ⟶ T₂.obj₂), T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧ T₁.mor₂ ≫ c = b ≫ T₂.mor₂ := by
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := complete_distinguished_triangle_morphism _ _
    (inv_rot_of_distTriang _ hT₁) (inv_rot_of_distTriang _ hT₂) (c⟦(-1 : ℤ)⟧') a (by
    dsimp
    simp only [neg_comp, comp_neg, ← Functor.map_comp_assoc, ← comm,
      Functor.map_comp, shift_shift_neg', Functor.id_obj, assoc, Iso.inv_hom_id_app, comp_id])
  refine ⟨a, ⟨ha₁, ?_⟩⟩
  dsimp only [Triangle.invRotate, Triangle.mk] at ha₂
  rw [← cancel_mono ((shiftEquiv C (1 : ℤ)).counitIso.inv.app T₂.obj₃), assoc, assoc, ← ha₂]
  simp only [shiftEquiv'_counitIso, shift_neg_shift', assoc, Iso.inv_hom_id_app_assoc]

/-- Obvious triangles `0 ⟶ X ⟶ X ⟶ 0⟦1⟧` are distinguished -/
lemma contractible_distinguished₁ (X : C) :
    Triangle.mk (0 : 0 ⟶ X) (𝟙 X) 0 ∈ distTriang C := by
  refine isomorphic_distinguished _
    (inv_rot_of_distTriang _ (contractible_distinguished X)) _ ?_
  exact Triangle.isoMk _ _ (Functor.mapZeroObject _).symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Obvious triangles `X ⟶ 0 ⟶ X⟦1⟧ ⟶ X⟦1⟧` are distinguished -/
lemma contractible_distinguished₂ (X : C) :
    Triangle.mk (0 : X ⟶ 0) 0 (𝟙 (X⟦1⟧)) ∈ distTriang C := by
  refine isomorphic_distinguished _
    (inv_rot_of_distTriang _ (contractible_distinguished₁ (X⟦(1 : ℤ)⟧))) _ ?_
  exact Triangle.isoMk _ _ ((shiftEquiv C (1 : ℤ)).unitIso.app X) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp)
    (by dsimp; simp only [shift_shiftFunctorCompIsoId_inv_app, id_comp])

namespace Triangle

variable (T : Triangle C) (hT : T ∈ distTriang C)
include hT

lemma yoneda_exact₂ {X : C} (f : T.obj₂ ⟶ X) (hf : T.mor₁ ≫ f = 0) :
    ∃ (g : T.obj₃ ⟶ X), f = T.mor₂ ≫ g := by
  obtain ⟨g, ⟨hg₁, _⟩⟩ := complete_distinguished_triangle_morphism T _ hT
    (contractible_distinguished₁ X) 0 f (by cat_disch)
  exact ⟨g, by simpa using hg₁.symm⟩

lemma yoneda_exact₃ {X : C} (f : T.obj₃ ⟶ X) (hf : T.mor₂ ≫ f = 0) :
    ∃ (g : T.obj₁⟦(1 : ℤ)⟧ ⟶ X), f = T.mor₃ ≫ g :=
  yoneda_exact₂ _ (rot_of_distTriang _ hT) f hf

lemma coyoneda_exact₂ {X : C} (f : X ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) :
    ∃ (g : X ⟶ T.obj₁), f = g ≫ T.mor₁ := by
  obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ T
    (contractible_distinguished X) hT f 0 (by cat_disch)
  exact ⟨a, by simpa using ha₁⟩

lemma coyoneda_exact₁ {X : C} (f : X ⟶ T.obj₁⟦(1 : ℤ)⟧) (hf : f ≫ T.mor₁⟦1⟧' = 0) :
    ∃ (g : X ⟶ T.obj₃), f = g ≫ T.mor₃ :=
  coyoneda_exact₂ _ (rot_of_distTriang _ (rot_of_distTriang _ hT)) f (by cat_disch)

lemma coyoneda_exact₃ {X : C} (f : X ⟶ T.obj₃) (hf : f ≫ T.mor₃ = 0) :
    ∃ (g : X ⟶ T.obj₂), f = g ≫ T.mor₂ :=
  coyoneda_exact₂ _ (rot_of_distTriang _ hT) f hf

lemma mor₃_eq_zero_iff_epi₂ : T.mor₃ = 0 ↔ Epi T.mor₂ := by
  constructor
  · intro h
    rw [epi_iff_cancel_zero]
    intro X g hg
    obtain ⟨f, rfl⟩ := yoneda_exact₃ T hT g hg
    rw [h, zero_comp]
  · intro
    rw [← cancel_epi T.mor₂, comp_distTriang_mor_zero₂₃ _ hT, comp_zero]

set_option backward.isDefEq.respectTransparency false in
lemma mor₂_eq_zero_iff_epi₁ : T.mor₂ = 0 ↔ Epi T.mor₁ := by
  have h := mor₃_eq_zero_iff_epi₂ _ (inv_rot_of_distTriang _ hT)
  dsimp at h
  rw [← h, IsIso.comp_right_eq_zero]

set_option backward.isDefEq.respectTransparency false in
lemma mor₁_eq_zero_iff_epi₃ : T.mor₁ = 0 ↔ Epi T.mor₃ := by
  have h := mor₃_eq_zero_iff_epi₂ _ (rot_of_distTriang _ hT)
  dsimp at h
  rw [← h, neg_eq_zero]
  exact (Functor.map_eq_zero_iff (CategoryTheory.shiftFunctor C 1)).symm

lemma mor₃_eq_zero_of_epi₂ (h : Epi T.mor₂) : T.mor₃ = 0 := (T.mor₃_eq_zero_iff_epi₂ hT).2 h
lemma mor₂_eq_zero_of_epi₁ (h : Epi T.mor₁) : T.mor₂ = 0 := (T.mor₂_eq_zero_iff_epi₁ hT).2 h
lemma mor₁_eq_zero_of_epi₃ (h : Epi T.mor₃) : T.mor₁ = 0 := (T.mor₁_eq_zero_iff_epi₃ hT).2 h

lemma epi₂ (h : T.mor₃ = 0) : Epi T.mor₂ := (T.mor₃_eq_zero_iff_epi₂ hT).1 h
lemma epi₁ (h : T.mor₂ = 0) : Epi T.mor₁ := (T.mor₂_eq_zero_iff_epi₁ hT).1 h
lemma epi₃ (h : T.mor₁ = 0) : Epi T.mor₃ := (T.mor₁_eq_zero_iff_epi₃ hT).1 h

lemma mor₁_eq_zero_iff_mono₂ : T.mor₁ = 0 ↔ Mono T.mor₂ := by
  constructor
  · intro h
    rw [mono_iff_cancel_zero]
    intro X g hg
    obtain ⟨f, rfl⟩ := coyoneda_exact₂ T hT g hg
    rw [h, comp_zero]
  · intro
    rw [← cancel_mono T.mor₂, comp_distTriang_mor_zero₁₂ _ hT, zero_comp]

lemma mor₂_eq_zero_iff_mono₃ : T.mor₂ = 0 ↔ Mono T.mor₃ :=
  mor₁_eq_zero_iff_mono₂ _ (rot_of_distTriang _ hT)

set_option backward.isDefEq.respectTransparency false in
lemma mor₃_eq_zero_iff_mono₁ : T.mor₃ = 0 ↔ Mono T.mor₁ := by
  have h := mor₁_eq_zero_iff_mono₂ _ (inv_rot_of_distTriang _ hT)
  dsimp at h
  rw [← h, neg_eq_zero, IsIso.comp_right_eq_zero]
  exact (Functor.map_eq_zero_iff (CategoryTheory.shiftFunctor C (-1))).symm

lemma mor₁_eq_zero_of_mono₂ (h : Mono T.mor₂) : T.mor₁ = 0 := (T.mor₁_eq_zero_iff_mono₂ hT).2 h
lemma mor₂_eq_zero_of_mono₃ (h : Mono T.mor₃) : T.mor₂ = 0 := (T.mor₂_eq_zero_iff_mono₃ hT).2 h
lemma mor₃_eq_zero_of_mono₁ (h : Mono T.mor₁) : T.mor₃ = 0 := (T.mor₃_eq_zero_iff_mono₁ hT).2 h

lemma mono₂ (h : T.mor₁ = 0) : Mono T.mor₂ := (T.mor₁_eq_zero_iff_mono₂ hT).1 h
lemma mono₃ (h : T.mor₂ = 0) : Mono T.mor₃ := (T.mor₂_eq_zero_iff_mono₃ hT).1 h
lemma mono₁ (h : T.mor₃ = 0) : Mono T.mor₁ := (T.mor₃_eq_zero_iff_mono₁ hT).1 h

lemma isZero₂_iff : IsZero T.obj₂ ↔ (T.mor₁ = 0 ∧ T.mor₂ = 0) := by
  constructor
  · intro h
    exact ⟨h.eq_of_tgt _ _, h.eq_of_src _ _⟩
  · intro ⟨h₁, h₂⟩
    obtain ⟨f, hf⟩ := coyoneda_exact₂ T hT (𝟙 _) (by rw [h₂, comp_zero])
    rw [IsZero.iff_id_eq_zero, hf, h₁, comp_zero]

set_option backward.isDefEq.respectTransparency false in
lemma isZero₁_iff : IsZero T.obj₁ ↔ (T.mor₁ = 0 ∧ T.mor₃ = 0) := by
  refine (isZero₂_iff _ (inv_rot_of_distTriang _ hT)).trans ?_
  dsimp
  simp only [neg_eq_zero, IsIso.comp_right_eq_zero, Functor.map_eq_zero_iff]
  tauto

lemma isZero₃_iff : IsZero T.obj₃ ↔ (T.mor₂ = 0 ∧ T.mor₃ = 0) := by
  refine (isZero₂_iff _ (rot_of_distTriang _ hT)).trans ?_
  dsimp
  tauto

lemma isZero₁_of_isZero₂₃ (h₂ : IsZero T.obj₂) (h₃ : IsZero T.obj₃) : IsZero T.obj₁ := by
  rw [T.isZero₁_iff hT]
  exact ⟨h₂.eq_of_tgt _ _, h₃.eq_of_src _ _⟩

lemma isZero₂_of_isZero₁₃ (h₁ : IsZero T.obj₁) (h₃ : IsZero T.obj₃) : IsZero T.obj₂ := by
  rw [T.isZero₂_iff hT]
  exact ⟨h₁.eq_of_src _ _, h₃.eq_of_tgt _ _⟩

lemma isZero₃_of_isZero₁₂ (h₁ : IsZero T.obj₁) (h₂ : IsZero T.obj₂) : IsZero T.obj₃ :=
  isZero₂_of_isZero₁₃ _ (rot_of_distTriang _ hT) h₂ (by
    dsimp
    simp only [IsZero.iff_id_eq_zero] at h₁ ⊢
    rw [← Functor.map_id, h₁, Functor.map_zero])

lemma isZero₁_iff_isIso₂ :
    IsZero T.obj₁ ↔ IsIso T.mor₂ := by
  rw [T.isZero₁_iff hT]
  constructor
  · intro ⟨h₁, h₃⟩
    have := T.epi₂ hT h₃
    obtain ⟨f, hf⟩ := yoneda_exact₂ T hT (𝟙 _) (by rw [h₁, zero_comp])
    exact ⟨f, hf.symm, by rw [← cancel_epi T.mor₂, comp_id, ← reassoc_of% hf]⟩
  · intro
    rw [T.mor₁_eq_zero_iff_mono₂ hT, T.mor₃_eq_zero_iff_epi₂ hT]
    constructor <;> infer_instance

lemma isZero₂_iff_isIso₃ : IsZero T.obj₂ ↔ IsIso T.mor₃ :=
  isZero₁_iff_isIso₂ _ (rot_of_distTriang _ hT)

lemma isZero₃_iff_isIso₁ : IsZero T.obj₃ ↔ IsIso T.mor₁ := by
  refine Iff.trans ?_ (Triangle.isZero₁_iff_isIso₂ _ (inv_rot_of_distTriang _ hT))
  dsimp
  simp only [IsZero.iff_id_eq_zero, ← Functor.map_id, Functor.map_eq_zero_iff]

lemma isZero₁_of_isIso₂ (h : IsIso T.mor₂) : IsZero T.obj₁ := (T.isZero₁_iff_isIso₂ hT).2 h
lemma isZero₂_of_isIso₃ (h : IsIso T.mor₃) : IsZero T.obj₂ := (T.isZero₂_iff_isIso₃ hT).2 h
lemma isZero₃_of_isIso₁ (h : IsIso T.mor₁) : IsZero T.obj₃ := (T.isZero₃_iff_isIso₁ hT).2 h

lemma shift_distinguished (n : ℤ) :
    (CategoryTheory.shiftFunctor (Triangle C) n).obj T ∈ distTriang C := by
  revert T hT
  let H : ℤ → Prop := fun n => ∀ (T : Triangle C) (_ : T ∈ distTriang C),
    (Triangle.shiftFunctor C n).obj T ∈ distTriang C
  change H n
  have H_zero : H 0 := fun T hT =>
    isomorphic_distinguished _ hT _ ((Triangle.shiftFunctorZero C).app T)
  have H_one : H 1 := fun T hT =>
    isomorphic_distinguished _ (rot_of_distTriang _
      (rot_of_distTriang _ (rot_of_distTriang _ hT))) _
        ((rotateRotateRotateIso C).symm.app T)
  have H_neg_one : H (-1) := fun T hT =>
    isomorphic_distinguished _ (inv_rot_of_distTriang _
      (inv_rot_of_distTriang _ (inv_rot_of_distTriang _ hT))) _
        ((invRotateInvRotateInvRotateIso C).symm.app T)
  have H_add : ∀ {a b c : ℤ}, H a → H b → a + b = c → H c := fun {a b c} ha hb hc T hT =>
    isomorphic_distinguished _ (hb _ (ha _ hT)) _
      ((Triangle.shiftFunctorAdd' C _ _ _ hc).app T)
  obtain (n | n) := n
  · induction n with
    | zero => exact H_zero
    | succ n hn => exact H_add hn H_one rfl
  · induction n with
    | zero => exact H_neg_one
    | succ n hn => exact H_add hn H_neg_one rfl

section

omit hT

lemma shift_distinguished_iff (n : ℤ) :
    (CategoryTheory.shiftFunctor (Triangle C) n).obj T ∈ (distTriang C) ↔ T ∈ distTriang C :=
  ⟨fun hT ↦ isomorphic_distinguished _ (shift_distinguished _ hT (-n)) _
      ((shiftEquiv (Triangle C) n).unitIso.app T),
    fun hT ↦ shift_distinguished T hT n⟩

lemma distinguished_iff_of_isZero₃ (T : Triangle C) (h : IsZero T.obj₃) :
    T ∈ distTriang _ ↔ IsIso T.mor₁ :=
  ⟨fun hT ↦ by rwa [← isZero₃_iff_isIso₁ _ hT],
    fun _ ↦ isomorphic_distinguished _ (contractible_distinguished T.obj₁) _
      (isoMk _ _ (Iso.refl _) (asIso T.mor₁).symm h.isoZero (by simp)
        ((isZero_zero C).eq_of_tgt _ _) (h.eq_of_src _ _))⟩

lemma distinguished_iff_of_isZero₁ (T : Triangle C) (h : IsZero T.obj₁) :
    T ∈ distTriang _ ↔ IsIso T.mor₂ := by
  rw [rotate_distinguished_triangle,
    distinguished_iff_of_isZero₃ _ (Functor.map_isZero (CategoryTheory.shiftFunctor C 1) h)]
  simp

lemma distinguished_iff_of_isZero₂ (T : Triangle C) (h : IsZero T.obj₂) :
    T ∈ distTriang _ ↔ IsIso T.mor₃ := by
  rw [rotate_distinguished_triangle, distinguished_iff_of_isZero₁ _ h]
  simp

end

end Triangle

instance : SplitEpiCategory C where
  isSplitEpi_of_epi f hf := by
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
    obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₂ _ hT (𝟙 _)
      (by rw [Triangle.mor₂_eq_zero_of_epi₁ _ hT hf, comp_zero])
    exact ⟨r, hr.symm⟩

instance : SplitMonoCategory C where
  isSplitMono_of_mono f hf := by
    obtain ⟨X, g, h, hT⟩ := distinguished_cocone_triangle₁ f
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ hT (𝟙 _) (by
      rw [Triangle.mor₁_eq_zero_of_mono₂ _ hT hf, zero_comp])
    exact ⟨r, hr.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the first and third components of a morphism of distinguished triangles are
isomorphisms, the second component is as well. This can be thought of as a
pretriangulated category theoretical version of the five lemma. -/
@[stacks 014A]
lemma isIso₂_of_isIso₁₃ {T T' : Triangle C} (φ : T ⟶ T') (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₂ := by
  have : Mono φ.hom₂ := by
    rw [mono_iff_cancel_zero]
    intro A f hf
    obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₂ _ hT f
      (by rw [← cancel_mono φ.hom₃, assoc, φ.comm₂, reassoc_of% hf, zero_comp, zero_comp])
    rw [assoc] at hf
    obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ T'.invRotate (inv_rot_of_distTriang _ hT')
      (g ≫ φ.hom₁) (by dsimp; rw [assoc, ← φ.comm₁, hf])
    obtain ⟨k, rfl⟩ : ∃ (k : A ⟶ T.invRotate.obj₁), k ≫ T.invRotate.mor₁ = g := by
      refine ⟨h ≫ inv (φ.hom₃⟦(-1 : ℤ)⟧'), ?_⟩
      have eq := ((invRotate C).map φ).comm₁
      dsimp only [invRotate] at eq
      rw [← cancel_mono φ.hom₁, assoc, assoc, eq, IsIso.inv_hom_id_assoc, hh]
    erw [assoc, comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hT), comp_zero]
  refine isIso_of_yoneda_map_bijective _ (fun A => ⟨?_, ?_⟩)
  · intro f₁ f₂ h
    simpa only [← cancel_mono φ.hom₂] using h
  · intro y₂
    obtain ⟨x₃, hx₃⟩ : ∃ (x₃ : A ⟶ T.obj₃), x₃ ≫ φ.hom₃ = y₂ ≫ T'.mor₂ :=
      ⟨y₂ ≫ T'.mor₂ ≫ inv φ.hom₃, by simp⟩
    obtain ⟨x₂, hx₂⟩ := Triangle.coyoneda_exact₃ _ hT x₃
      (by rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), assoc, zero_comp, φ.comm₃, reassoc_of% hx₃,
        comp_distTriang_mor_zero₂₃ _ hT', comp_zero])
    obtain ⟨y₁, hy₁⟩ := Triangle.coyoneda_exact₂ _ hT' (y₂ - x₂ ≫ φ.hom₂)
      (by rw [sub_comp, assoc, ← φ.comm₂, ← reassoc_of% hx₂, hx₃, sub_self])
    obtain ⟨x₁, hx₁⟩ : ∃ (x₁ : A ⟶ T.obj₁), x₁ ≫ φ.hom₁ = y₁ := ⟨y₁ ≫ inv φ.hom₁, by simp⟩
    refine ⟨x₂ + x₁ ≫ T.mor₁, ?_⟩
    dsimp
    rw [add_comp, assoc, φ.comm₁, reassoc_of% hx₁, ← hy₁, add_sub_cancel]

/-- If the first and second components of a morphism of distinguished triangles are
isomorphisms, the third component is as well. This can be thought of as a
pretriangulated category theoretical version of the five lemma. -/
@[stacks 014A]
lemma isIso₃_of_isIso₁₂ {T T' : Triangle C} (φ : T ⟶ T') (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) : IsIso φ.hom₃ :=
  isIso₂_of_isIso₁₃ ((rotate C).map φ) (rot_of_distTriang _ hT)
    (rot_of_distTriang _ hT') h₂ (by dsimp; infer_instance)

/-- If the second and third components of a morphism of distinguished triangles are
isomorphisms, the first component is as well. This can be thought of as a
pretriangulated category theoretical version of the five lemma. -/
@[stacks 014A]
lemma isIso₁_of_isIso₂₃ {T T' : Triangle C} (φ : T ⟶ T') (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (h₂ : IsIso φ.hom₂) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₁ :=
  isIso₂_of_isIso₁₃ ((invRotate C).map φ) (inv_rot_of_distTriang _ hT)
    (inv_rot_of_distTriang _ hT') (by dsimp; infer_instance) (by dsimp; infer_instance)

/-- Given a distinguished triangle `T` such that `T.mor₃ = 0` and the datum of morphisms
`inr : T.obj₃ ⟶ T.obj₂` and `fst : T.obj₂ ⟶ T.obj₁` satisfying suitable relations, this
is the binary biproduct data expressing that `T.obj₂` identifies to the binary
biproduct of `T.obj₁` and `T.obj₃`.
See also `exists_iso_binaryBiproduct_of_distTriang`. -/
@[simps]
def binaryBiproductData (T : Triangle C) (hT : T ∈ distTriang C) (hT₀ : T.mor₃ = 0)
    (inr : T.obj₃ ⟶ T.obj₂) (inr_snd : inr ≫ T.mor₂ = 𝟙 _) (fst : T.obj₂ ⟶ T.obj₁)
    (total : fst ≫ T.mor₁ + T.mor₂ ≫ inr = 𝟙 T.obj₂) :
    BinaryBiproductData T.obj₁ T.obj₃ := by
  have : Mono T.mor₁ := T.mono₁ hT hT₀
  have eq : fst ≫ T.mor₁ = 𝟙 T.obj₂ - T.mor₂ ≫ inr := by rw [← total, add_sub_cancel_right]
  exact
    { bicone :=
      { pt := T.obj₂
        fst := fst
        snd := T.mor₂
        inl := T.mor₁
        inr := inr
        inl_fst := by
          simp only [← cancel_mono T.mor₁, assoc, id_comp, eq, comp_sub, comp_id,
            comp_distTriang_mor_zero₁₂_assoc _ hT, zero_comp, sub_zero]
        inl_snd := comp_distTriang_mor_zero₁₂ _ hT
        inr_fst := by
          simp only [← cancel_mono T.mor₁, assoc, eq, comp_sub, reassoc_of% inr_snd,
            comp_id, sub_self, zero_comp]
        inr_snd := inr_snd }
      isBilimit := isBinaryBilimitOfTotal _ total }

set_option backward.isDefEq.respectTransparency false in
instance : HasBinaryBiproducts C := ⟨fun X₁ X₃ => by
  obtain ⟨X₂, inl, snd, mem⟩ := distinguished_cocone_triangle₂ (0 : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
  obtain ⟨inr : X₃ ⟶ X₂, inr_snd : 𝟙 _ = inr ≫ snd⟩ :=
    Triangle.coyoneda_exact₃ _ mem (𝟙 X₃) (by simp)
  obtain ⟨fst : X₂ ⟶ X₁, hfst : 𝟙 X₂ - snd ≫ inr = fst ≫ inl⟩ :=
    Triangle.coyoneda_exact₂ _ mem (𝟙 X₂ - snd ≫ inr) (by
      dsimp
      simp only [sub_comp, assoc, id_comp, ← inr_snd, comp_id, sub_self])
  refine ⟨⟨binaryBiproductData _ mem rfl inr inr_snd.symm fst ?_⟩⟩
  dsimp
  simp only [← hfst, sub_add_cancel]⟩

instance : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
instance : HasFiniteCoproducts C := hasFiniteCoproducts_of_has_binary_and_initial
instance : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts

lemma exists_iso_binaryBiproduct_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C)
    (zero : T.mor₃ = 0) :
    ∃ (e : T.obj₂ ≅ T.obj₁ ⊞ T.obj₃), T.mor₁ ≫ e.hom = biprod.inl ∧
      T.mor₂ = e.hom ≫ biprod.snd := by
  have := T.epi₂ hT zero
  have := isSplitEpi_of_epi T.mor₂
  obtain ⟨fst, hfst⟩ := T.coyoneda_exact₂ hT (𝟙 T.obj₂ - T.mor₂ ≫ section_ T.mor₂) (by simp)
  let d := binaryBiproductData _ hT zero (section_ T.mor₂) (by simp) fst
    (by simp only [← hfst, sub_add_cancel])
  refine ⟨biprod.uniqueUpToIso _ _ d.isBilimit, ⟨?_, by simp [d]⟩⟩
  ext
  · simpa [d] using d.bicone.inl_fst
  · simpa [d] using d.bicone.inl_snd

lemma binaryBiproductTriangle_distinguished (X₁ X₂ : C) :
    binaryBiproductTriangle X₁ X₂ ∈ distTriang C := by
  obtain ⟨Y, g, h, mem⟩ := distinguished_cocone_triangle₂ (0 : X₂ ⟶ X₁⟦(1 : ℤ)⟧)
  obtain ⟨e, ⟨he₁, he₂⟩⟩ := exists_iso_binaryBiproduct_of_distTriang _ mem rfl
  dsimp at he₁ he₂
  refine isomorphic_distinguished _ mem _ (Iso.symm ?_)
  refine Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
    (by cat_disch) (by cat_disch) (by simp)

lemma binaryProductTriangle_distinguished (X₁ X₂ : C) :
    binaryProductTriangle X₁ X₂ ∈ distTriang C :=
  isomorphic_distinguished _ (binaryBiproductTriangle_distinguished X₁ X₂) _
    (binaryProductTriangleIsoBinaryBiproductTriangle X₁ X₂)

/-- A chosen extension of a commutative square into a morphism of distinguished triangles. -/
@[simps hom₁ hom₂]
def completeDistinguishedTriangleMorphism (T₁ T₂ : Triangle C)
    (hT₁ : T₁ ∈ distTriang C) (hT₂ : T₂ ∈ distTriang C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    T₁ ⟶ T₂ :=
    have h := complete_distinguished_triangle_morphism _ _ hT₁ hT₂ a b comm
    { hom₁ := a
      hom₂ := b
      hom₃ := h.choose
      comm₁ := comm
      comm₂ := h.choose_spec.1
      comm₃ := h.choose_spec.2 }

set_option backward.isDefEq.respectTransparency false in
/-- A product of distinguished triangles is distinguished -/
lemma productTriangle_distinguished {J : Type*} (T : J → Triangle C)
    (hT : ∀ j, T j ∈ distTriang C)
    [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
    [HasProduct (fun j => (T j).obj₃)] [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)] :
    productTriangle T ∈ distTriang C := by
  /- The proof proceeds by constructing a morphism of triangles
    `φ' : T' ⟶ productTriangle T` with `T'` distinguished, and such that
    `φ'.hom₁` and `φ'.hom₂` are identities. Then, it suffices to show that
    `φ'.hom₃` is an isomorphism, which is achieved by using Yoneda's lemma
    and diagram chases. -/
  let f₁ := Limits.Pi.map (fun j => (T j).mor₁)
  obtain ⟨Z, f₂, f₃, hT'⟩ := distinguished_cocone_triangle f₁
  let T' := Triangle.mk f₁ f₂ f₃
  change T' ∈ distTriang C at hT'
  let φ : ∀ j, T' ⟶ T j := fun j => completeDistinguishedTriangleMorphism _ _
    hT' (hT j) (Pi.π _ j) (Pi.π _ j) (by simp [f₁, T'])
  let φ' := productTriangle.lift _ φ
  have h₁ : φ'.hom₁ = 𝟙 _ := by cat_disch
  have h₂ : φ'.hom₂ = 𝟙 _ := by cat_disch
  have : IsIso φ'.hom₁ := by rw [h₁]; infer_instance
  have : IsIso φ'.hom₂ := by rw [h₂]; infer_instance
  suffices IsIso φ'.hom₃ by
    have : IsIso φ' := by
      apply Triangle.isIso_of_isIsos
      all_goals infer_instance
    exact isomorphic_distinguished _ hT' _ (asIso φ').symm
  refine isIso_of_yoneda_map_bijective _ (fun A => ⟨?_, ?_⟩)
  /- the proofs by diagram chase start here -/
  · suffices Mono φ'.hom₃ by
      intro a₁ a₂ ha
      simpa only [← cancel_mono φ'.hom₃] using ha
    rw [mono_iff_cancel_zero]
    intro A f hf
    have hf' : f ≫ T'.mor₃ = 0 := by
      rw [← cancel_mono (φ'.hom₁⟦1⟧'), zero_comp, assoc, φ'.comm₃, reassoc_of% hf, zero_comp]
    obtain ⟨g, hg⟩ := T'.coyoneda_exact₃ hT' f hf'
    have hg' : ∀ j, (g ≫ Pi.π _ j) ≫ (T j).mor₂ = 0 := fun j => by
      have : g ≫ T'.mor₂ ≫ φ'.hom₃ ≫ Pi.π _ j = 0 := by
        rw [← reassoc_of% hg, reassoc_of% hf, zero_comp]
      rw [φ'.comm₂_assoc, h₂, id_comp] at this
      simpa using this
    have hg'' := fun j => (T j).coyoneda_exact₂ (hT j) _ (hg' j)
    let α := fun j => (hg'' j).choose
    have hα : ∀ j, _ = α j ≫ _ := fun j => (hg'' j).choose_spec
    have hg''' : g = Pi.lift α ≫ T'.mor₁ := by dsimp [f₁, T']; ext j; rw [hα]; simp
    rw [hg, hg''', assoc, comp_distTriang_mor_zero₁₂ _ hT', comp_zero]
  · intro a
    obtain ⟨a', ha'⟩ : ∃ (a' : A ⟶ Z), a' ≫ T'.mor₃ = a ≫ (productTriangle T).mor₃ := by
      have zero : ((productTriangle T).mor₃) ≫ (shiftFunctor C 1).map T'.mor₁ = 0 := by
        rw [← cancel_mono (φ'.hom₂⟦1⟧'), zero_comp, assoc, ← Functor.map_comp, φ'.comm₁, h₁,
          id_comp, productTriangle.zero₃₁]
        intro j
        exact comp_distTriang_mor_zero₃₁ _ (hT j)
      have ⟨g, hg⟩ := T'.coyoneda_exact₁ hT' (a ≫ (productTriangle T).mor₃) (by
        rw [assoc, zero, comp_zero])
      exact ⟨g, hg.symm⟩
    have ha'' := fun (j : J) => (T j).coyoneda_exact₃ (hT j) ((a - a' ≫ φ'.hom₃) ≫ Pi.π _ j) (by
      simp only [sub_comp, assoc]
      erw [← (productTriangle.π T j).comm₃]
      rw [← φ'.comm₃_assoc]
      rw [reassoc_of% ha', sub_eq_zero, h₁, Functor.map_id, id_comp])
    let b := fun j => (ha'' j).choose
    have hb : ∀ j, _ = b j ≫ _ := fun j => (ha'' j).choose_spec
    have hb' : a - a' ≫ φ'.hom₃ = Pi.lift b ≫ (productTriangle T).mor₂ :=
      Limits.Pi.hom_ext _ _ (fun j => by rw [hb]; simp)
    have : (a' + (by exact Pi.lift b) ≫ T'.mor₂) ≫ φ'.hom₃ = a := by
      rw [add_comp, assoc, φ'.comm₂, h₂, id_comp, ← hb', add_sub_cancel]
    exact ⟨_, this⟩

set_option backward.isDefEq.respectTransparency false in
lemma exists_iso_of_arrow_iso (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (e : Arrow.mk T₁.mor₁ ≅ Arrow.mk T₂.mor₁) :
    ∃ (e' : T₁ ≅ T₂), e'.hom.hom₁ = e.hom.left ∧ e'.hom.hom₂ = e.hom.right := by
  let φ := completeDistinguishedTriangleMorphism T₁ T₂ hT₁ hT₂ e.hom.left e.hom.right e.hom.w.symm
  have : IsIso φ.hom₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.hom₂ := by dsimp [φ]; infer_instance
  have : IsIso φ.hom₃ := isIso₃_of_isIso₁₂ φ hT₁ hT₂ inferInstance inferInstance
  have : IsIso φ := by
    apply Triangle.isIso_of_isIsos
    all_goals infer_instance
  exact ⟨asIso φ, by simp [φ], by simp [φ]⟩

/-- A choice of isomorphism `T₁ ≅ T₂` between two distinguished triangles
when we are given two isomorphisms `e₁ : T₁.obj₁ ≅ T₂.obj₁` and `e₂ : T₁.obj₂ ≅ T₂.obj₂`. -/
@[simps! hom_hom₁ hom_hom₂ inv_hom₁ inv_hom₂]
def isoTriangleOfIso₁₂ (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₂ : T₁.obj₂ ≅ T₂.obj₂)
    (comm : T₁.mor₁ ≫ e₂.hom = e₁.hom ≫ T₂.mor₁) : T₁ ≅ T₂ := by
  have h := exists_iso_of_arrow_iso T₁ T₂ hT₁ hT₂ (Arrow.isoMk e₁ e₂ comm.symm)
  exact Triangle.isoMk _ _ e₁ e₂ (Triangle.π₃.mapIso h.choose) comm (by
    have eq := h.choose_spec.2
    dsimp at eq ⊢
    conv_rhs => rw [← eq, ← TriangleMorphism.comm₂]) (by
    have eq := h.choose_spec.1
    dsimp at eq ⊢
    conv_lhs => rw [← eq, TriangleMorphism.comm₃])

set_option backward.isDefEq.respectTransparency false in
/-- A choice of isomorphism `T₁ ≅ T₂` between two distinguished triangles
when we are given two isomorphisms `e₁ : T₁.obj₁ ≅ T₂.obj₁` and `e₃ : T₁.obj₃ ≅ T₂.obj₃`. -/
@[simps! hom_hom₁ hom_hom₃ inv_hom₁ inv_hom₃]
def isoTriangleOfIso₁₃ (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distTriang C)
    (hT₂ : T₂ ∈ distTriang C) (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₃ : T₁.obj₃ ≅ T₂.obj₃)
    (comm : T₁.mor₃ ≫ (shiftFunctor C 1).map e₁.hom = e₃.hom ≫ T₂.mor₃) :
    T₁ ≅ T₂ := by
  have h := exists_iso_of_arrow_iso _ _ (inv_rot_of_distTriang _ hT₁)
    (inv_rot_of_distTriang _ hT₂)
    (Arrow.isoMk ((shiftFunctor C (-1)).mapIso e₃) e₁ (by
      have := (shiftFunctorCompIsoId C (1 : ℤ) (-1) (by simp)).hom.naturality e₁.hom
      dsimp at this ⊢
      simp only [comp_neg, neg_comp, assoc, neg_inj, ← Functor.map_comp_assoc, ← comm]
      simp [this]))
  let e := h.choose
  have h₁ : e.hom.hom₁ = _ := h.choose_spec.1
  have h₂ : _ = e.hom.hom₂ := h.choose_spec.2.symm
  have h₃ := e.hom.comm₃
  have h₄ := (shiftFunctorCompIsoId C (-1 : ℤ) 1 (by simp)).inv.naturality e₃.hom
  dsimp at h₁ h₂ h₃ h₄
  refine Triangle.isoMk _ _ e₁ (Triangle.π₃.mapIso e) e₃ ?_ ?_ comm
  · convert e.hom.comm₂ using 2
  · simp [← cancel_mono ((shiftFunctorCompIsoId C (-1) 1 (neg_add_cancel 1)).inv.app T₂.obj₃),
      ← h₃, assoc, h₁, h₄]

end Pretriangulated

end CategoryTheory
