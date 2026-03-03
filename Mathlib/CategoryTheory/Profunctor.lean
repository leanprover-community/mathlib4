/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti, Aristotle
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Tactic.CategoryTheory.CategoryStar

/-!
# Profunctors and Natural Transformations

In this file we define profunctors between two categories and natural transformations between
profunctors.

Profunctors are defined as a structure with a mapping operation `map` that lets us map on both sides
of the profunctor at once. We also provide operations `mapL` and `mapR` to map only on one side.
-/

@[expose] public section

namespace CategoryTheory

universe w

/-- A profunctor between two categories `C` and `D` is a functor from `Cᵒᵖ × D` to the category of
types. We encode this data as a structure. -/
structure Profunctor (C : Type*) [Category* C] (D : Type*) [Category* D] where
  /-- Apply a profunctor to a pair of objects. -/
  obj : D → C → Type w
  /-- Apply a profunctor to a pair of maps. -/
  map {X X' : D} {Y Y' : C} (f : X' ⟶ X) (g : Y ⟶ Y') :
    obj X Y → obj X' Y'
  /-- Identity law for profunctors. -/
  map_id (X : D) (Y : C) (e : obj X Y) : map (𝟙 _) (𝟙 _) e = e
  /-- Composition law for profunctors. -/
  map_comp {X X' X'' : D} {Y Y' Y'' : C}
    (f' : X'' ⟶ X') (f : X' ⟶ X)
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
    (e : obj X Y) :
    map (f' ≫ f) (g ≫ g') e = map f' g' (map f g e)

attribute [simp] Profunctor.map_id Profunctor.map_comp
attribute [grind =] Profunctor.map_id
attribute [grind _=_] Profunctor.map_comp

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

namespace Profunctor

/-! ### Left and right mapping -/

/-- Apply a profunctor to a morphism on the left (contravariant) side,
    keeping the right (covariant) side fixed. -/
def mapL (H : Profunctor.{w} C D) {X X' : D} (f : X ⟶ X') {Y : C} :
    H.obj X' Y → H.obj X Y :=
  H.map f (𝟙 Y)

/-- Apply a profunctor to a morphism on the right (covariant) side,
    keeping the left (contravariant) side fixed. -/
def mapR (H : Profunctor.{w} C D) {X : D} {Y Y' : C} (g : Y ⟶ Y') :
    H.obj X Y → H.obj X Y' :=
  H.map (𝟙 X) g

@[simp]
theorem mapL_id (H : Profunctor.{w} C D) (X : D) (Y : C) (e : H.obj X Y) :
    H.mapL (𝟙 X) e = e :=
  H.map_id X Y e

@[simp]
theorem mapR_id (H : Profunctor.{w} C D) (X : D) (Y : C) (e : H.obj X Y) :
    H.mapR (𝟙 Y) e = e :=
  H.map_id X Y e

theorem mapL_comp (H : Profunctor.{w} C D) {X X' X'' : D} (f : X ⟶ X') (f' : X' ⟶ X'')
    {Y : C} (e : H.obj X'' Y) :
    H.mapL (f ≫ f') e = H.mapL f (H.mapL f' e) := by
  simp only [mapL, ← H.map_comp, Category.comp_id]

theorem mapR_comp (H : Profunctor.{w} C D) {X : D} {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
    (e : H.obj X Y) :
    H.mapR (g ≫ g') e = H.mapR g' (H.mapR g e) := by
  simp only [mapR, ← H.map_comp, Category.comp_id]

theorem map_eq_mapL_mapR (H : Profunctor.{w} C D) {X X' : D} {Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (e : H.obj X' Y) :
    H.map f g e = H.mapR g (H.mapL f e) := by
  simp only [mapL, mapR, ← H.map_comp, Category.id_comp]

theorem map_eq_mapR_mapL (H : Profunctor.{w} C D) {X X' : D} {Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (e : H.obj X' Y) :
    H.map f g e = H.mapL f (H.mapR g e) := by
  simp only [mapL, mapR, ← H.map_comp, Category.comp_id]

/-- Transport a profunctor along an equality on the left. -/
def mpLeft (H : Profunctor.{w} C D) {a b c} (p : a = b) (f : H.obj b c) : H.obj a c :=
  H.mapL (eqToHom p) f

/-- Transport a profunctor along an equality on the right. -/
def mpRight (H : Profunctor.{w} C D) {a b c} (p : b = c) (f : H.obj a b) : H.obj a c :=
  H.mapR (eqToHom p) f

/-- A natural transformation between profunctors `H` and `K`. -/
structure NatTrans (H K : Profunctor.{w} C D) where
  /-- The component of the natural transformation at each pair of objects. -/
  app (X : D) (Y : C) : H.obj X Y → K.obj X Y
  /-- Naturality: the transformation commutes with `map`. -/
  naturality {X X' : D} {Y Y' : C} (f : X' ⟶ X) (g : Y ⟶ Y') (e : H.obj X Y) :
    app X' Y' (H.map f g e) = K.map f g (app X Y e)

namespace NatTrans

/-- The identity natural transformation. -/
@[simps]
def id (H : Profunctor.{w} C D) : NatTrans H H where
  app _ _ e := e
  naturality _ _ _ := rfl

/-- Composition of natural transformations between profunctors. -/
@[simps]
def comp {H K R : Profunctor.{w} C D} (β : NatTrans K R) (α : NatTrans H K) :
    NatTrans H R where
  app X Y e := β.app X Y (α.app X Y e)
  naturality f g e := by rw [α.naturality, β.naturality]

@[ext]
theorem ext {H K : Profunctor.{w} C D} {α β : NatTrans H K}
    (H : ∀ (X : D) (Y : C) (e : H.obj X Y), α.app X Y e = β.app X Y e) :
    α = β := by
  cases α
  cases β
  congr
  funext X Y e
  exact H X Y e

@[simp]
theorem id_comp {H K : Profunctor.{w} C D} (α : NatTrans H K) :
    (NatTrans.id K).comp α = α := by
  ext
  simp [comp, id]

@[simp]
theorem comp_id {H K : Profunctor.{w} C D} (α : NatTrans H K) :
    α.comp (NatTrans.id H) = α := by
  ext
  simp [comp, id]

theorem comp_assoc {H K L M : Profunctor.{w} C D}
    (γ : NatTrans L M) (β : NatTrans K L) (α : NatTrans H K) :
    (γ.comp β).comp α = γ.comp (β.comp α) :=
  rfl

/-- Naturality with respect to `mapL`. -/
theorem naturality_mapL {H K : Profunctor.{w} C D} (α : NatTrans H K)
    {X X' : D} (f : X ⟶ X') {Y : C} (e : H.obj X' Y) :
    α.app X Y (H.mapL f e) = K.mapL f (α.app X' Y e) := by
  simp only [mapL]
  exact α.naturality f (𝟙 Y) e

/-- Naturality with respect to `mapR`. -/
theorem naturality_mapR {H K : Profunctor.{w} C D} (α : NatTrans H K)
    {X : D} {Y Y' : C} (g : Y ⟶ Y') (e : H.obj X Y) :
    α.app X Y' (H.mapR g e) = K.mapR g (α.app X Y e) := by
  simp only [mapR]
  exact α.naturality (𝟙 X) g e

end NatTrans

/-! ### Category instance for profunctors -/

/-- The category of profunctors from `D` to `C`, with natural transformations as morphisms. -/
instance instCategory : Category (Profunctor.{w} C D) where
  Hom H K := NatTrans H K
  id H := NatTrans.id H
  comp α β := β.comp α
  id_comp := NatTrans.comp_id
  comp_id := NatTrans.id_comp
  assoc _ _ _ := (NatTrans.comp_assoc _ _ _).symm

end Profunctor

end CategoryTheory
