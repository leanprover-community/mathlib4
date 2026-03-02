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

In this file we define profunctors between two categories and natural transformations between profunctors.

Profunctors are defined as a structure with a mapping operation `map` that lets us map on both sides of the profunctor at once. We also provide operations `mapL` and `mapR` to map only on one side.
-/

@[expose] public section

namespace CategoryTheory

universe w

structure Profunctor (C : Type*) [Category* C] (D : Type*) [Category* D] where
  obj : D → C → Type w
  map {X X' : D} {Y Y' : C} (f : X' ⟶ X) (g : Y ⟶ Y') :
    obj X Y → obj X' Y'
  map_id (X : D) (Y : C) (e : obj X Y) : map (𝟙 _) (𝟙 _) e = e
  map_comp {X X' X'' : D} {Y Y' Y'' : C}
    (f' : X'' ⟶ X') (f : X' ⟶ X)
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
    (e : obj X Y) :
    map (f' ≫ f) (g ≫ g') e = map f' g' (map f g e)


variable {C : Type*} [Category C] {D : Type*} [Category D]

namespace Profunctor

/-! ### Left and right mapping -/

/-- Apply a profunctor to a morphism on the left (contravariant) side,
    keeping the right (covariant) side fixed. -/
def mapL (h : Profunctor.{w} C D) {X X' : D} (f : X ⟶ X') {Y : C} :
    h.obj X' Y → h.obj X Y :=
  h.map f (𝟙 Y)

/-- Apply a profunctor to a morphism on the right (covariant) side,
    keeping the left (contravariant) side fixed. -/
def mapR (h : Profunctor.{w} C D) {X : D} {Y Y' : C} (g : Y ⟶ Y') :
    h.obj X Y → h.obj X Y' :=
  h.map (𝟙 X) g

@[simp]
theorem mapL_id (h : Profunctor.{w} C D) (X : D) (Y : C) (e : h.obj X Y) :
    h.mapL (𝟙 X) e = e :=
  h.map_id X Y e

@[simp]
theorem mapR_id (h : Profunctor.{w} C D) (X : D) (Y : C) (e : h.obj X Y) :
    h.mapR (𝟙 Y) e = e :=
  h.map_id X Y e

theorem mapL_comp (h : Profunctor.{w} C D) {X X' X'' : D} (f : X ⟶ X') (f' : X' ⟶ X'')
    {Y : C} (e : h.obj X'' Y) :
    h.mapL (f ≫ f') e = h.mapL f (h.mapL f' e) := by
  simp only [mapL, ← h.map_comp, Category.comp_id]

theorem mapR_comp (h : Profunctor.{w} C D) {X : D} {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
    (e : h.obj X Y) :
    h.mapR (g ≫ g') e = h.mapR g' (h.mapR g e) := by
  simp only [mapR, ← h.map_comp, Category.comp_id]

theorem map_eq_mapL_mapR (h : Profunctor.{w} C D) {X X' : D} {Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (e : h.obj X' Y) :
    h.map f g e = h.mapR g (h.mapL f e) := by
  simp only [mapL, mapR, ← h.map_comp, Category.id_comp]

theorem map_eq_mapR_mapL (h : Profunctor.{w} C D) {X X' : D} {Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (e : h.obj X' Y) :
    h.map f g e = h.mapL f (h.mapR g e) := by
  simp only [mapL, mapR, ← h.map_comp, Category.comp_id]

def mpRight (h : Profunctor.{w} C D) {a b c} (p : b = c) (f : h.obj a b) : h.obj a c :=
  h.mapR (eqToHom p) f

def mpLeft (h : Profunctor.{w} C D) {a b c} (p : a = b) (f : h.obj b c) : h.obj a c :=
  h.mapL (eqToHom p) f

/-- A natural transformation between profunctors `h` and `k`. -/
structure NatTrans (h k : Profunctor.{w} C D) where
  /-- The component of the natural transformation at each pair of objects. -/
  app (X : D) (Y : C) : h.obj X Y → k.obj X Y
  /-- Naturality: the transformation commutes with `map`. -/
  naturality {X X' : D} {Y Y' : C} (f : X' ⟶ X) (g : Y ⟶ Y') (e : h.obj X Y) :
    app X' Y' (h.map f g e) = k.map f g (app X Y e)

namespace NatTrans

/-- The identity natural transformation. -/
@[simps]
def id (h : Profunctor.{w} C D) : NatTrans h h where
  app _ _ e := e
  naturality _ _ _ := rfl

/-- Composition of natural transformations between profunctors. -/
@[simps]
def comp {h k R : Profunctor.{w} C D} (β : NatTrans k R) (α : NatTrans h k) :
    NatTrans h R where
  app X Y e := β.app X Y (α.app X Y e)
  naturality f g e := by rw [α.naturality, β.naturality]

@[ext]
theorem ext {h k : Profunctor.{w} C D} {α β : NatTrans h k}
    (h : ∀ (X : D) (Y : C) (e : h.obj X Y), α.app X Y e = β.app X Y e) :
    α = β := by
  cases α
  cases β
  congr
  funext X Y e
  exact h X Y e

@[simp]
theorem id_comp {h k : Profunctor.{w} C D} (α : NatTrans h k) :
    (NatTrans.id k).comp α = α := by
  ext
  simp [comp, id]

@[simp]
theorem comp_id {h k : Profunctor.{w} C D} (α : NatTrans h k) :
    α.comp (NatTrans.id h) = α := by
  ext
  simp [comp, id]

theorem comp_assoc {h k R S : Profunctor.{w} C D}
    (γ : NatTrans R S) (β : NatTrans k R) (α : NatTrans h k) :
    (γ.comp β).comp α = γ.comp (β.comp α) :=
  rfl

/-- Naturality with respect to `mapL`. -/
theorem naturality_mapL {h k : Profunctor.{w} C D} (α : NatTrans h k)
    {X X' : D} (f : X ⟶ X') {Y : C} (e : h.obj X' Y) :
    α.app X Y (h.mapL f e) = k.mapL f (α.app X' Y e) := by
  simp only [mapL]
  exact α.naturality f (𝟙 Y) e

/-- Naturality with respect to `mapR`. -/
theorem naturality_mapR {h k : Profunctor.{w} C D} (α : NatTrans h k)
    {X : D} {Y Y' : C} (g : Y ⟶ Y') (e : h.obj X Y) :
    α.app X Y' (h.mapR g e) = k.mapR g (α.app X Y e) := by
  simp only [mapR]
  exact α.naturality (𝟙 X) g e

end NatTrans

/-! ### Category instance for profunctors -/

/-- The category of profunctors from `D` to `C`, with natural transformations as morphisms. -/
instance instCategory : Category (Profunctor.{w} C D) where
  Hom h k := NatTrans h k
  id h := NatTrans.id h
  comp α β := β.comp α
  id_comp := NatTrans.comp_id
  comp_id := NatTrans.id_comp
  assoc _ _ _ := (NatTrans.comp_assoc _ _ _).symm

end Profunctor

end CategoryTheory
