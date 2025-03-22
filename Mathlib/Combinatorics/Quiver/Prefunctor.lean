/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Kim Morrison
-/
import Mathlib.Combinatorics.Quiver.Basic

/-!
# Morphisms of quivers
-/

universe v₁ v₂ u u₁ u₂

/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `Prefunctor`. -/
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)


namespace Prefunctor

-- These lemmas can not be `@[simp]` because after `whnfR` they have a variable on the LHS.
-- Nevertheless they are sometimes useful when building functors.
lemma mk_obj {V W : Type*} [Quiver V] [Quiver W] {obj : V → W} {map} {X : V} :
    (Prefunctor.mk obj map).obj X = obj X := rfl

lemma mk_map {V W : Type*} [Quiver V] [Quiver W] {obj : V → W} {map} {X Y : V} {f : X ⟶ Y} :
    (Prefunctor.mk obj map).map f = map f := rfl

@[ext (iff := false)]
theorem ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  obtain ⟨F_obj, _⟩ := F
  obtain ⟨G_obj, _⟩ := G
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f

/-- This may be a more useful form of `Prefunctor.ext`. -/
theorem ext' {V W : Type u} [Quiver V] [Quiver W] {F G : Prefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Quiver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm) : F = G := by
  obtain ⟨Fobj, Fmap⟩ := F
  obtain ⟨Gobj, Gmap⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext X Y f
  simpa only [Quiver.homOfEq_rfl] using h_map X Y f

/-- The identity morphism between quivers. -/
@[simps]
def id (V : Type*) [Quiver V] : Prefunctor V V where
  obj := fun X => X
  map f := f

instance (V : Type*) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

/-- Composition of morphisms between quivers. -/
@[simps]
def comp {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W]
    (F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

@[simp]
theorem comp_id {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    F.comp (id _) = F := rfl

@[simp]
theorem id_comp {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    (id _).comp F = F := rfl

@[simp]
theorem comp_assoc {U V W Z : Type*} [Quiver U] [Quiver V] [Quiver W] [Quiver Z]
    (F : Prefunctor U V) (G : Prefunctor V W) (H : Prefunctor W Z) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  rfl

/-- Notation for a prefunctor between quivers. -/
infixl:50 " ⥤q " => Prefunctor

/-- Notation for composition of prefunctors. -/
infixl:60 " ⋙q " => Prefunctor.comp

/-- Notation for the identity prefunctor on a quiver. -/
notation "𝟭q" => id

theorem congr_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
    (h : f = g) : F.map f = F.map g := by
  rw [h]

/-- An equality of prefunctors gives an equality on objects. -/
theorem congr_obj {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) (X : U) :
    F.obj X = G.obj X := by cases e; rfl

/-- An equality of prefunctors gives an equality on homs. -/
theorem congr_hom {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) {X Y : U}
    (f : X ⟶ Y) : Quiver.homOfEq (F.map f) (congr_obj e X) (congr_obj e Y) = G.map f := by
  subst e
  simp

/-- Prefunctors commute with `homOfEq`. -/
@[simp]
theorem homOfEq_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} (f : X ⟶ Y)
    {X' Y' : U} (hX : X = X') (hY : Y = Y') :
    F.map (Quiver.homOfEq f hX hY) =
      Quiver.homOfEq (F.map f) (congr_arg F.obj hX) (congr_arg F.obj hY) := by subst hX hY; simp

end Prefunctor
