/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary

/-!
# Strict pseudofunctors

In this file we introduce the notion of strict pseudofunctors, which are pseudofunctors such
that `mapId` and `mapComp` are given by `eqToIso _`.

We implement this notion as a typeclass, `Pseudofunctor.IsStrict`.

To a strict pseudofunctor between strict bicategories we can associate a functor between the
underlying categories, see `Pseudofunctor.toFunctor`.

-/

namespace CategoryTheory

open Bicategory

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D]

variable (B C)

/-- A strict pseudofunctor `F` between bicategories `B` and `C` is a
pseudofunctor `F` from `B` to `C` such that `mapId` and `mapComp` are given by `eqToIso _`. -/
structure StrictPseudofunctor extends StrictlyUnitaryPseudofunctor B C where
  map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) = map f ≫ map g := by
    cat_disch
  mapComp_eq_eqToIso : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
    mapComp f g = eqToIso (map_comp f g) := by cat_disch

/-- A helper structure that bundles the necessary data to
construct a `StrictPseudofunctor` without specifying the redundant
fields `mapId` and `mapComp`. -/
structure StrictPseudofunctorCore extends PrelaxFunctor B C where
  map_id (X : B) : map (𝟙 X) = 𝟙 (obj X)
  map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) = map f ≫ map g := by
    cat_disch
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
      map₂ (f ◁ η) = eqToHom (map_comp f g) ≫
        map f ◁ map₂ η ≫ eqToHom (map_comp f g').symm := by cat_disch
  map₂_whisker_right :
      ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
        map₂ (η ▷ g) = eqToHom (map_comp f g) ≫
          map₂ η ▷ map g ≫ eqToHom (map_comp f' g).symm := by cat_disch
  map₂_left_unitor :
      ∀ {a b : B} (f : a ⟶ b),
        map₂ (λ_ f).hom =
        eqToHom (by rw [map_comp (𝟙 a) f, map_id a]) ≫
          (λ_ (map f)).hom := by
    cat_disch
  map₂_right_unitor :
      ∀ {a b : B} (f : a ⟶ b),
        map₂ (ρ_ f).hom =
         eqToHom (by rw [map_comp f (𝟙 b), map_id b]) ≫
          (ρ_ (map f)).hom := by
    cat_disch
  map₂_associator :
      ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
        map₂ (α_ f g h).hom = eqToHom (by simp only [map_comp]) ≫
          (α_ (map f) (map g) (map h)).hom ≫ eqToHom (by simp only [map_comp]) := by
    cat_disch

namespace StrictPseudofunctor

variable {B C}

/-- An alternate constructor for strictly unitary lax functors that does not
require the `mapId` fields, and that adapts the `map₂_leftUnitor` and
`map₂_rightUnitor` to the fact that the functor is strictly unitary. -/
@[simps]
def mk' (S : StrictPseudofunctorCore B C) : StrictPseudofunctor B C where
  obj := S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToIso (S.map_id x)
  mapId_eq_eqToIso x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  map_comp := S.map_comp
  mapComp f g := eqToIso <| S.map_comp f g
  map₂_left_unitor f := by
    simpa using S.map₂_left_unitor f
  map₂_right_unitor f := by
    simpa using S.map₂_right_unitor f
  map₂_associator f g h := by
    simpa using S.map₂_associator f g h
  map₂_whisker_left f _ _ η := by
    simpa using S.map₂_whisker_left f η
  map₂_whisker_right η f := by
    simpa using S.map₂_whisker_right η f

section

variable (F : StrictPseudofunctor B C)

variable (B) in
/-- The identity `StrictPseudofunctor`. -/
@[simps!]
def id : StrictPseudofunctor B B where
  __ := StrictlyUnitaryPseudofunctor.id B

/-- Composition of `StrictPseudofunctor`. -/
@[simps!]
def comp (F : StrictPseudofunctor B C)
    (G : StrictPseudofunctor C D) :
    StrictPseudofunctor B D where
  __ := StrictlyUnitaryPseudofunctor.comp
    F.toStrictlyUnitaryPseudofunctor G.toStrictlyUnitaryPseudofunctor
  map_comp _ := by simp [StrictPseudofunctor.map_comp]
  mapComp_eq_eqToIso _ _ := by
    ext
    simp [StrictPseudofunctor.mapComp_eq_eqToIso,
      PrelaxFunctor.map₂_eqToHom]

end

section

variable [Strict B] [Strict C]

/-- A strict pseudofunctor between strict bicategories induces a functor on the underlying
categories. -/
def toFunctor (F : StrictPseudofunctor B C) : Functor B C where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

end

end StrictPseudofunctor

end CategoryTheory
