/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Prelax
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Lax functors

A lax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
-- TODO: flip arrows?
* a family of 2-morphisms `F.mapId a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.mapComp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

## Main definitions

* `CategoryTheory.LaxFunctor B C` : an lax functor between bicategories `B` and `C`
* `CategoryTheory.LaxFunctor.comp F G` : the composition of lax functors
* PSEUDOCORE

## Future work

Some constructions in the Bicategory library have only been done in terms of lax functors,
since Lax functors had not yet been added (e.g `FunctorBicategory.lean`).


Possible future work would

-/

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- A lax functor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` do not need to strictly commute with the composition,
and do not need to strictly preserve the identity. Instead, there are specified 2-morphisms
`𝟙 (F.obj a) ⟶ F.map (𝟙 a)` and `F.map f ≫ F.map g ⟶ F.map (f ≫ g)`.

`F.map₂` strictly commute with compositions and preserve the identity. They also preserve the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
structure LaxFunctor (B: Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  mapId (a : B) : 𝟙 (obj a) ⟶ map (𝟙 a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map f ≫ map g ⟶ map (f ≫ g)
  mapComp_naturality_left :
    ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g:= by aesop_cat
  mapComp_naturality_right :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
     mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g' := by aesop_cat
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom =
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫ mapComp f (g ≫ h) := by aesop_cat
  map₂_leftUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).inv = (λ_ (map f)).inv ≫ mapId a ▷ map f ≫ mapComp (𝟙 a) f := by aesop_cat
      -- mapId a ▷ map f ≫ mapComp (𝟙 a) f ≫ map₂ (λ_ f).hom = (λ_ (map f)).hom := by aesop_cat
  map₂_rightUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).inv = (ρ_ (map f)).inv ≫ map f ◁ mapId b ≫ mapComp f (𝟙 b) := by aesop_cat

initialize_simps_projections LaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace LaxFunctor

attribute [reassoc (attr := simp)]
  mapComp_naturality_left mapComp_naturality_right map₂_associator

-- the simpNF linter complains that `map₂_leftUnitor_assoc` etc can be
-- proved with `simp` so I move them here
attribute [reassoc] map₂_leftUnitor map₂_rightUnitor
attribute [simp] map₂_leftUnitor map₂_rightUnitor

/-- The underlying prelax functor. -/
add_decl_doc LaxFunctor.toPrelaxFunctor

attribute [nolint docBlame] CategoryTheory.LaxFunctor.mapId
  CategoryTheory.LaxFunctor.mapComp
  CategoryTheory.LaxFunctor.mapComp_naturality_left
  CategoryTheory.LaxFunctor.mapComp_naturality_right
  CategoryTheory.LaxFunctor.map₂_associator
  CategoryTheory.LaxFunctor.map₂_leftUnitor
  CategoryTheory.LaxFunctor.map₂_rightUnitor

instance hasCoeToPrelax : Coe (LaxFunctor B C) (PrelaxFunctor B C) :=
  ⟨toPrelaxFunctor⟩

variable (F : LaxFunctor B C)

/-- The identity lax functor. -/
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : LaxFunctor B B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => 𝟙 (𝟙 a)
  mapComp := fun f g => 𝟙 (f ≫ g)

instance : Inhabited (LaxFunctor B B) :=
  ⟨id B⟩

/-- Composition of lax functors. -/
-- @[simps]
def comp {D : Type u₃} [Bicategory.{w₃, v₃} D] (F : LaxFunctor B C) (G : LaxFunctor C D) :
    LaxFunctor B D where
  toPrelaxFunctor := PrelaxFunctor.comp F.toPrelaxFunctor G.toPrelaxFunctor
  mapId := fun a => G.mapId (F.obj a) ≫ G.map₂ (F.mapId a)
  mapComp := fun f g => G.mapComp (F.map f) (F.map g) ≫ G.map₂ (F.mapComp f g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [assoc, ← G.map₂_comp, mapComp_naturality_left, G.map₂_comp, mapComp_naturality_left_assoc]
  mapComp_naturality_right := fun f _ _ η => by
    dsimp
    rw [assoc, ← G.map₂_comp, mapComp_naturality_right, G.map₂_comp, mapComp_naturality_right_assoc]
  -- TODO: this proof might be easier if map₂_assoc is arranged better...
  map₂_associator := fun f g h => by
    dsimp
    slice_rhs 1 3 =>
      rw [whiskerLeft_comp, assoc, ← mapComp_naturality_right]
      rw [← map₂_associator_assoc]
    slice_rhs 3 5 =>
      rw [← G.map₂_comp, ← G.map₂_comp]
      rw [← F.map₂_associator]
      rw [G.map₂_comp, G.map₂_comp]
    slice_lhs 1 3 =>
      rw [comp_whiskerRight, assoc, ← G.mapComp_naturality_left_assoc]
    simp only [assoc]
  map₂_leftUnitor := fun f => by
    dsimp
    simp only [map₂_leftUnitor, PrelaxFunctor.map₂_comp, assoc, mapComp_naturality_left_assoc,
      comp_whiskerRight]
  map₂_rightUnitor := fun f => by
    dsimp
    simp only [map₂_rightUnitor, PrelaxFunctor.map₂_comp, assoc, mapComp_naturality_right_assoc,
      whiskerLeft_comp]

/-- A structure on an Lax functor that promotes an Lax functor to a pseudofunctor.
See `Pseudofunctor.mkOfLax` (TODO).
-/
structure PseudoCore (F : LaxFunctor B C) where
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  mapIdIso_inv {a : B} : (mapIdIso a).inv = F.mapId a := by aesop_cat
  mapCompIso_inv {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : (mapCompIso f g).inv = F.mapComp f g := by
    aesop_cat

attribute [nolint docBlame] CategoryTheory.LaxFunctor.PseudoCore.mapIdIso
  CategoryTheory.LaxFunctor.PseudoCore.mapCompIso
  CategoryTheory.LaxFunctor.PseudoCore.mapIdIso_inv
  CategoryTheory.LaxFunctor.PseudoCore.mapCompIso_inv

attribute [simp] PseudoCore.mapIdIso_inv PseudoCore.mapCompIso_inv

end LaxFunctor

-- Later: associator API
