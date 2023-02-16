/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno

! This file was ported from Lean 3 source module category_theory.bicategory.functor
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Oplax functors and pseudofunctors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.map_id a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.map_comp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

A pseudofunctor is an oplax functor whose `map_id` and `map_comp` are isomorphisms. We provide
several constructors for pseudofunctors:
* `pseudofunctor.mk` : the default constructor, which requires `map₂_whiskerLeft` and
  `map₂_whiskerRight` instead of naturality of `map_comp`.
* `pseudofunctor.mk_of_oplax` : construct a pseudofunctor from an oplax functor whose
  `map_id` and `map_comp` are isomorphisms. This constructor uses `iso` to describe isomorphisms.
* `pseudofunctor.mk_of_oplax'` : similar to `mk_of_oplax`, but uses `is_iso` to describe
  isomorphisms.

The additional constructors are useful when constructing a pseudofunctor where the construction
of the oplax functor associated with it is already done. For example, the composition of
pseudofunctors can be defined by using the composition of oplax functors as follows:
```lean
def pseudofunctor.comp (F : pseudofunctor B C) (G : pseudofunctor C D) : pseudofunctor B D :=
mk_of_oplax ((F : oplax_functor B C).comp G)
{ map_id_iso := λ a, (G.map_functor _ _).map_iso (F.map_id a) ≪≫ G.map_id (F.obj a),
  map_comp_iso := λ a b c f g,
    (G.map_functor _ _).map_iso (F.map_comp f g) ≪≫ G.map_comp (F.map f) (F.map g) }
```
although the composition of pseudofunctors in this file is defined by using the default constructor
because `obviously` is smart enough. Similarly, the composition is also defined by using
`mk_of_oplax'` after giving appropriate instances for `is_iso`. The former constructor
`mk_of_oplax` requires isomorphisms as data type `iso`, and so it is useful if you don't want
to forget the definitions of the inverses. On the other hand, the latter constructor
`mk_of_oplax'` is useful if you want to use propositional type class `is_iso`.

## Main definitions

* `category_theory.oplax_functor B C` : an oplax functor between bicategories `B` and `C`
* `category_theory.oplax_functor.comp F G` : the composition of oplax functors
* `category_theory.pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`
* `category_theory.pseudofunctor.comp F G` : the composition of pseudofunctors

## Future work

There are two types of functors between bicategories, called lax and oplax functors, depending on
the directions of `map_id` and `map_comp`. We may need both in mathlib in the future, but for
now we only define oplax functors.
-/


namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable {B : Type u₁} [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]

variable {C : Type u₂} [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)]

variable {D : Type u₃} [Quiver.{v₃ + 1} D] [∀ a b : D, Quiver.{w₃ + 1} (a ⟶ b)]

/-- A prelax functor between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `oplax_functor`.
-/
structure PrelaxFunctor (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]
  (C : Type u₂) [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)] extends
  Prefunctor B C where
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)
#align category_theory.prelax_functor CategoryTheory.PrelaxFunctor

/-- The prefunctor between the underlying quivers. -/
add_decl_doc PrelaxFunctor.toPrefunctor

namespace PrelaxFunctor

attribute [coe] CategoryTheory.PrelaxFunctor.toPrefunctor

instance hasCoeToPrefunctor : Coe (PrelaxFunctor B C) (Prefunctor B C) :=
  ⟨toPrefunctor⟩
#align category_theory.prelax_functor.has_coe_to_prefunctor CategoryTheory.PrelaxFunctor.hasCoeToPrefunctor

variable (F : PrelaxFunctor B C)

-- porting note: deleted syntactic tautologies `toPrefunctor_eq_coe : F.toPrefunctor = F`
-- and `to_prefunctor_obj : (F : Prefunctor B C).obj = F.obj`
-- and `to_prefunctor_map`
#noalign category_theory.prelax_functor.to_prefunctor_eq_coe
#noalign category_theory.prelax_functor.to_prefunctor_obj
#noalign category_theory.prelax_functor.to_prefunctor_map

/-- The identity prelax functor. -/
@[simps]
def id (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)] : PrelaxFunctor B B :=
  { Prefunctor.id B with map₂ := fun η => η }
#align category_theory.prelax_functor.id CategoryTheory.PrelaxFunctor.id

instance : Inhabited (PrelaxFunctor B B) :=
  ⟨PrelaxFunctor.id B⟩

-- porting note: `by exact` was not necessary in mathlib3
/-- Composition of prelax functors. -/
@[simps]
def comp (F : PrelaxFunctor B C) (G : PrelaxFunctor C D) : PrelaxFunctor B D :=
  { (F : Prefunctor B C).comp ↑G with map₂ := fun η => by exact G.map₂ (F.map₂ η) }
#align category_theory.prelax_functor.comp CategoryTheory.PrelaxFunctor.comp

end PrelaxFunctor

end

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/-
We use this auxiliary definition instead of writing it directly in the definition
of oplax functors because doing so will cause a timeout.
-/
/-- This auxiliary definition states that oplax functors preserve the associators
modulo some adjustments of domains and codomains of 2-morphisms.
-/
@[simp]
def OplaxFunctor.Map₂AssociatorAux (obj : B → C) (map : ∀ {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (map₂ : ∀ {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
    (map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ⟶ map f ≫ map g) {a b c d : B}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : Prop :=
  map₂ (α_ f g h).hom ≫ map_comp f (g ≫ h) ≫ map f ◁ map_comp g h =
    map_comp (f ≫ g) h ≫ map_comp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom
#align category_theory.oplax_functor.map₂_associator_aux CategoryTheory.OplaxFunctor.Map₂AssociatorAux

/-- An oplax functor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` do not need to strictly commute with the composition,
and do not need to strictly preserve the identity. Instead, there are specified 2-morphisms
`F.map (𝟙 a) ⟶ 𝟙 (F.obj a)` and `F.map (f ≫ g) ⟶ F.map f ≫ F.map g`.

`F.map₂` strictly commute with compositions and preserve the identity. They also preserve the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
structure OplaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  mapId (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g
  mapComp_naturality_left :
    ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      map₂ (η ▷ g) ≫ mapComp f' g = mapComp f g ≫ map₂ η ▷ map g := by
    aesop
  mapComp_naturality_right :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
      map₂ (f ◁ η) ≫ mapComp f g' = mapComp f g ≫ map f ◁ map₂ η := by
    aesop
  map₂_id : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by aesop
  map₂_comp :
    ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    aesop
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      OplaxFunctor.Map₂AssociatorAux obj map map₂ map_comp f g h := by
    aesop
  map₂_leftUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = mapComp (𝟙 a) f ≫ mapId a ▷ map f ≫ (λ_ (map f)).hom := by
    aesop
  map₂_rightUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = mapComp f (𝟙 b) ≫ map f ◁ mapId b ≫ (ρ_ (map f)).hom := by
    aesop
#align category_theory.oplax_functor CategoryTheory.OplaxFunctor
#align category_theory.oplax_functor.map_id CategoryTheory.OplaxFunctor.mapId
#align category_theory.oplax_functor.map_comp CategoryTheory.OplaxFunctor.mapComp
#align category_theory.oplax_functor.map_comp_naturality_left' CategoryTheory.OplaxFunctor.mapComp_naturality_left
#align category_theory.oplax_functor.map_comp_naturality_left CategoryTheory.OplaxFunctor.mapComp_naturality_left
#align category_theory.oplax_functor.map_comp_naturality_right' CategoryTheory.OplaxFunctor.mapComp_naturality_right
#align category_theory.oplax_functor.map_comp_naturality_right CategoryTheory.OplaxFunctor.mapComp_naturality_right
#align category_theory.oplax_functor.map₂_id' CategoryTheory.OplaxFunctor.map₂_id
#align category_theory.oplax_functor.map₂_comp' CategoryTheory.OplaxFunctor.map₂_comp
#align category_theory.oplax_functor.map₂_associator' CategoryTheory.OplaxFunctor.map₂_associator
#align category_theory.oplax_functor.map₂_left_unitor CategoryTheory.OplaxFunctor.map₂_leftUnitor
#align category_theory.oplax_functor.map₂_left_unitor' CategoryTheory.OplaxFunctor.map₂_leftUnitor
#align category_theory.oplax_functor.map₂_right_unitor CategoryTheory.OplaxFunctor.map₂_rightUnitor
#align category_theory.oplax_functor.map₂_right_unitor' CategoryTheory.OplaxFunctor.map₂_rightUnitor


namespace OplaxFunctor

/- Porting note: removed primes from field names and remove `restate_axiom` since 
that is no longer needed in Lean 4 -/

attribute [simp] mapComp_naturality_left mapComp_naturality_right map₂_id map₂_associator

-- porting note: was auto-ported as `attribute [reassoc.1]` for some reason
attribute [reassoc (attr := simp)] -- can't stop this being noisy
  mapComp_naturality_left mapComp_naturality_right map₂_comp map₂_leftUnitor map₂_rightUnitor

-- porting note: reassoc on the previous line would not mark these as simp;
-- error was
/-
CategoryTheory.OplaxFunctor.map₂_associator and CategoryTheory.OplaxFunctor.map₂_associator_assoc
do not generate the same number of simp lemmas.

-/
attribute [reassoc] map₂_associator -- can't stop this being noisy
attribute [simp] map₂_associator_assoc

attribute [simp] map₂_comp map₂_leftUnitor map₂_rightUnitor

section

/-- The prelax functor between the underlying quivers. -/
add_decl_doc OplaxFunctor.toPrelaxFunctor

instance hasCoeToPrelax : Coe (OplaxFunctor B C) (PrelaxFunctor B C) :=
  ⟨toPrelaxFunctor⟩
#align category_theory.oplax_functor.has_coe_to_prelax CategoryTheory.OplaxFunctor.hasCoeToPrelax

variable (F : OplaxFunctor B C)

@[simp]
theorem to_prelax_eq_coe : F.toPrelaxFunctor = F :=
  rfl
#align category_theory.oplax_functor.to_prelax_eq_coe CategoryTheory.OplaxFunctor.to_prelax_eq_coe

@[simp]
theorem to_prelaxFunctor_obj : (F : PrelaxFunctor B C).obj = F.obj :=
  rfl
#align category_theory.oplax_functor.to_prelax_functor_obj CategoryTheory.OplaxFunctor.to_prelaxFunctor_obj

--porting note: removed `to_prelaxFunctor_map` relating the now
-- nonexistent `PrelaxFunctor.map` and `OplaxFunctor.map`
#noalign CategoryTheory.OplaxFunctor.to_prelaxFunctor_map

--porting note: removed `to_prelaxFunctor_map₂` relating
-- `PrelaxFunctor.map₂` to nonexistent `OplaxFunctor.map₂`
#noalign category_theory.oplax_functor.to_prelax_functor_map₂

/-- Function between 1-morphisms as a functor. -/
@[simps]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b)
    where
  obj f := F.map f
  map η := F.map₂ η
#align category_theory.oplax_functor.map_functor CategoryTheory.OplaxFunctor.mapFunctor

/-- The identity oplax functor. -/
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : OplaxFunctor B B :=
  { PrelaxFunctor.id B with
    mapId := fun a => 𝟙 (𝟙 a)
    mapComp := fun f g => 𝟙 (f ≫ g)
    map₂_associator := sorry 
  }
#align category_theory.oplax_functor.id CategoryTheory.OplaxFunctor.id

instance : Inhabited (OplaxFunctor B B) :=
  ⟨id B⟩

/-- Composition of oplax functors. -/
--@[simps]
def comp (F : OplaxFunctor B C) (G : OplaxFunctor C D) : OplaxFunctor B D :=
  {
    (F : PrelaxFunctor B C).comp G with
    mapId := fun a => by exact (G.mapFunctor _ _).map (F.mapId a) ≫ G.mapId (F.obj a)
    mapComp := fun f g => by
      exact (G.mapFunctor _ _).map (F.mapComp f g) ≫ G.mapComp (F.map f) (F.map g)
    mapComp_naturality_left := fun η g =>
      by
      dsimp
      rw [← map₂_comp_assoc, mapComp_naturality_left, map₂_comp_assoc, mapComp_naturality_left,
        assoc]
    mapComp_naturality_right := fun η =>
      by 
      dsimp
      intros
      rw [← map₂_comp_assoc, mapComp_naturality_right, map₂_comp_assoc, mapComp_naturality_right,
        assoc]
    map₂_associator := fun f g h => by
      -- ⊢ map₂_associator_aux (↑F.comp ↑G).obj ... (complicated)
      dsimp
      /- Lean 3 goal now

      G.map₂ (F.map₂ (α_ f g h).hom) ≫
    (G.map₂ (F.map_comp f (g ≫ h)) ≫ G.map_comp (F.map f) (F.map (g ≫ h))) ≫
      G.map (F.map f) ◁ (G.map₂ (F.map_comp g h) ≫ G.map_comp (F.map g) (F.map h)) =
  (G.map₂ (F.map_comp (f ≫ g) h) ≫ G.map_comp (F.map (f ≫ g)) (F.map h)) ≫
    (G.map₂ (F.map_comp f g) ≫ G.map_comp (F.map f) (F.map g)) ▷ G.map (F.map h) ≫
      (α_ (G.map (F.map f)) (G.map (F.map g)) (G.map (F.map h))).hom

      but Lean 4 still a mess
      -/
      simp only [map₂_associator, ← map₂_comp_assoc, ← mapComp_naturality_right_assoc,
        whiskerLeft_comp, assoc]
      simp only [map₂_associator, map₂_comp, mapComp_naturality_left_assoc, comp_whiskerRight,
        assoc]
      dsimp
      simp
      sorry
    map₂_leftUnitor := fun f => by
      dsimp
      simp only [map₂_leftUnitor, map₂_comp, mapComp_naturality_left_assoc, comp_whiskerRight,
        assoc]
    map₂_rightUnitor := fun f => by
      dsimp
      simp only [map₂_rightUnitor, map₂_comp, mapComp_naturality_right_assoc, whiskerLeft_comp,
        assoc] }
  #exit
    map_comp := fun f g =>
      (G.mapFunctor _ _).map (F.map_comp f g) ≫ G.map_comp (F.map f) (F.map g)
    mapComp_naturality_left := fun a b c f f' η g =>
      by
      dsimp
      rw [← map₂_comp_assoc, map_comp_naturality_left, map₂_comp_assoc, map_comp_naturality_left,
        assoc]
    mapComp_naturality_right' := fun a b c f g g' η =>
      by
      dsimp
      rw [← map₂_comp_assoc, map_comp_naturality_right, map₂_comp_assoc, map_comp_naturality_right,
        assoc]
    map₂_associator' := fun a b c d f g h => by
      dsimp
      simp only [map₂_associator, ← map₂_comp_assoc, ← map_comp_naturality_right_assoc,
        whiskerLeft_comp, assoc]
      simp only [map₂_associator, map₂_comp, map_comp_naturality_left_assoc, comp_whiskerRight,
        assoc]
    map₂_left_unitor' := fun a b f => by
      dsimp
      simp only [map₂_left_unitor, map₂_comp, map_comp_naturality_left_assoc, comp_whiskerRight,
        assoc]
    map₂_right_unitor' := fun a b f => by
      dsimp
      simp only [map₂_right_unitor, map₂_comp, map_comp_naturality_right_assoc, whiskerLeft_comp,
        assoc] }

#exit
#align category_theory.oplax_functor.comp CategoryTheory.OplaxFunctor.comp

/-- A structure on an oplax functor that promotes an oplax functor to a pseudofunctor.
See `pseudofunctor.mk_of_oplax`.
-/
@[nolint has_nonempty_instance]
structure PseudoCore (F : OplaxFunctor B C) where
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  mapIdIso_hom' : ∀ {a : B}, (map_id_iso a).Hom = F.map_id a := by obviously
  mapCompIso_hom' :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), (map_comp_iso f g).Hom = F.map_comp f g := by obviously
#align category_theory.oplax_functor.pseudo_core CategoryTheory.OplaxFunctor.PseudoCore

restate_axiom pseudo_core.map_id_iso_hom'

restate_axiom pseudo_core.map_comp_iso_hom'

attribute [simp] pseudo_core.map_id_iso_hom pseudo_core.map_comp_iso_hom

end

end OplaxFunctor

/-
We use this auxiliary definition instead of writing it directly in the definition
of pseudofunctors because doing so will cause a timeout.
-/
/-- This auxiliary definition states that pseudofunctors preserve the associators
modulo some adjustments of domains and codomains of 2-morphisms.
-/
@[simp]
def Pseudofunctor.Map₂AssociatorAux (obj : B → C) (map : ∀ {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (map₂ : ∀ {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
    (map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ≅ map f ≫ map g) {a b c d : B}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : Prop :=
  map₂ (α_ f g h).Hom =
    (map_comp (f ≫ g) h).Hom ≫
      (map_comp f g).Hom ▷ map h ≫
        (α_ (map f) (map g) (map h)).Hom ≫ map f ◁ (map_comp g h).inv ≫ (map_comp f (g ≫ h)).inv
#align category_theory.pseudofunctor.map₂_associator_aux CategoryTheory.Pseudofunctor.Map₂AssociatorAux

/-- A pseudofunctor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` do not need to strictly commute with the compositions,
and do not need to strictly preserve the identity. Instead, there are specified 2-isomorphisms
`F.map (𝟙 a) ≅ 𝟙 (F.obj a)` and `F.map (f ≫ g) ≅ F.map f ≫ F.map g`.

`F.map₂` strictly commute with compositions and preserve the identity. They also preserve the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
structure Pseudofunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  map_id (a : B) : map (𝟙 a) ≅ 𝟙 (obj a)
  map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g
  map₂_id' : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by obviously
  map₂_comp' :
    ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    obviously
  map₂_whisker_left' :
    ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) = (map_comp f g).Hom ≫ map f ◁ map₂ η ≫ (map_comp f h).inv := by
    obviously
  map₂_whisker_right' :
    ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) = (map_comp f h).Hom ≫ map₂ η ▷ map h ≫ (map_comp g h).inv := by
    obviously
  map₂_associator' :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      Pseudofunctor.Map₂AssociatorAux obj (fun a b => map) (fun a b f g => map₂)
        (fun a b c => map_comp) f g h := by
    obviously
  map₂_left_unitor' :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).Hom = (map_comp (𝟙 a) f).Hom ≫ (map_id a).Hom ▷ map f ≫ (λ_ (map f)).Hom := by
    obviously
  map₂_right_unitor' :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).Hom = (map_comp f (𝟙 b)).Hom ≫ map f ◁ (map_id b).Hom ≫ (ρ_ (map f)).Hom := by
    obviously
#align category_theory.pseudofunctor CategoryTheory.Pseudofunctor

namespace Pseudofunctor

restate_axiom map₂_id'

restate_axiom map₂_comp'

restate_axiom map₂_whisker_left'

restate_axiom map₂_whisker_right'

restate_axiom map₂_associator'

restate_axiom map₂_left_unitor'

restate_axiom map₂_right_unitor'

attribute [reassoc.1]
  map₂_comp map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor

attribute [simp]
  map₂_id map₂_comp map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor

section

open Iso

/-- The prelax functor between the underlying quivers. -/
add_decl_doc pseudofunctor.to_prelax_functor

instance hasCoeToPrelaxFunctor : Coe (Pseudofunctor B C) (PrelaxFunctor B C) :=
  ⟨toPrelaxFunctor⟩
#align category_theory.pseudofunctor.has_coe_to_prelax_functor CategoryTheory.Pseudofunctor.hasCoeToPrelaxFunctor

variable (F : Pseudofunctor B C)

@[simp]
theorem toPrelaxFunctor_eq_coe : F.toPrelaxFunctor = F :=
  rfl
#align category_theory.pseudofunctor.to_prelax_functor_eq_coe CategoryTheory.Pseudofunctor.toPrelaxFunctor_eq_coe

@[simp]
theorem to_prelaxFunctor_obj : (F : PrelaxFunctor B C).obj = F.obj :=
  rfl
#align category_theory.pseudofunctor.to_prelax_functor_obj CategoryTheory.Pseudofunctor.to_prelaxFunctor_obj

@[simp]
theorem to_prelaxFunctor_map : @PrelaxFunctor.map B _ _ C _ _ F = @map _ _ _ _ F :=
  rfl
#align category_theory.pseudofunctor.to_prelax_functor_map CategoryTheory.Pseudofunctor.to_prelaxFunctor_map

@[simp]
theorem to_prelaxFunctor_map₂ : @PrelaxFunctor.map₂ B _ _ C _ _ F = @map₂ _ _ _ _ F :=
  rfl
#align category_theory.pseudofunctor.to_prelax_functor_map₂ CategoryTheory.Pseudofunctor.to_prelaxFunctor_map₂

/-- The oplax functor associated with a pseudofunctor. -/
def toOplax : OplaxFunctor B C :=
  { (F : PrelaxFunctor B C) with
    map_id := fun a => (F.map_id a).Hom
    map_comp := fun a b c f g => (F.map_comp f g).Hom }
#align category_theory.pseudofunctor.to_oplax CategoryTheory.Pseudofunctor.toOplax

instance hasCoeToOplax : Coe (Pseudofunctor B C) (OplaxFunctor B C) :=
  ⟨toOplax⟩
#align category_theory.pseudofunctor.has_coe_to_oplax CategoryTheory.Pseudofunctor.hasCoeToOplax

@[simp]
theorem toOplax_eq_coe : F.toOplax = F :=
  rfl
#align category_theory.pseudofunctor.to_oplax_eq_coe CategoryTheory.Pseudofunctor.toOplax_eq_coe

@[simp]
theorem to_oplax_obj : (F : OplaxFunctor B C).obj = F.obj :=
  rfl
#align category_theory.pseudofunctor.to_oplax_obj CategoryTheory.Pseudofunctor.to_oplax_obj

@[simp]
theorem to_oplax_map : @OplaxFunctor.map B _ C _ F = @map _ _ _ _ F :=
  rfl
#align category_theory.pseudofunctor.to_oplax_map CategoryTheory.Pseudofunctor.to_oplax_map

@[simp]
theorem to_oplax_map₂ : @OplaxFunctor.map₂ B _ C _ F = @map₂ _ _ _ _ F :=
  rfl
#align category_theory.pseudofunctor.to_oplax_map₂ CategoryTheory.Pseudofunctor.to_oplax_map₂

@[simp]
theorem to_oplax_mapId (a : B) : (F : OplaxFunctor B C).map_id a = (F.map_id a).Hom :=
  rfl
#align category_theory.pseudofunctor.to_oplax_map_id CategoryTheory.Pseudofunctor.to_oplax_mapId

@[simp]
theorem to_oplax_mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (F : OplaxFunctor B C).map_comp f g = (F.map_comp f g).Hom :=
  rfl
#align category_theory.pseudofunctor.to_oplax_map_comp CategoryTheory.Pseudofunctor.to_oplax_mapComp

/-- Function on 1-morphisms as a functor. -/
@[simps]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) :=
  (F : OplaxFunctor B C).mapFunctor a b
#align category_theory.pseudofunctor.map_functor CategoryTheory.Pseudofunctor.mapFunctor

/-- The identity pseudofunctor. -/
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : Pseudofunctor B B :=
  { PrelaxFunctor.id B with
    map_id := fun a => Iso.refl (𝟙 a)
    map_comp := fun a b c f g => Iso.refl (f ≫ g) }
#align category_theory.pseudofunctor.id CategoryTheory.Pseudofunctor.id

instance : Inhabited (Pseudofunctor B B) :=
  ⟨id B⟩

/-- Composition of pseudofunctors. -/
@[simps]
def comp (F : Pseudofunctor B C) (G : Pseudofunctor C D) : Pseudofunctor B D :=
  {
    (F : PrelaxFunctor B C).comp
      ↑G with
    map_id := fun a => (G.mapFunctor _ _).mapIso (F.map_id a) ≪≫ G.map_id (F.obj a)
    map_comp := fun a b c f g =>
      (G.mapFunctor _ _).mapIso (F.map_comp f g) ≪≫ G.map_comp (F.map f) (F.map g) }
#align category_theory.pseudofunctor.comp CategoryTheory.Pseudofunctor.comp

/-- Construct a pseudofunctor from an oplax functor whose `map_id` and `map_comp` are isomorphisms.
-/
@[simps]
def mkOfOplax (F : OplaxFunctor B C) (F' : F.PseudoCore) : Pseudofunctor B C :=
  { (F : PrelaxFunctor B C) with
    map_id := F'.mapIdIso
    map_comp := fun _ _ _ => F'.mapCompIso
    map₂_whisker_left' := fun a b c f g h η => by
      dsimp
      rw [F'.map_comp_iso_hom f g, ← F.map_comp_naturality_right_assoc, ← F'.map_comp_iso_hom f h,
        hom_inv_id, comp_id]
    map₂_whisker_right' := fun a b c f g η h => by
      dsimp
      rw [F'.map_comp_iso_hom f h, ← F.map_comp_naturality_left_assoc, ← F'.map_comp_iso_hom g h,
        hom_inv_id, comp_id]
    map₂_associator' := fun a b c d f g h => by
      dsimp
      rw [F'.map_comp_iso_hom (f ≫ g) h, F'.map_comp_iso_hom f g, ← F.map₂_associator_assoc, ←
        F'.map_comp_iso_hom f (g ≫ h), ← F'.map_comp_iso_hom g h, hom_inv_whisker_left_assoc,
        hom_inv_id, comp_id] }
#align category_theory.pseudofunctor.mk_of_oplax CategoryTheory.Pseudofunctor.mkOfOplax

/-- Construct a pseudofunctor from an oplax functor whose `map_id` and `map_comp` are isomorphisms.
-/
@[simps]
noncomputable def mkOfOplax' (F : OplaxFunctor B C) [∀ a, IsIso (F.map_id a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.map_comp f g)] : Pseudofunctor B C :=
  { (F : PrelaxFunctor B C) with
    map_id := fun a => asIso (F.map_id a)
    map_comp := fun a b c f g => asIso (F.map_comp f g)
    map₂_whisker_left' := fun a b c f g h η => by
      dsimp
      rw [← assoc, is_iso.eq_comp_inv, F.map_comp_naturality_right]
    map₂_whisker_right' := fun a b c f g η h => by
      dsimp
      rw [← assoc, is_iso.eq_comp_inv, F.map_comp_naturality_left]
    map₂_associator' := fun a b c d f g h => by
      dsimp
      simp only [← assoc]
      rw [is_iso.eq_comp_inv, ← inv_whisker_left, is_iso.eq_comp_inv]
      simp only [assoc, F.map₂_associator] }
#align category_theory.pseudofunctor.mk_of_oplax' CategoryTheory.Pseudofunctor.mkOfOplax'

end

end Pseudofunctor

end

end CategoryTheory
