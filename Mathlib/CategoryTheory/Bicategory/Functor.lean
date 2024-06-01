/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Basic

#align_import category_theory.bicategory.functor from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

/-!
# Oplax functors and pseudofunctors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.mapId a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.mapComp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

A pseudofunctor is an oplax functor whose `mapId` and `mapComp` are isomorphisms. We provide
several constructors for pseudofunctors:
* `Pseudofunctor.mk` : the default constructor, which requires `map₂_whiskerLeft` and
  `map₂_whiskerRight` instead of naturality of `mapComp`.
* `Pseudofunctor.mkOfOplax` : construct a pseudofunctor from an oplax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `pseudofunctor.mkOfOplax'` : similar to `mkOfOplax`, but uses `IsIso` to describe
  isomorphisms.

The additional constructors are useful when constructing a pseudofunctor where the construction
of the oplax functor associated with it is already done. For example, the composition of
pseudofunctors can be defined by using the composition of oplax functors as follows:
```lean
def comp (F : Pseudofunctor B C) (G : Pseudofunctor C D) : Pseudofunctor B D :=
  mkOfOplax ((F : OplaxFunctor B C).comp G)
  { mapIdIso := fun a ↦ (G.mapFunctor _ _).mapIso (F.mapId a) ≪≫ G.mapId (F.obj a),
    mapCompIso := fun f g ↦
      (G.mapFunctor _ _).mapIso (F.mapComp f g) ≪≫ G.mapComp (F.map f) (F.map g) }
```
although the composition of pseudofunctors in this file is defined by using the default constructor
because `obviously` wasn't smart enough in mathlib3 and the porter of this file was too lazy
to investigate this issue further in mathlib4. Similarly, the composition is also defined by using
`mkOfOplax'` after giving appropriate instances for `IsIso`. The former constructor
`mkOfOplax` requires isomorphisms as data type `Iso`, and so it is useful if you don't want
to forget the definitions of the inverses. On the other hand, the latter constructor
`mkOfOplax'` is useful if you want to use propositional type class `IsIso`.

## Main definitions

* `CategoryTheory.OplaxFunctor B C` : an oplax functor between bicategories `B` and `C`
* `CategoryTheory.OplaxFunctor.comp F G` : the composition of oplax functors
* `CategoryTheory.Pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`
* `CategoryTheory.Pseudofunctor.comp F G` : the composition of pseudofunctors

## Future work

There are two types of functors between bicategories, called lax and oplax functors, depending on
the directions of `mapId` and `mapComp`. We may need both in mathlib in the future, but for
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
1-morphisms, and 2-morphisms. This structure will be extended to define `OplaxFunctor`.
-/
structure PrelaxFunctor (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]
  (C : Type u₂) [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)] extends
  Prefunctor B C where
  /-- The action of a prelax functor on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)
#align category_theory.prelax_functor CategoryTheory.PrelaxFunctor

initialize_simps_projections PrelaxFunctor (+toPrefunctor, -obj, -map)

/-- The prefunctor between the underlying quivers. -/
add_decl_doc PrelaxFunctor.toPrefunctor

namespace PrelaxFunctor

attribute [coe] CategoryTheory.PrelaxFunctor.toPrefunctor

instance hasCoeToPrefunctor : Coe (PrelaxFunctor B C) (Prefunctor B C) :=
  ⟨toPrefunctor⟩
#align category_theory.prelax_functor.has_coe_to_prefunctor CategoryTheory.PrelaxFunctor.hasCoeToPrefunctor

variable (F : PrelaxFunctor B C)

-- Porting note: deleted syntactic tautologies `toPrefunctor_eq_coe : F.toPrefunctor = F`
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

-- Porting note: `by exact` was not necessary in mathlib3
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

-- Porting note: in Lean 3 the below auxiliary definition was only used once, in the definition
-- of oplax functor, with a comment that it had to be used to fix a timeout. The timeout is
-- not present in Lean 4, however Lean 4 is not as good at seeing through the definition,
-- meaning that `simp` wasn't functioning as well as it should. I have hence removed
-- the auxiliary definition.
--@[simp]
--def OplaxFunctor.Map₂AssociatorAux (obj : B → C) (map : ∀ {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
--    (map₂ : ∀ {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
--    (map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ⟶ map f ≫ map g) {a b c d : B}
--    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : Prop := ...

#noalign category_theory.oplax_functor.map₂_associator_aux

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
    aesop_cat
  mapComp_naturality_right :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
      map₂ (f ◁ η) ≫ mapComp f g' = mapComp f g ≫ map f ◁ map₂ η := by
    aesop_cat
  map₂_id : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by aesop
  map₂_comp :
    ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    aesop_cat
  -- Porting note: `map₂_associator_aux` was used here in lean 3, but this was a hack
  -- to avoid a timeout; we revert this hack here (because it was causing other problems
  -- and was not necessary in lean 4)
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h =
    mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom := by
    aesop_cat
  map₂_leftUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = mapComp (𝟙 a) f ≫ mapId a ▷ map f ≫ (λ_ (map f)).hom := by
    aesop_cat
  map₂_rightUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = mapComp f (𝟙 b) ≫ map f ◁ mapId b ≫ (ρ_ (map f)).hom := by
    aesop_cat
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

initialize_simps_projections OplaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace OplaxFunctor

-- Porting note: more stuff was tagged `simp` here in lean 3 but `reassoc (attr := simp)`
-- is doing this job a couple of lines below this.
attribute [simp] map₂_id

attribute [reassoc (attr := simp)]
  mapComp_naturality_left mapComp_naturality_right map₂_associator

-- the simpNF linter complains that `map₂_leftUnitor_assoc` etc can be
-- proved with `simp` so I move them here
attribute [reassoc] map₂_leftUnitor map₂_comp map₂_rightUnitor
attribute [simp] map₂_leftUnitor map₂_comp map₂_rightUnitor
section

/-- The prelax functor between the underlying quivers. -/
add_decl_doc OplaxFunctor.toPrelaxFunctor

attribute [nolint docBlame] CategoryTheory.OplaxFunctor.mapId
  CategoryTheory.OplaxFunctor.mapComp
  CategoryTheory.OplaxFunctor.mapComp_naturality_left
  CategoryTheory.OplaxFunctor.mapComp_naturality_right
  CategoryTheory.OplaxFunctor.map₂_id
  CategoryTheory.OplaxFunctor.map₂_comp
  CategoryTheory.OplaxFunctor.map₂_associator
  CategoryTheory.OplaxFunctor.map₂_leftUnitor
  CategoryTheory.OplaxFunctor.map₂_rightUnitor

instance hasCoeToPrelax : Coe (OplaxFunctor B C) (PrelaxFunctor B C) :=
  ⟨toPrelaxFunctor⟩
#align category_theory.oplax_functor.has_coe_to_prelax CategoryTheory.OplaxFunctor.hasCoeToPrelax

variable (F : OplaxFunctor B C)

-- Porting note: `to_prelax_eq_coe` and `to_prelaxFunctor_obj` are
-- syntactic tautologies in lean 4
#noalign category_theory.oplax_functor.to_prelax_eq_coe
#noalign category_theory.oplax_functor.to_prelax_functor_obj

-- Porting note: removed lemma `to_prelaxFunctor_map` relating the now
-- nonexistent `PrelaxFunctor.map` and `OplaxFunctor.map`
#noalign CategoryTheory.OplaxFunctor.to_prelaxFunctor_map

-- Porting note: removed lemma `to_prelaxFunctor_map₂` relating
-- `PrelaxFunctor.map₂` to nonexistent `OplaxFunctor.map₂`
#noalign category_theory.oplax_functor.to_prelax_functor_map₂

/-- Function between 1-morphisms as a functor. -/
@[simps]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj f := F.map f
  map η := F.map₂ η
#align category_theory.oplax_functor.map_functor CategoryTheory.OplaxFunctor.mapFunctor

/-- The identity oplax functor. -/
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : OplaxFunctor B B :=
  { PrelaxFunctor.id B with
    mapId := fun a => 𝟙 (𝟙 a)
    mapComp := fun f g => 𝟙 (f ≫ g)
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
    mapComp_naturality_left := fun η g => by
      dsimp
      rw [← map₂_comp_assoc, mapComp_naturality_left, map₂_comp_assoc, mapComp_naturality_left,
        assoc]
    mapComp_naturality_right := fun η => by
      dsimp
      intros
      rw [← map₂_comp_assoc, mapComp_naturality_right, map₂_comp_assoc, mapComp_naturality_right,
        assoc]
    map₂_associator := fun f g h => by
      dsimp
      -- Porting note: if you use the `map₂_associator_aux` hack in the definition of
      -- `map₂_associator` then the `simp only` call below does not seem to apply `map₂_associator`
      simp only [map₂_associator, ← map₂_comp_assoc, ← mapComp_naturality_right_assoc,
        whiskerLeft_comp, assoc]
      simp only [map₂_associator, map₂_comp, mapComp_naturality_left_assoc, comp_whiskerRight,
        assoc]
    map₂_leftUnitor := fun f => by
      dsimp
      simp only [map₂_leftUnitor, map₂_comp, mapComp_naturality_left_assoc, comp_whiskerRight,
        assoc]
    map₂_rightUnitor := fun f => by
      dsimp
      simp only [map₂_rightUnitor, map₂_comp, mapComp_naturality_right_assoc, whiskerLeft_comp,
        assoc] }
#align category_theory.oplax_functor.comp CategoryTheory.OplaxFunctor.comp

/-- A structure on an oplax functor that promotes an oplax functor to a pseudofunctor.
See `Pseudofunctor.mkOfOplax`.
-/
-- Porting note(#5171): linter not ported yet
-- @[nolint has_nonempty_instance]
-- Porting note: removing primes in structure name because
-- my understanding is that they're no longer needed
structure PseudoCore (F : OplaxFunctor B C) where
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  mapIdIso_hom : ∀ {a : B}, (mapIdIso a).hom = F.mapId a := by aesop_cat
  mapCompIso_hom :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), (mapCompIso f g).hom = F.mapComp f g := by aesop_cat
#align category_theory.oplax_functor.pseudo_core CategoryTheory.OplaxFunctor.PseudoCore

attribute [nolint docBlame] CategoryTheory.OplaxFunctor.PseudoCore.mapIdIso
  CategoryTheory.OplaxFunctor.PseudoCore.mapCompIso
  CategoryTheory.OplaxFunctor.PseudoCore.mapIdIso_hom
  CategoryTheory.OplaxFunctor.PseudoCore.mapCompIso_hom

attribute [simp] PseudoCore.mapIdIso_hom PseudoCore.mapCompIso_hom

end

end OplaxFunctor

-- Porting note: this auxiliary def was introduced in Lean 3 and only used once, in this file,
-- to avoid a timeout. In Lean 4 the timeout isn't present and the definition causes other
-- things to break (simp proofs) so I removed it.
-- def Pseudofunctor.Map₂AssociatorAux (obj : B → C) (map : ∀ {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
--     (map₂ : ∀ {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
--    (map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ≅ map f ≫ map g) {a b c d : B}
--     (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : Prop :=
--   map₂ (α_ f g h).hom =
--     (map_comp (f ≫ g) h).hom ≫
--       (map_comp f g).hom ▷ map h ≫
--        (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (map_comp g h).inv ≫ (map_comp f (g ≫ h)).inv
#noalign category_theory.pseudofunctor.map₂_associator_aux

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
  mapId (a : B) : map (𝟙 a) ≅ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g
  map₂_id : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by aesop_cat
  map₂_comp :
    ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    aesop_cat
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv := by
    aesop_cat
  map₂_whisker_right :
    ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv := by
    aesop_cat
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫
      (mapComp f (g ≫ h)).inv := by
    aesop_cat
  map₂_left_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (λ_ (map f)).hom := by
    aesop_cat
  map₂_right_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom := by
    aesop_cat
#align category_theory.pseudofunctor CategoryTheory.Pseudofunctor

initialize_simps_projections Pseudofunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace Pseudofunctor

attribute [reassoc]
  map₂_comp map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor

attribute [simp]
  map₂_id map₂_comp map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor
  map₂_right_unitor

section

open Iso

/-- The prelax functor between the underlying quivers. -/
add_decl_doc Pseudofunctor.toPrelaxFunctor


attribute [nolint docBlame] CategoryTheory.Pseudofunctor.mapId
  CategoryTheory.Pseudofunctor.mapComp
  CategoryTheory.Pseudofunctor.map₂_id
  CategoryTheory.Pseudofunctor.map₂_comp
  CategoryTheory.Pseudofunctor.map₂_whisker_left
  CategoryTheory.Pseudofunctor.map₂_whisker_right
  CategoryTheory.Pseudofunctor.map₂_associator
  CategoryTheory.Pseudofunctor.map₂_left_unitor
  CategoryTheory.Pseudofunctor.map₂_right_unitor

instance hasCoeToPrelaxFunctor : Coe (Pseudofunctor B C) (PrelaxFunctor B C) :=
  ⟨toPrelaxFunctor⟩
#align category_theory.pseudofunctor.has_coe_to_prelax_functor CategoryTheory.Pseudofunctor.hasCoeToPrelaxFunctor

variable (F : Pseudofunctor B C)

-- Porting note: `toPrelaxFunctor_eq_coe` and `to_prelaxFunctor_obj`
-- are syntactic tautologies in lean 4
#noalign category_theory.pseudofunctor.to_prelax_functor_eq_coe
#noalign category_theory.pseudofunctor.to_prelax_functor_obj

-- Porting note: removed lemma `to_prelaxFunctor_map` relating the now
-- nonexistent `PrelaxFunctor.map` and the now nonexistent `Pseudofunctor.map`
#noalign category_theory.pseudofunctor.to_prelax_functor_map

-- Porting note: removed lemma `to_prelaxFunctor_map₂` relating
-- `PrelaxFunctor.map₂` to nonexistent `Pseudofunctor.map₂`
#noalign category_theory.pseudofunctor.to_prelax_functor_map₂

/-- The oplax functor associated with a pseudofunctor. -/
def toOplax : OplaxFunctor B C :=
  { (F : PrelaxFunctor B C) with
    mapId := fun a => (F.mapId a).hom
    mapComp := fun f g => (F.mapComp f g).hom }
#align category_theory.pseudofunctor.to_oplax CategoryTheory.Pseudofunctor.toOplax

instance hasCoeToOplax : Coe (Pseudofunctor B C) (OplaxFunctor B C) :=
  ⟨toOplax⟩
#align category_theory.pseudofunctor.has_coe_to_oplax CategoryTheory.Pseudofunctor.hasCoeToOplax

-- Porting note: `toOplax_eq_coe` is a syntactic tautology in lean 4
#noalign category_theory.pseudofunctor.to_oplax_eq_coe

@[simp]
theorem to_oplax_obj : (F : OplaxFunctor B C).obj = F.obj :=
  rfl
#align category_theory.pseudofunctor.to_oplax_obj CategoryTheory.Pseudofunctor.to_oplax_obj

-- Porting note: to_oplax_map related `OplaxFunctor.map` to `Pseudofunctor.map` but neither
-- of these exist
#noalign category_theory.pseudofunctor.to_oplax_map

-- Porting note: to_oplax_map₂ related `OplaxFunctor.map₂` to `Pseudofunctor.map₂` but neither
-- of these exist
#noalign category_theory.pseudofunctor.to_oplax_map₂

@[simp]
theorem to_oplax_mapId (a : B) : (F : OplaxFunctor B C).mapId a = (F.mapId a).hom :=
  rfl
#align category_theory.pseudofunctor.to_oplax_map_id CategoryTheory.Pseudofunctor.to_oplax_mapId

@[simp]
theorem to_oplax_mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (F : OplaxFunctor B C).mapComp f g = (F.mapComp f g).hom :=
  rfl
#align category_theory.pseudofunctor.to_oplax_map_comp CategoryTheory.Pseudofunctor.to_oplax_mapComp

-- Porting note: I changed `simps` to `simps!` without understanding what I was doing
-- (lean 4 told me to do this)
/-- Function on 1-morphisms as a functor. -/
@[simps!]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) :=
  (F : OplaxFunctor B C).mapFunctor a b
#align category_theory.pseudofunctor.map_functor CategoryTheory.Pseudofunctor.mapFunctor

/-- The identity pseudofunctor. -/
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : Pseudofunctor B B :=
  { PrelaxFunctor.id B with
    mapId := fun a => Iso.refl (𝟙 a)
    mapComp := fun f g => Iso.refl (f ≫ g) }
#align category_theory.pseudofunctor.id CategoryTheory.Pseudofunctor.id

instance : Inhabited (Pseudofunctor B B) :=
  ⟨id B⟩

/-- Composition of pseudofunctors. -/
def comp (F : Pseudofunctor B C) (G : Pseudofunctor C D) : Pseudofunctor B D :=
  { (F : PrelaxFunctor B C).comp
      (G : PrelaxFunctor C D) with
    mapId := fun a => (G.mapFunctor _ _).mapIso (F.mapId a) ≪≫ G.mapId (F.obj a)
    mapComp := fun f g =>
      (G.mapFunctor _ _).mapIso (F.mapComp f g) ≪≫ G.mapComp (F.map f) (F.map g) }
#align category_theory.pseudofunctor.comp CategoryTheory.Pseudofunctor.comp

-- `comp` is near the `maxHeartbeats` limit (and seems to go over in CI),
-- so we defer creating its `@[simp]` lemmas until a separate command.
attribute [simps] comp

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms.
-/
@[simps]
def mkOfOplax (F : OplaxFunctor B C) (F' : F.PseudoCore) : Pseudofunctor B C :=
  { (F : PrelaxFunctor B C) with
    mapId := F'.mapIdIso
    mapComp := F'.mapCompIso
    map₂_whisker_left := fun f g h η => by
      dsimp
      rw [F'.mapCompIso_hom f g, ← F.mapComp_naturality_right_assoc, ← F'.mapCompIso_hom f h,
        hom_inv_id, comp_id]
    map₂_whisker_right := fun η h => by
      dsimp
      rw [F'.mapCompIso_hom _ h, ← F.mapComp_naturality_left_assoc, ← F'.mapCompIso_hom _ h,
        hom_inv_id, comp_id]
    map₂_associator := fun f g h => by
      dsimp
      rw [F'.mapCompIso_hom (f ≫ g) h, F'.mapCompIso_hom f g, ← F.map₂_associator_assoc, ←
        F'.mapCompIso_hom f (g ≫ h), ← F'.mapCompIso_hom g h, whiskerLeft_hom_inv_assoc,
        hom_inv_id, comp_id] }
#align category_theory.pseudofunctor.mk_of_oplax CategoryTheory.Pseudofunctor.mkOfOplax

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms.
-/
@[simps]
noncomputable def mkOfOplax' (F : OplaxFunctor B C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : Pseudofunctor B C :=
  { (F : PrelaxFunctor B C) with
    mapId := fun a => asIso (F.mapId a)
    mapComp := fun f g => asIso (F.mapComp f g)
    map₂_whisker_left := fun f g h η => by
      dsimp
      rw [← assoc, IsIso.eq_comp_inv, F.mapComp_naturality_right]
    map₂_whisker_right := fun η h => by
      dsimp
      rw [← assoc, IsIso.eq_comp_inv, F.mapComp_naturality_left]
    map₂_associator := fun f g h => by
      dsimp
      simp only [← assoc]
      rw [IsIso.eq_comp_inv, ← inv_whiskerLeft, IsIso.eq_comp_inv]
      simp only [assoc, F.map₂_associator] }
#align category_theory.pseudofunctor.mk_of_oplax' CategoryTheory.Pseudofunctor.mkOfOplax'

end

end Pseudofunctor

end

end CategoryTheory
