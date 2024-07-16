/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
import Mathlib.CategoryTheory.Bicategory.Functor.Lax

#align_import category_theory.bicategory.functor from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

/-!
# Pseudofunctors

A pseudofunctor is an oplax (or lax) functor whose `mapId` and `mapComp` are isomorphisms.
We provide several constructors for pseudofunctors:
* `Pseudofunctor.mk` : the default constructor, which requires `map₂_whiskerLeft` and
  `map₂_whiskerRight` instead of naturality of `mapComp`.

* `Pseudofunctor.mkOfOplax` : construct a pseudofunctor from an oplax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `pseudofunctor.mkOfOplax'` : similar to `mkOfOplax`, but uses `IsIso` to describe isomorphisms.

* `Pseudofunctor.mkOfLax` : construct a pseudofunctor from a lax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `pseudofunctor.mkOfLax'` : similar to `mkOfLax`, but uses `IsIso` to describe isomorphisms.

## Main definitions

* `CategoryTheory.Pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`
* `CategoryTheory.Pseudofunctor.comp F G` : the composition of pseudofunctors

-/

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

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

attribute [simp, reassoc]
  map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor

section

open Iso

/-- The underlying prelax functor. -/
add_decl_doc Pseudofunctor.toPrelaxFunctor


attribute [nolint docBlame] CategoryTheory.Pseudofunctor.mapId
  CategoryTheory.Pseudofunctor.mapComp
  CategoryTheory.Pseudofunctor.map₂_whisker_left
  CategoryTheory.Pseudofunctor.map₂_whisker_right
  CategoryTheory.Pseudofunctor.map₂_associator
  CategoryTheory.Pseudofunctor.map₂_left_unitor
  CategoryTheory.Pseudofunctor.map₂_right_unitor

#noalign category_theory.pseudofunctor.has_coe_to_prelax_functor

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
@[simps]
def toOplax : OplaxFunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).hom
  mapComp := fun f g => (F.mapComp f g).hom
#align category_theory.pseudofunctor.to_oplax CategoryTheory.Pseudofunctor.toOplax
#align category_theory.pseudofunctor.to_oplax_map_id CategoryTheory.Pseudofunctor.toOplax_mapId
#align category_theory.pseudofunctor.to_oplax_map_comp CategoryTheory.Pseudofunctor.toOplax_mapComp
#noalign category_theory.pseudofunctor.to_oplax_obj
#noalign category_theory.pseudofunctor.to_oplax_map
#noalign category_theory.pseudofunctor.to_oplax_map₂

instance hasCoeToOplax : Coe (Pseudofunctor B C) (OplaxFunctor B C) :=
  ⟨toOplax⟩
#align category_theory.pseudofunctor.has_coe_to_oplax CategoryTheory.Pseudofunctor.hasCoeToOplax

-- Porting note: `toOplax_eq_coe` is a syntactic tautology in lean 4
#noalign category_theory.pseudofunctor.to_oplax_eq_coe

/-- The Lax functor associated with a pseudofunctor. -/
@[simps]
def toLax : LaxFunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).inv
  mapComp := fun f g => (F.mapComp f g).inv
  map₂_leftUnitor f := by
    rw [← F.map₂Iso_inv, eq_inv_comp, comp_inv_eq]
    simp
  map₂_rightUnitor f := by
    rw [← F.map₂Iso_inv, eq_inv_comp, comp_inv_eq]
    simp

instance hasCoeToLax : Coe (Pseudofunctor B C) (LaxFunctor B C) :=
  ⟨toLax⟩


/-- The identity pseudofunctor. -/
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : Pseudofunctor B B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => Iso.refl (𝟙 a)
  mapComp := fun f g => Iso.refl (f ≫ g)
#align category_theory.pseudofunctor.id CategoryTheory.Pseudofunctor.id

instance : Inhabited (Pseudofunctor B B) :=
  ⟨id B⟩

/-- Composition of pseudofunctors. -/
@[simps]
def comp (F : Pseudofunctor B C) (G : Pseudofunctor C D) : Pseudofunctor B D where
  toPrelaxFunctor := F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => G.map₂Iso (F.mapId a) ≪≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.map₂Iso (F.mapComp f g)) ≪≫ G.mapComp (F.map f) (F.map g)
  -- Note: whilst these are all provable by `aesop_cat`, the proof is very slow
  map₂_whisker_left f η := by dsimp; simp
  map₂_whisker_right η h := by dsimp; simp
  map₂_associator f g h := by dsimp; simp
  map₂_left_unitor f := by dsimp; simp
  map₂_right_unitor f := by dsimp; simp
#align category_theory.pseudofunctor.comp CategoryTheory.Pseudofunctor.comp

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps]
def mkOfOplax (F : OplaxFunctor B C) (F' : F.PseudoCore) : Pseudofunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
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
      hom_inv_id, comp_id]
#align category_theory.pseudofunctor.mk_of_oplax CategoryTheory.Pseudofunctor.mkOfOplax

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps!]
noncomputable def mkOfOplax' (F : OplaxFunctor B C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : Pseudofunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
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
    simp only [assoc, F.map₂_associator]
#align category_theory.pseudofunctor.mk_of_oplax' CategoryTheory.Pseudofunctor.mkOfOplax'

/-- Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps]
def mkOfLax (F : LaxFunctor B C) (F' : F.PseudoCore) : Pseudofunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left f g h η := by
    rw [F'.mapCompIso_inv, ← LaxFunctor.mapComp_naturality_right, ← F'.mapCompIso_inv,
      hom_inv_id_assoc]
  map₂_whisker_right η h := by
    rw [F'.mapCompIso_inv, ← LaxFunctor.mapComp_naturality_left, ← F'.mapCompIso_inv,
      hom_inv_id_assoc]
  map₂_associator {a b c d} f g h := by
    rw [F'.mapCompIso_inv, F'.mapCompIso_inv, ← inv_comp_eq, ← IsIso.inv_comp_eq]
    simp
  map₂_left_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp
  map₂_right_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp

/-- Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps!]
noncomputable def mkOfLax' (F : LaxFunctor B C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : Pseudofunctor B C :=
  mkOfLax F
  { mapIdIso := fun a => (asIso (F.mapId a)).symm
    mapCompIso := fun f g => (asIso (F.mapComp f g)).symm }

end

end Pseudofunctor

end CategoryTheory
