/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Free groupoid on a category

This file defines the free groupoid on a category, the lifting of a functor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given a type `C` and a category instance on `C`:

- `CategoryTheory.Category.FreeGroupoid C`: the underlying type of the free groupoid on `C`.
- `CategoryTheory.Category.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `FreeGroupoid C`.
- `CategoryTheory.Category.FreeGroupoid.lift`: the lifting of a functor `C ⥤ G` where `G` is a
  groupoid, to a functor `CategoryTheory.Category.FreeGroupoid C ⥤ G`.
- `CategoryTheory.Category.FreeGroupoid.lift_spec` and
  `CategoryTheory.Category.FreeGroupoid.lift_unique`:
  the proofs that, respectively, `CategoryTheory.Category.FreeGroupoid.lift` indeed is a lifting
  and is the unique one.
- `CategoryTheory.Category.Grpd.free`: the free functor from `Grpd` to `Cat`
- `CategoryTheory.Category.Grpd.freeForgetAdjunction`: that `free` is left adjoint to
  `Grpd.forgetToCat`.

## Implementation notes

The free groupoid on a category `C` is first defined by taking the free groupoid `G`
on the underlying *quiver* of `C`. Then the free groupoid on the *category* `C` is defined as
the quotient of `G` by the relation that makes the inclusion prefunctor `C ⥤q G` a functor.

-/

noncomputable section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂

namespace Category

variable (C : Type u) [Category.{v} C]

open Quiver in
/-- The relation on the free groupoid on the underlying *quiver* of C that
promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`. -/
inductive FreeGroupoid.homRel : HomRel (Quiver.FreeGroupoid C) where
| map_id (X : C) : homRel ((FreeGroupoid.of C).map (𝟙 X)) (𝟙 ((FreeGroupoid.of C).obj X))
| map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : homRel ((FreeGroupoid.of C).map (f ≫ g))
  ((FreeGroupoid.of C).map f ≫ (FreeGroupoid.of C).map g)

/-- The underlying type of the free groupoid on a category,
defined by quotienting the free groupoid on the underlying quiver of `C`
by the relation that promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`. -/
protected def FreeGroupoid := Quotient (FreeGroupoid.homRel C)

instance [Nonempty C] : Nonempty (Category.FreeGroupoid C) :=
  ⟨Quotient.mk (Quotient.mk ((Paths.of _).obj (Classical.arbitrary C)))⟩

instance : Groupoid (Category.FreeGroupoid C) :=
  Quotient.groupoid (Category.FreeGroupoid.homRel C)

namespace FreeGroupoid

/-- The localization map from the category `C` to the groupoid `Category.FreeGroupoid C` -/
def of : C ⥤ Category.FreeGroupoid C where
  __ := Quiver.FreeGroupoid.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor
  map_id X := Quotient.sound _ (Category.FreeGroupoid.homRel.map_id X)
  map_comp f g := Quotient.sound _ (Category.FreeGroupoid.homRel.map_comp f g)

variable {C}

lemma of_obj_bijective : Function.Bijective (of C).obj where
  left _ _ h := by cases h; rfl
  right X := ⟨X.as.as, rfl⟩

section UniversalProperty

variable {G : Type u₁} [Groupoid.{v₁} G]

/-- The lift of a functor from `C` to a groupoid to a functor from
`FreeGroupoid C` to the groupoid -/
def lift (φ : C ⥤ G) : Category.FreeGroupoid C ⥤ G :=
  Quotient.lift (FreeGroupoid.homRel C) (Quiver.FreeGroupoid.lift φ.toPrefunctor)
    (fun _ _ f g r ↦ by
      have {X Y : C} (f : X ⟶ Y) :=
        Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ.toPrefunctor) f
      induction r <;> cat_disch)

theorem lift_spec (φ : C ⥤ G) : of C ⋙ lift φ = φ :=
  Functor.toPrefunctor_injective (by
    change Quiver.FreeGroupoid.of C ⋙q
      (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor ⋙q
        (lift φ).toPrefunctor = φ.toPrefunctor
    simp [lift, Quotient.lift_spec, Quiver.FreeGroupoid.lift_spec])

theorem lift_unique (φ : C ⥤ G) (Φ : Category.FreeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) :
    Φ = lift φ := by
  apply Quotient.lift_unique
  apply Quiver.FreeGroupoid.lift_unique
  exact congr_arg Functor.toPrefunctor hΦ

theorem lift_comp {H : Type u₂} [Groupoid.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H) :
    lift (φ ⋙ ψ) = lift φ ⋙ ψ := by
  symm
  apply lift_unique
  rw [← Functor.assoc, lift_spec]

/-- The universal property of the free groupoid. -/
def strictUniversalPropertyFixedTarget :
    Localization.StrictUniversalPropertyFixedTarget (of C) ⊤ G where
  inverts _ := inferInstance
  lift F _ := lift F
  fac _ _ := lift_spec ..
  uniq F G h := by rw [lift_unique (of C ⋙ G) F h, ← lift_unique (of C ⋙ G) G rfl]

attribute [local instance] Localization.groupoid

instance : (of C).IsLocalization ⊤ :=
  .mk' _ _ strictUniversalPropertyFixedTarget strictUniversalPropertyFixedTarget

end UniversalProperty

section Functoriality

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/-- The functor of free groupoid induced by a functor between the original categories. -/
def map (φ : C ⥤ D) : Category.FreeGroupoid C ⥤ Category.FreeGroupoid D :=
  lift (φ ⋙ of D)

variable (C) in
theorem map_id : map (𝟭 C) = 𝟭 (Category.FreeGroupoid C) := by
  symm; apply lift_unique; rfl

variable (C) in
/-- The functor induced by the identity is the identity. -/
def mapId : map (𝟭 C) ≅ 𝟭 (Category.FreeGroupoid C) :=
  eqToIso (map_id C)

theorem map_comp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') = map φ ⋙ map φ' := by
  symm; apply lift_unique; rfl

/-- The functor induced by a composition is the composition of the functors they induce. -/
def mapComp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') ≅ map φ ⋙ map φ':=
  eqToIso (map_comp φ φ')

lemma of_map (F : C ⥤ D) : of C ⋙ map F = F ⋙ of D := rfl

/-- The operation `of` is natural. -/
def ofMap (F : C ⥤ D) : of C ⋙ map F ≅ F ⋙ of D := Iso.refl _

lemma map_lift {E : Type u₂} [Groupoid.{v₂} E] (F : C ⥤ D) (G : D ⥤ E) :
  map F ⋙ lift G = lift (F ⋙ G) := by
    apply lift_unique
    rw [← Functor.assoc, of_map, Functor.assoc, lift_spec G]

/-- The operation `lift` is natural. -/
def mapLift {E : Type u₂} [Groupoid.{v₂} E] (F : C ⥤ D) (G : D ⥤ E) :
  map F ⋙ lift G ≅ lift (F ⋙ G) := eqToIso (map_lift F G)

end Functoriality

/-- Functors out of the free groupoid biject with functors out of the original category. -/
@[simps]
def functorEquiv {D : Type*} [Groupoid D] : (Category.FreeGroupoid C ⥤ D) ≃ (C ⥤ D) where
  toFun G := of C ⋙ G
  invFun := lift
  right_inv := lift_spec
  left_inv _ := (lift_unique _ _ rfl).symm

end FreeGroupoid

end Category

namespace Grpd

open Category.FreeGroupoid

/-- The free groupoid construction on a category as a functor. -/
@[simps]
def free : Cat.{u, u} ⥤ Grpd.{u, u} where
  obj C := Grpd.of <| Category.FreeGroupoid C
  map {C D} F := map F
  map_id C := by simp [Grpd.id_eq_id, ← map_id]; rfl
  map_comp F G := by simp [Grpd.comp_eq_comp, ← map_comp]; rfl

/-- The free-forgetful adjunction between `Grpd` and `Cat`. -/
def freeForgetAdjunction : free ⊣ Grpd.forgetToCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Category.FreeGroupoid.functorEquiv
      homEquiv_naturality_left_symm _ _ := (Category.FreeGroupoid.map_lift _ _).symm
      homEquiv_naturality_right _ _ := rfl }

instance : Reflective Grpd.forgetToCat where
  L := free
  adj := freeForgetAdjunction

end Grpd
end CategoryTheory
end
