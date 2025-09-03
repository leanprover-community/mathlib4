/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Free groupoid on a category

This file defines the free groupoid on a category, the lifting of a functor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given a type `C` and a category instance on `C`:

- `CategoryTheory.Category.FreeGroupoid C`: the underlying type of the free groupoid on `C`.
- `CategoryTheory.Category.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `FreeGroupoid C`.
- `CategoryTheory.Category.lift`: the lifting of a functor `C ⥤ G` where `G` is a groupoid,
  to a functor `CategoryTheory.Category.FreeGroupoid C ⥤ G`.
- `CategoryTheory.Category.lift_spec` and `CategoryTheory.Category.lift_unique`:
  the proofs that, respectively, `CategoryTheory.Category.lift` indeed is a lifting
  and is the unique one.

## Implementation notes

The free groupoid on a category `C` is first defined by taking the free groupoid `G`
on the underlying *quiver* of `C`. Then the free groupoid on the *category* `C` is defined as
the quotient of `G` by the relation that makes the inclusion prefunctor `C ⥤q G` a functor.

## TODO

- Place the original definition `CategoryTheory.FreeGroupoid` into the namespace
  `Quiver.FreeGroupoid`.

-/

noncomputable section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂

namespace Category

variable (C : Type u) [Category.{v} C]

/-- The relation on the free groupoid on the underlying *quiver* of C that
promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`. -/
inductive FreeGroupoid.homRel : HomRel (CategoryTheory.FreeGroupoid C) where
| map_id (X : C) : homRel ((Groupoid.Free.of C).map (𝟙 X)) (𝟙 ((Groupoid.Free.of C).obj X))
| map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : homRel ((Groupoid.Free.of C).map (f ≫ g))
  ((Groupoid.Free.of C).map f ≫ (Groupoid.Free.of C).map g)

/-- The underlying type of the free groupoid on a category,
defined by quotienting the free groupoid on the underlying quiver of `C`
by the relation that promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`. -/
protected def FreeGroupoid := Quotient (FreeGroupoid.homRel C)

variable {C} in
instance [Nonempty C] : Nonempty (Category.FreeGroupoid C) := by
  have : Inhabited (CategoryTheory.FreeGroupoid C) := by
    inhabit CategoryTheory.FreeGroupoid C
    exact ⟨@default (CategoryTheory.FreeGroupoid C) _⟩
  have : Inhabited (Category.FreeGroupoid C) := inferInstanceAs (Inhabited <| Quotient _)
  inhabit Category.FreeGroupoid C
  exact ⟨@default (Category.FreeGroupoid C) _⟩

variable {C} in
instance : Groupoid (Category.FreeGroupoid C) :=
  Quotient.groupoid (Category.FreeGroupoid.homRel C)

namespace FreeGroupoid

@[simp]
lemma of.map_id (X : C) : (Quotient.functor (FreeGroupoid.homRel C)).map
    ((Groupoid.Free.of C).map (𝟙 X)) = 𝟙 _:= by
  simp [Quotient.sound _ (Category.FreeGroupoid.homRel.map_id X)]

@[simp]
lemma of.map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Quotient.functor (FreeGroupoid.homRel C)).map ((Groupoid.Free.of C).map (f ≫ g)) =
    (Quotient.functor (FreeGroupoid.homRel C)).map ((Groupoid.Free.of C).map f) ≫
    (Quotient.functor (FreeGroupoid.homRel C)).map ((Groupoid.Free.of C).map g) := by
  simp [Quotient.sound _ (Category.FreeGroupoid.homRel.map_comp f g)]

/-- The localization map from the category `C` to the groupoid `Category.FreeGroupoid C` -/
def of : C ⥤ Category.FreeGroupoid C where
  __ := Groupoid.Free.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor
  map_id X := by simp
  map_comp {X Y Z} f g := by simp

section UniversalProperty

variable {C} {G : Type u₁} [Groupoid.{v₁} G]

/-- The lift of a functor from `C` to a groupoid to a functor from
`FreeGroupoid C` to the groupoid -/
def lift (φ : C ⥤ G) : Category.FreeGroupoid C ⥤ G :=
  Quotient.lift (FreeGroupoid.homRel C) (Groupoid.Free.lift φ.toPrefunctor) (by
    intros X Y f g r
    rcases r with X | ⟨ f , g ⟩
    · simpa using Prefunctor.congr_hom (Groupoid.Free.lift_spec φ.toPrefunctor) (𝟙 X)
    · have hf := Prefunctor.congr_hom (Groupoid.Free.lift_spec φ.toPrefunctor) f
      have hg := Prefunctor.congr_hom (Groupoid.Free.lift_spec φ.toPrefunctor) g
      have hfg := Prefunctor.congr_hom (Groupoid.Free.lift_spec φ.toPrefunctor) (f ≫ g)
      simp only [Functor.toPrefunctor_obj, Prefunctor.comp_obj, Prefunctor.comp_map,
        Functor.toPrefunctor_map, Quiver.homOfEq_rfl, Functor.map_comp] at *
      rw [hf, hg, hfg])

theorem lift_spec (φ : C ⥤ G) : of C ⋙ lift φ = φ := by
  have : Groupoid.Free.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor ⋙q
      (lift φ).toPrefunctor = φ.toPrefunctor := by
    simp [lift, Quotient.lift_spec, Groupoid.Free.lift_spec]
  fapply Functor.ext
  · apply Prefunctor.congr_obj this
  · intro _ _
    simpa using Prefunctor.congr_hom this

theorem lift_unique (φ : C ⥤ G) (Φ : Category.FreeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) :
    Φ = lift φ := by
  apply Quotient.lift_unique
  apply Groupoid.Free.lift_unique
  exact congr_arg Functor.toPrefunctor hΦ

theorem lift_comp {H : Type u₂} [Groupoid.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H) :
    lift (φ ⋙ ψ) = lift φ ⋙ ψ := by
  symm
  apply lift_unique
  rw [← Functor.assoc, lift_spec]

end UniversalProperty

section Functoriality

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {E : Type u₂} [Category.{v₂} E]

/-- The functor of free groupoid induced by a prefunctor of quivers -/
def map (φ : C ⥤ D) : Category.FreeGroupoid C ⥤ Category.FreeGroupoid D :=
  lift (φ ⋙ of D)

theorem map_id : map (𝟭 C) = 𝟭 (Category.FreeGroupoid C) := by
  dsimp only [map]; symm
  apply lift_unique; rfl

theorem map_comp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') = map φ ⋙ map φ' := by
  dsimp only [map]; symm
  apply lift_unique; rfl

end Functoriality

end FreeGroupoid

end Category

namespace Grpd

open Category.FreeGroupoid

/-- The free groupoid construction on a category as a functor. -/
@[simps]
def free : Cat.{u,u} ⥤ Grpd.{u,u} where
  obj C := Grpd.of <| Category.FreeGroupoid C
  map {C D} F := map F
  map_id C := by simp [Grpd.id_eq_id, ← map_id]; rfl
  map_comp F G := by simp [Grpd.comp_eq_comp, ← map_comp]; rfl

/-- The unit of the free-forgetful adjunction between `Grpd` and `Cat`. -/
@[simps]
def freeForgetAdjunction.unit : 𝟭 Cat ⟶ free ⋙ forgetToCat where
  app C := Category.FreeGroupoid.of C
  naturality C D F := by simp [forgetToCat, Cat.comp_eq_comp, map, lift_spec]

/-- The counit of the free-forgetful adjunction between `Grpd` and `Cat`. -/
@[simps]
def freeForgetAdjunction.counit : forgetToCat ⋙ free ⟶ 𝟭 Grpd where
  app G := lift (𝟭 G)
  naturality G H φ := by
    simp [map, Grpd.comp_eq_comp, ← lift_comp, forgetToCat, Functor.id_comp, Functor.assoc,
      lift_spec, Functor.comp_id]

/-- The free-forgetful adjunction between `Grpd` and `Cat`. -/
def freeForgetAdjunction : free ⊣ Grpd.forgetToCat where
  unit := freeForgetAdjunction.unit
  counit := freeForgetAdjunction.counit
  left_triangle_components C := by
    simp only [Functor.id_obj, free_obj, Functor.comp_obj, freeForgetAdjunction.unit_app, free_map,
      map, freeForgetAdjunction.counit_app, coe_of, comp_eq_comp, ← lift_comp]
    symm
    apply lift_unique
    simp [Functor.comp_id, forgetToCat, Functor.assoc, lift_spec, Grpd.id_eq_id]
  right_triangle_components G := by
    simp [forgetToCat, Cat.comp_eq_comp, lift_spec, Cat.id_eq_id]

instance : Reflective Grpd.forgetToCat where
  L := free
  adj := freeForgetAdjunction

end Grpd
end CategoryTheory
end
