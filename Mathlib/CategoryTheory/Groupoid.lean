/-
Copyright (c) 2018 Reid Barton All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison, David Wärn
-/
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.Quiver.Symmetric

#align_import category_theory.groupoid from "leanprover-community/mathlib"@"2efd2423f8d25fa57cf7a179f5d8652ab4d0df44"

/-!
# Groupoids

We define `Groupoid` as a typeclass extending `Category`,
asserting that all morphisms have inverses.

The instance `IsIso.ofGroupoid (f : X ⟶ Y) : IsIso f` means that you can then write
`inv f` to access the inverse of any morphism `f`.

`Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y)` provides the equivalence between
isomorphisms and morphisms in a groupoid.

We provide a (non-instance) constructor `Groupoid.ofIsIso` from an existing category
with `IsIso f` for every `f`.

## See also

See also `CategoryTheory.Core` for the groupoid of isomorphisms in a category.
-/


namespace CategoryTheory

universe v v₂ u u₂

-- morphism levels before object levels. See note [CategoryTheory universes].
/-- A `Groupoid` is a category such that all morphisms are isomorphisms. -/
class Groupoid (obj : Type u) extends Category.{v} obj : Type max u (v + 1) where
  /-- The inverse morphism -/
  inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
  /-- `inv f` composed `f` is the identity -/
  inv_comp : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by aesop_cat
  /-- `f` composed with `inv f` is the identity -/
  comp_inv : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by aesop_cat
#align category_theory.groupoid CategoryTheory.Groupoid

initialize_simps_projections Groupoid (-Hom)

/-- A `LargeGroupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
abbrev LargeGroupoid (C : Type (u + 1)) : Type (u + 1) :=
  Groupoid.{u} C
#align category_theory.large_groupoid CategoryTheory.LargeGroupoid

/-- A `SmallGroupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
abbrev SmallGroupoid (C : Type u) : Type (u + 1) :=
  Groupoid.{u} C
#align category_theory.small_groupoid CategoryTheory.SmallGroupoid

section

variable {C : Type u} [Groupoid.{v} C] {X Y : C}

-- see Note [lower instance priority]
instance (priority := 100) IsIso.of_groupoid (f : X ⟶ Y) : IsIso f :=
  ⟨⟨Groupoid.inv f, Groupoid.comp_inv f, Groupoid.inv_comp f⟩⟩
#align category_theory.is_iso.of_groupoid CategoryTheory.IsIso.of_groupoid

@[simp]
theorem Groupoid.inv_eq_inv (f : X ⟶ Y) : Groupoid.inv f = CategoryTheory.inv f :=
  IsIso.eq_inv_of_hom_inv_id <| Groupoid.comp_inv f
#align category_theory.groupoid.inv_eq_inv CategoryTheory.Groupoid.inv_eq_inv

/-- `Groupoid.inv` is involutive. -/
@[simps]
def Groupoid.invEquiv : (X ⟶ Y) ≃ (Y ⟶ X) :=
  ⟨Groupoid.inv, Groupoid.inv, fun f => by simp, fun f => by simp⟩
                                           -- 🎉 no goals
                                                             -- 🎉 no goals
#align category_theory.groupoid.inv_equiv CategoryTheory.Groupoid.invEquiv

instance (priority := 100) groupoidHasInvolutiveReverse : Quiver.HasInvolutiveReverse C where
  reverse' f := Groupoid.inv f
  inv' f := by
    dsimp [Quiver.reverse]
    -- ⊢ Groupoid.inv (Groupoid.inv f) = f
    simp
    -- 🎉 no goals
#align category_theory.groupoid_has_involutive_reverse CategoryTheory.groupoidHasInvolutiveReverse

@[simp]
theorem Groupoid.reverse_eq_inv (f : X ⟶ Y) : Quiver.reverse f = Groupoid.inv f :=
  rfl
#align category_theory.groupoid.reverse_eq_inv CategoryTheory.Groupoid.reverse_eq_inv

instance functorMapReverse {D : Type*} [Groupoid D] (F : C ⥤ D) : F.toPrefunctor.MapReverse where
  map_reverse' f := by
    simp only [Quiver.reverse, Quiver.HasReverse.reverse', Groupoid.inv_eq_inv,
      Functor.map_inv]
#align category_theory.functor_map_reverse CategoryTheory.functorMapReverse

variable (X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
def Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y) where
  toFun := Iso.hom
  invFun f := ⟨f, Groupoid.inv f, (by aesop_cat), (by aesop_cat)⟩
                                      -- 🎉 no goals
                                                      -- 🎉 no goals
  left_inv i := Iso.ext rfl
  right_inv f := rfl
#align category_theory.groupoid.iso_equiv_hom CategoryTheory.Groupoid.isoEquivHom

variable (C)

/-- The functor from a groupoid `C` to its opposite sending every morphism to its inverse. -/
@[simps]
noncomputable def Groupoid.invFunctor : C ⥤ Cᵒᵖ where
  obj := Opposite.op
  map {X Y} f := (inv f).op
#align category_theory.groupoid.inv_functor CategoryTheory.Groupoid.invFunctor

end

section

variable {C : Type u} [Category.{v} C]

/-- A category where every morphism `IsIso` is a groupoid. -/
noncomputable def Groupoid.ofIsIso (all_is_iso : ∀ {X Y : C} (f : X ⟶ Y), IsIso f) :
    Groupoid.{v} C where
  inv := fun f => CategoryTheory.inv f
  inv_comp := fun f => Classical.choose_spec (all_is_iso f).out|>.right
#align category_theory.groupoid.of_is_iso CategoryTheory.Groupoid.ofIsIso

/-- A category with a unique morphism between any two objects is a groupoid -/
def Groupoid.ofHomUnique (all_unique : ∀ {X Y : C}, Unique (X ⟶ Y)) : Groupoid.{v} C where
  inv _ := all_unique.default
#align category_theory.groupoid.of_hom_unique CategoryTheory.Groupoid.ofHomUnique

end

instance InducedCategory.groupoid {C : Type u} (D : Type u₂) [Groupoid.{v} D] (F : C → D) :
    Groupoid.{v} (InducedCategory D F) :=
  { InducedCategory.category F with
    inv := fun f => Groupoid.inv f
    inv_comp := fun f => Groupoid.inv_comp f
    comp_inv := fun f => Groupoid.comp_inv f }
#align category_theory.induced_category.groupoid CategoryTheory.InducedCategory.groupoid

section

instance groupoidPi {I : Type u} {J : I → Type u₂} [∀ i, Groupoid.{v} (J i)] :
    Groupoid.{max u v} (∀ i : I, J i) where
  inv f := fun i : I => Groupoid.inv (f i)
  comp_inv := fun f => by funext i; apply Groupoid.comp_inv
                          -- ⊢ (f ≫ (fun {X Y} f i => Groupoid.inv (f i)) f) i = 𝟙 X✝ i
                          -- ⊢ ((fun {X Y} f i => Groupoid.inv (f i)) f ≫ f) i = 𝟙 Y✝ i
                                    -- 🎉 no goals
                                    -- 🎉 no goals
  inv_comp := fun f => by funext i; apply Groupoid.inv_comp
#align category_theory.groupoid_pi CategoryTheory.groupoidPi

instance groupoidProd {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β] :
    Groupoid.{max u₂ v₂} (α × β) where
  inv f := (Groupoid.inv f.1, Groupoid.inv f.2)
#align category_theory.groupoid_prod CategoryTheory.groupoidProd

end

end CategoryTheory
