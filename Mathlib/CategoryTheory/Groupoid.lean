/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison, David Wärn
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

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
class Groupoid (obj : Type u) : Type max u (v + 1) extends Category.{v} obj where
  /-- The inverse morphism -/
  inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
  /-- `inv f` composed `f` is the identity -/
  inv_comp : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by aesop_cat
  /-- `f` composed with `inv f` is the identity -/
  comp_inv : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by aesop_cat

initialize_simps_projections Groupoid (-Hom)

/-- A `LargeGroupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
abbrev LargeGroupoid (C : Type (u + 1)) : Type (u + 1) :=
  Groupoid.{u} C

/-- A `SmallGroupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
abbrev SmallGroupoid (C : Type u) : Type (u + 1) :=
  Groupoid.{u} C

section

variable {C : Type u} [Groupoid.{v} C] {X Y : C}

-- see Note [lower instance priority]
instance (priority := 100) IsIso.of_groupoid (f : X ⟶ Y) : IsIso f :=
  ⟨⟨Groupoid.inv f, Groupoid.comp_inv f, Groupoid.inv_comp f⟩⟩

@[simp]
theorem Groupoid.inv_eq_inv (f : X ⟶ Y) : Groupoid.inv f = CategoryTheory.inv f :=
  IsIso.eq_inv_of_hom_inv_id <| Groupoid.comp_inv f

/-- `Groupoid.inv` is involutive. -/
@[simps]
def Groupoid.invEquiv : (X ⟶ Y) ≃ (Y ⟶ X) :=
  ⟨Groupoid.inv, Groupoid.inv, fun f => by simp, fun f => by simp⟩

instance (priority := 100) groupoidHasInvolutiveReverse : Quiver.HasInvolutiveReverse C where
  reverse' f := Groupoid.inv f
  inv' f := by
    dsimp [Quiver.reverse]
    simp

@[simp]
theorem Groupoid.reverse_eq_inv (f : X ⟶ Y) : Quiver.reverse f = Groupoid.inv f :=
  rfl

instance functorMapReverse {D : Type*} [Groupoid D] (F : C ⥤ D) : F.toPrefunctor.MapReverse where
  map_reverse' f := by
    simp only [Quiver.reverse, Quiver.HasReverse.reverse', Groupoid.inv_eq_inv,
      Functor.map_inv]

variable (X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
@[simps!]
def Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y) where
  toFun := Iso.hom
  invFun f := ⟨f, Groupoid.inv f, (by simp), (by simp)⟩

variable (C)

/-- The functor from a groupoid `C` to its opposite sending every morphism to its inverse. -/
@[simps]
noncomputable def Groupoid.invFunctor : C ⥤ Cᵒᵖ where
  obj := Opposite.op
  map {_ _} f := (inv f).op

end

section

/-- A Prop-valued typeclass asserting that a given category is a groupoid. -/
class IsGroupoid (C : Type u) [Category.{v} C] : Prop where
  all_isIso {X Y : C} (f : X ⟶ Y) : IsIso f := by infer_instance

attribute [instance] IsGroupoid.all_isIso

noncomputable instance {C : Type u} [Groupoid.{v} C] : IsGroupoid C where

variable {C : Type u} [Category.{v} C]

/-- Promote (noncomputably) an `IsGroupoid` to a `Groupoid` structure. -/
noncomputable def Groupoid.ofIsGroupoid [IsGroupoid C] :
    Groupoid.{v} C where
  inv := fun f => CategoryTheory.inv f

/-- A category where every morphism `IsIso` is a groupoid. -/
noncomputable def Groupoid.ofIsIso (all_is_iso : ∀ {X Y : C} (f : X ⟶ Y), IsIso f) :
    Groupoid.{v} C where
  inv := fun f => CategoryTheory.inv f
  inv_comp := fun f => Classical.choose_spec (all_is_iso f).out|>.right

/-- A category with a unique morphism between any two objects is a groupoid -/
def Groupoid.ofHomUnique (all_unique : ∀ {X Y : C}, Unique (X ⟶ Y)) : Groupoid.{v} C where
  inv _ := all_unique.default

end

lemma isGroupoid_of_reflects_iso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.ReflectsIsomorphisms] [IsGroupoid D] :
    IsGroupoid C where
  all_isIso _ := isIso_of_reflects_iso _ F

/-- A category equipped with a fully faithful functor to a groupoid is fully faithful -/
def Groupoid.ofFullyFaithfulToGroupoid {C : Type*} [𝒞 : Category C] {D : Type u} [Groupoid.{v} D]
    (F : C ⥤ D) (h : F.FullyFaithful) : Groupoid C :=
  { 𝒞 with
    inv f := h.preimage <| Groupoid.inv (F.map f)
    inv_comp f := by
      apply h.map_injective
      simp
    comp_inv f := by
      apply h.map_injective
      simp }

instance InducedCategory.groupoid {C : Type u} (D : Type u₂) [Groupoid.{v} D] (F : C → D) :
    Groupoid.{v} (InducedCategory D F) :=
  Groupoid.ofFullyFaithfulToGroupoid (inducedFunctor F) (fullyFaithfulInducedFunctor F)

instance InducedCategory.isGroupoid {C : Type u} (D : Type u₂)
    [Category.{v} D] [IsGroupoid D] (F : C → D) :
    IsGroupoid (InducedCategory D F) :=
  isGroupoid_of_reflects_iso (inducedFunctor F)

section

instance groupoidPi {I : Type u} {J : I → Type u₂} [∀ i, Groupoid.{v} (J i)] :
    Groupoid.{max u v} (∀ i : I, J i) where
  inv f := fun i : I => Groupoid.inv (f i)
  comp_inv := fun f => by funext i; apply Groupoid.comp_inv
  inv_comp := fun f => by funext i; apply Groupoid.inv_comp

instance groupoidProd {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β] :
    Groupoid.{max u₂ v₂} (α × β) where
  inv f := (Groupoid.inv f.1, Groupoid.inv f.2)

instance isGroupoidPi {I : Type u} {J : I → Type u₂}
    [∀ i, Category.{v} (J i)] [∀ i, IsGroupoid (J i)] :
    IsGroupoid (∀ i : I, J i) where
  all_isIso f := (isIso_pi_iff f).mpr (fun _ ↦ inferInstance)

instance isGroupoidProd {α : Type u} {β : Type u₂} [Category.{v} α] [Category.{v₂} β]
    [IsGroupoid α] [IsGroupoid β] :
    IsGroupoid (α × β) where
  all_isIso f := (isIso_prod_iff (f := f)).mpr ⟨inferInstance, inferInstance⟩

end

end CategoryTheory
