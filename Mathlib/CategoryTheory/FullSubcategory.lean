/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Induced categories and full subcategories

Given a category `D` and a function `F : C → D `from a type `C` to the
objects of `D`, there is an essentially unique way to give `C` a
category structure such that `F` becomes a fully faithful functor,
namely by taking $$ Hom_C(X, Y) = Hom_D(FX, FY) $$. We call this the
category induced from `D` along `F`.

As a special case, if `C` is a subtype of `D`,
this produces the full subcategory of `D` on the objects belonging to `C`.
In general the induced category is equivalent to the full subcategory of `D` on the
image of `F`.

## Implementation notes

It looks odd to make `D` an explicit argument of `InducedCategory`,
when it is determined by the argument `F` anyways. The reason to make `D`
explicit is in order to control its syntactic form, so that instances
like `InducedCategory.has_forget₂` (elsewhere) refer to the correct
form of `D`. This is used to set up several algebraic categories like

  def CommMon : Type (u+1) := InducedCategory Mon (Bundled.map @CommMonoid.toMonoid)
  -- not `InducedCategory (Bundled Monoid) (Bundled.map @CommMonoid.toMonoid)`,
  -- even though `MonCat = Bundled Monoid`!
-/


namespace CategoryTheory

universe v v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]
variable (F : C → D)

/-- `InducedCategory D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint unusedArguments]
def InducedCategory (_F : C → D) : Type u₁ :=
  C

variable {D}

instance InducedCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedCategory D F) α :=
  ⟨fun c => F c⟩

instance InducedCategory.category : Category.{v} (InducedCategory D F) where
  Hom X Y := F X ⟶ F Y
  id X := 𝟙 (F X)
  comp f g := f ≫ g

variable {F} in
/-- Construct an isomorphism in the induced category
from an isomorphism in the original category. -/
@[simps] def InducedCategory.isoMk {X Y : InducedCategory D F} (f : F X ≅ F Y) : X ≅ Y where
  hom := f.hom
  inv := f.inv
  hom_inv_id := f.hom_inv_id
  inv_hom_id := f.inv_hom_id

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps]
def inducedFunctor : InducedCategory D F ⥤ D where
  obj := F
  map f := f

/-- The induced functor `inducedFunctor F : InducedCategory D F ⥤ D` is fully faithful. -/
def fullyFaithfulInducedFunctor : (inducedFunctor F).FullyFaithful where
  preimage f := f

instance InducedCategory.full : (inducedFunctor F).Full :=
  (fullyFaithfulInducedFunctor F).full

instance InducedCategory.faithful : (inducedFunctor F).Faithful :=
  (fullyFaithfulInducedFunctor F).faithful

end Induced

section FullSubcategory

variable {C : Type u₁} [Category.{v} C]
variable (Z : C → Prop)

/--
A subtype-like structure for full subcategories. Morphisms just ignore the property. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
subcategories. -/
@[ext, stacks 001D "We do not define 'strictly full' subcategories."]
structure FullSubcategory where
  /-- The category of which this is a full subcategory -/
  obj : C
  /-- The predicate satisfied by all objects in this subcategory -/
  property : Z obj

instance FullSubcategory.category : Category.{v} (FullSubcategory Z) :=
  InducedCategory.category FullSubcategory.obj

-- these lemmas are not particularly well-typed, so would probably be dangerous as simp lemmas

lemma FullSubcategory.id_def (X : FullSubcategory Z) : 𝟙 X = 𝟙 X.obj := rfl

lemma FullSubcategory.comp_def {X Y Z : FullSubcategory Z} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (f ≫ g : X.obj ⟶ Z.obj) := rfl

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def fullSubcategoryInclusion : FullSubcategory Z ⥤ C :=
  inducedFunctor FullSubcategory.obj

@[simp]
theorem fullSubcategoryInclusion.obj {X} : (fullSubcategoryInclusion Z).obj X = X.obj :=
  rfl

@[simp]
theorem fullSubcategoryInclusion.map {X Y} {f : X ⟶ Y} : (fullSubcategoryInclusion Z).map f = f :=
  rfl

/-- The inclusion of a full subcategory is fully faithful. -/
abbrev fullyFaithfulFullSubcategoryInclusion :
    (fullSubcategoryInclusion Z).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance FullSubcategory.full : (fullSubcategoryInclusion Z).Full :=
  (fullyFaithfulFullSubcategoryInclusion _).full

instance FullSubcategory.faithful : (fullSubcategoryInclusion Z).Faithful :=
  (fullyFaithfulFullSubcategoryInclusion _).faithful

variable {Z} {Z' : C → Prop}

/-- An implication of predicates `Z → Z'` induces a functor between full subcategories. -/
@[simps]
def FullSubcategory.map (h : ∀ ⦃X⦄, Z X → Z' X) : FullSubcategory Z ⥤ FullSubcategory Z' where
  obj X := ⟨X.1, h X.2⟩
  map f := f

instance FullSubcategory.full_map (h : ∀ ⦃X⦄, Z X → Z' X) :
  (FullSubcategory.map h).Full where map_surjective f := ⟨f, rfl⟩

instance FullSubcategory.faithful_map (h : ∀ ⦃X⦄, Z X → Z' X) :
  (FullSubcategory.map h).Faithful where

@[simp]
theorem FullSubcategory.map_inclusion (h : ∀ ⦃X⦄, Z X → Z' X) :
    FullSubcategory.map h ⋙ fullSubcategoryInclusion Z' = fullSubcategoryInclusion Z :=
  rfl

section lift

variable {D : Type u₂} [Category.{v₂} D] (P Q : D → Prop)

/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps]
def FullSubcategory.lift (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) : C ⥤ FullSubcategory P where
  obj X := ⟨F.obj X, hF X⟩
  map f := F.map f

@[simp]
theorem FullSubcategory.lift_comp_inclusion_eq (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
    FullSubcategory.lift P F hF ⋙ fullSubcategoryInclusion P = F :=
  rfl

/-- Composing the lift of a functor through a full subcategory with the inclusion yields the
    original functor. This is actually true definitionally. -/
def FullSubcategory.lift_comp_inclusion (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
    FullSubcategory.lift P F hF ⋙ fullSubcategoryInclusion P ≅ F :=
  Iso.refl _

@[simp]
theorem fullSubcategoryInclusion_obj_lift_obj (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) {X : C} :
    (fullSubcategoryInclusion P).obj ((FullSubcategory.lift P F hF).obj X) = F.obj X :=
  rfl

@[simp]
theorem fullSubcategoryInclusion_map_lift_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) {X Y : C}
    (f : X ⟶ Y) :
    (fullSubcategoryInclusion P).map ((FullSubcategory.lift P F hF).map f) = F.map f :=
  rfl

instance (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [F.Faithful] :
    (FullSubcategory.lift P F hF).Faithful :=
  Functor.Faithful.of_comp_iso (FullSubcategory.lift_comp_inclusion P F hF)

instance (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [F.Full] : (FullSubcategory.lift P F hF).Full :=
  Functor.Full.of_comp_faithful_iso (FullSubcategory.lift_comp_inclusion P F hF)

@[simp]
theorem FullSubcategory.lift_comp_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) (h : ∀ ⦃X⦄, P X → Q X) :
    FullSubcategory.lift P F hF ⋙ FullSubcategory.map h =
      FullSubcategory.lift Q F fun X => h (hF X) :=
  rfl

end lift

end FullSubcategory

end CategoryTheory
