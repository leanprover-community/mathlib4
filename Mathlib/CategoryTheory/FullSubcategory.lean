/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathlib.CategoryTheory.Functor.FullyFaithful

#align_import category_theory.full_subcategory from "leanprover-community/mathlib"@"550b58538991c8977703fdeb7c9d51a5aa27df11"

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
-- Porting note(#5171): removed @[nolint has_nonempty_instance]
@[nolint unusedArguments]
def InducedCategory (_F : C → D) : Type u₁ :=
  C
#align category_theory.induced_category CategoryTheory.InducedCategory

variable {D}

instance InducedCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedCategory D F) α :=
  ⟨fun c => F c⟩
#align category_theory.induced_category.has_coe_to_sort CategoryTheory.InducedCategory.hasCoeToSort

instance InducedCategory.category : Category.{v} (InducedCategory D F) where
  Hom X Y := F X ⟶ F Y
  id X := 𝟙 (F X)
  comp f g := f ≫ g
#align category_theory.induced_category.category CategoryTheory.InducedCategory.category

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps]
def inducedFunctor : InducedCategory D F ⥤ D where
  obj := F
  map f := f
#align category_theory.induced_functor CategoryTheory.inducedFunctor
#align category_theory.induced_functor_map CategoryTheory.inducedFunctor_map
#align category_theory.induced_functor_obj CategoryTheory.inducedFunctor_obj

/-- The induced functor `inducedFunctor F : InducedCategory D F ⥤ D` is fully faithful. -/
def fullyFaithfulInducedFunctor : (inducedFunctor F).FullyFaithful where
  preimage f := f

instance InducedCategory.full : (inducedFunctor F).Full :=
  (fullyFaithfulInducedFunctor F).full
#align category_theory.induced_category.full CategoryTheory.InducedCategory.full

instance InducedCategory.faithful : (inducedFunctor F).Faithful :=
  (fullyFaithfulInducedFunctor F).faithful
#align category_theory.induced_category.faithful CategoryTheory.InducedCategory.faithful

end Induced

section FullSubcategory

variable {C : Type u₁} [Category.{v} C]
variable (Z : C → Prop)

/--
A subtype-like structure for full subcategories. Morphisms just ignore the property. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
subcategories.

See <https://stacks.math.columbia.edu/tag/001D>. We do not define 'strictly full' subcategories.
-/
@[ext]
structure FullSubcategory where
  /-- The category of which this is a full subcategory-/
  obj : C
  /-- The predicate satisfied by all objects in this subcategory-/
  property : Z obj
#align category_theory.full_subcategory CategoryTheory.FullSubcategory
#align category_theory.full_subcategory.ext CategoryTheory.FullSubcategory.ext
#align category_theory.full_subcategory.ext_iff CategoryTheory.FullSubcategory.ext_iff

instance FullSubcategory.category : Category.{v} (FullSubcategory Z) :=
  InducedCategory.category FullSubcategory.obj
#align category_theory.full_subcategory.category CategoryTheory.FullSubcategory.category

-- these lemmas are not particularly well-typed, so would probably be dangerous as simp lemmas

lemma FullSubcategory.id_def (X : FullSubcategory Z) : 𝟙 X = 𝟙 X.obj := rfl

lemma FullSubcategory.comp_def {X Y Z : FullSubcategory Z} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (f ≫ g : X.obj ⟶ Z.obj) := rfl

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def fullSubcategoryInclusion : FullSubcategory Z ⥤ C :=
  inducedFunctor FullSubcategory.obj
#align category_theory.full_subcategory_inclusion CategoryTheory.fullSubcategoryInclusion

@[simp]
theorem fullSubcategoryInclusion.obj {X} : (fullSubcategoryInclusion Z).obj X = X.obj :=
  rfl
#align category_theory.full_subcategory_inclusion.obj CategoryTheory.fullSubcategoryInclusion.obj

@[simp]
theorem fullSubcategoryInclusion.map {X Y} {f : X ⟶ Y} : (fullSubcategoryInclusion Z).map f = f :=
  rfl
#align category_theory.full_subcategory_inclusion.map CategoryTheory.fullSubcategoryInclusion.map

/-- The inclusion of a full subcategory is fully faithful. -/
abbrev fullyFaithfulFullSubcategoryInclusion :
    (fullSubcategoryInclusion Z).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance FullSubcategory.full : (fullSubcategoryInclusion Z).Full :=
  (fullyFaithfulFullSubcategoryInclusion _).full
#align category_theory.full_subcategory.full CategoryTheory.FullSubcategory.full

instance FullSubcategory.faithful : (fullSubcategoryInclusion Z).Faithful :=
  (fullyFaithfulFullSubcategoryInclusion _).faithful
#align category_theory.full_subcategory.faithful CategoryTheory.FullSubcategory.faithful

variable {Z} {Z' : C → Prop}

/-- An implication of predicates `Z → Z'` induces a functor between full subcategories. -/
@[simps]
def FullSubcategory.map (h : ∀ ⦃X⦄, Z X → Z' X) : FullSubcategory Z ⥤ FullSubcategory Z' where
  obj X := ⟨X.1, h X.2⟩
  map f := f
#align category_theory.full_subcategory.map CategoryTheory.FullSubcategory.map
#align category_theory.full_subcategory.map_obj_obj CategoryTheory.FullSubcategory.map_obj_obj
#align category_theory.full_subcategory.map_map CategoryTheory.FullSubcategory.map_map

instance FullSubcategory.full_map (h : ∀ ⦃X⦄, Z X → Z' X) :
  (FullSubcategory.map h).Full where map_surjective f := ⟨f, rfl⟩

instance FullSubcategory.faithful_map (h : ∀ ⦃X⦄, Z X → Z' X) :
  (FullSubcategory.map h).Faithful where

@[simp]
theorem FullSubcategory.map_inclusion (h : ∀ ⦃X⦄, Z X → Z' X) :
    FullSubcategory.map h ⋙ fullSubcategoryInclusion Z' = fullSubcategoryInclusion Z :=
  rfl
#align category_theory.full_subcategory.map_inclusion CategoryTheory.FullSubcategory.map_inclusion

section lift

variable {D : Type u₂} [Category.{v₂} D] (P Q : D → Prop)

/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps]
def FullSubcategory.lift (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) : C ⥤ FullSubcategory P where
  obj X := ⟨F.obj X, hF X⟩
  map f := F.map f
#align category_theory.full_subcategory.lift CategoryTheory.FullSubcategory.lift
#align category_theory.full_subcategory.lift_obj_obj CategoryTheory.FullSubcategory.lift_obj_obj
#align category_theory.full_subcategory.lift_map CategoryTheory.FullSubcategory.lift_map

@[simp]
theorem FullSubcategory.lift_comp_inclusion_eq (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
    FullSubcategory.lift P F hF ⋙ fullSubcategoryInclusion P = F :=
  rfl

/-- Composing the lift of a functor through a full subcategory with the inclusion yields the
    original functor. This is actually true definitionally. -/
def FullSubcategory.lift_comp_inclusion (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
    FullSubcategory.lift P F hF ⋙ fullSubcategoryInclusion P ≅ F :=
  Iso.refl _
#align category_theory.full_subcategory.lift_comp_inclusion CategoryTheory.FullSubcategory.lift_comp_inclusion

@[simp]
theorem fullSubcategoryInclusion_obj_lift_obj (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) {X : C} :
    (fullSubcategoryInclusion P).obj ((FullSubcategory.lift P F hF).obj X) = F.obj X :=
  rfl
#align category_theory.full_subcategory.inclusion_obj_lift_obj CategoryTheory.fullSubcategoryInclusion_obj_lift_obj

@[simp]
theorem fullSubcategoryInclusion_map_lift_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) {X Y : C}
    (f : X ⟶ Y) :
    (fullSubcategoryInclusion P).map ((FullSubcategory.lift P F hF).map f) = F.map f :=
  rfl
#align category_theory.full_subcategory.inclusion_map_lift_map CategoryTheory.fullSubcategoryInclusion_map_lift_map

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
#align category_theory.full_subcategory.lift_comp_map CategoryTheory.FullSubcategory.lift_comp_map

end lift

end FullSubcategory

end CategoryTheory
