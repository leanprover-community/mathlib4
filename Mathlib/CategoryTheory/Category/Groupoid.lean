/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module category_theory.category.Groupoid
! leanprover-community/mathlib commit c9c9fa15fec7ca18e9ec97306fb8764bfe988a7e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Category of groupoids

This file contains the definition of the category `GroupoidCat` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : GroupoidCat ⥤ Type`
and `forgetToCat : GroupoidCat ⥤ Cat`.

## Implementation notes

Though `GroupoidCat` is not a concrete category, we use `Bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of groupoids -/
@[nolint checkUnivs]
def GroupoidCat :=
  Bundled Groupoid.{v, u}
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid CategoryTheory.GroupoidCat

namespace GroupoidCat

instance : Inhabited GroupoidCat :=
  ⟨Bundled.of (SingleObj PUnit)⟩


instance str' (C : GroupoidCat.{v, u}) : Groupoid.{v, u} C.α :=
  C.str
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.str CategoryTheory.GroupoidCat.str'

instance : CoeSort GroupoidCat (Type _) :=
  Bundled.coeSort

/-- Construct a bundled `GroupoidCat` from the underlying type and the typeclass. -/
def of (C : Type u) [Groupoid.{v} C] : GroupoidCat.{v, u} :=
  Bundled.of C
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.of CategoryTheory.GroupoidCat.of

@[simp]
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.coe_of CategoryTheory.GroupoidCat.coe_of

/-- Category structure on `GroupoidCat` -/
instance category : LargeCategory.{max v u} GroupoidCat.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  id_comp _ := by rfl
  comp_id _ := by rfl
  assoc := by intros ; rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.category CategoryTheory.GroupoidCat.category

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : GroupoidCat.{v, u} ⥤ Type u where
  obj := Bundled.α
  map F := F.obj
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.objects CategoryTheory.GroupoidCat.objects

/-- Forgetting functor to `Cat` -/
def forgetToCat : GroupoidCat.{v, u} ⥤ Cat.{v, u} where
  obj C := Cat.of C
  map := id
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.forget_to_Cat CategoryTheory.GroupoidCat.forgetToCat

instance forgetToCatFull : Full forgetToCat where preimage := id
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.forget_to_Cat_full CategoryTheory.GroupoidCat.forgetToCatFull

instance forgetToCat_faithful : Faithful forgetToCat where
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.forget_to_Cat_faithful CategoryTheory.GroupoidCat.forgetToCat_faithful

/-- Convert arrows in the category of groupoids to functors,
which sometimes helps in applying simp lemmas -/
theorem hom_to_functor {C D E : GroupoidCat.{v, u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.hom_to_functor CategoryTheory.GroupoidCat.hom_to_functor

/-- Converts identity in the category of groupoids to the functor identity -/
theorem id_to_functor {C : GroupoidCat.{v, u}} : 𝟭 C = 𝟙 C :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.id_to_functor CategoryTheory.GroupoidCat.id_to_functor

section Products

--attribute [local tidy] tactic.discrete_cases

/-- Construct the product over an indexed family of groupoids, as a fan. -/
def piLimitFan ⦃J : Type u⦄ (F : J → GroupoidCat.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (∀ j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.pi_limit_fan CategoryTheory.GroupoidCat.piLimitFan

/-- The product fan over an indexed family of groupoids, is a limit cone. -/
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J → GroupoidCat.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.mkFanLimit (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dsimp only [piLimitFan]
      simp [hom_to_functor])
    (by
      intro s m w
      apply Functor.pi_ext
      intro j; specialize w j
      simpa)
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.pi_limit_fan_is_limit CategoryTheory.GroupoidCat.piLimitFanIsLimit

instance has_pi : Limits.HasProducts GroupoidCat.{u, u} :=
  Limits.hasProducts_of_limit_fans (by apply piLimitFan) (by apply piLimitFanIsLimit)
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.has_pi CategoryTheory.GroupoidCat.has_pi

/-- The product of a family of groupoids is isomorphic
to the product object in the category of Groupoids -/
noncomputable def piIsoPi (J : Type u) (f : J → GroupoidCat.{u, u}) : @of (∀ j, f j) _ ≅ ∏ f :=
  Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.pi_iso_pi CategoryTheory.GroupoidCat.piIsoPi

@[simp]
theorem piIsoPi_hom_π (J : Type u) (f : J → GroupoidCat.{u, u}) (j : J) :
    (piIsoPi J f).hom ≫ Limits.Pi.π f j = CategoryTheory.Pi.eval _ j := by
  simp [piIsoPi]
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Groupoid.pi_iso_pi_hom_π CategoryTheory.GroupoidCat.piIsoPi_hom_π

end Products

end GroupoidCat

end CategoryTheory
