/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Category of groupoids

This file contains the definition of the category `Grpd` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Grpd ⥤ Type`
and `forgetToCat : Grpd ⥤ Cat`.

## Implementation notes

Though `Grpd` is not a concrete category, we use `Bundled` to define
its carrier type.
-/

assert_not_exists MonoidWithZero

universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of groupoids -/
@[nolint checkUnivs]
def Grpd :=
  Bundled Groupoid.{v, u}

namespace Grpd

instance : Inhabited Grpd :=
  ⟨Bundled.of (SingleObj PUnit)⟩


instance str' (C : Grpd.{v, u}) : Groupoid.{v, u} C.α :=
  C.str

instance : CoeSort Grpd Type* :=
  Bundled.coeSort

/-- Construct a bundled `Grpd` from the underlying type and the typeclass `Groupoid`. -/
def of (C : Type u) [Groupoid.{v} C] : Grpd.{v, u} :=
  Bundled.of C

@[simp]
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl

/-- Category structure on `Grpd` -/
instance category : LargeCategory.{max v u} Grpd.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc := by intros; rfl

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Grpd.{v, u} ⥤ Type u where
  obj := Bundled.α
  map F := F.obj

/-- Forgetting functor to `Cat` -/
def forgetToCat : Grpd.{v, u} ⥤ Cat.{v, u} where
  obj C := Cat.of C
  map := id

instance forgetToCat_full : forgetToCat.Full where map_surjective f := ⟨f, rfl⟩

instance forgetToCat_faithful : forgetToCat.Faithful where

/-- Convert arrows in the category of groupoids to functors,
which sometimes helps in applying simp lemmas -/
theorem comp_eq_comp {C D E : Grpd.{v, u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g :=
  rfl

/-- Converts identity in the category of groupoids to the functor identity -/
theorem id_eq_id {C : Grpd.{v, u}} : 𝟙 C = 𝟭 C :=
  rfl

@[deprecated (since := "2025-09-04")] alias hom_to_functor := comp_eq_comp

@[deprecated "Deprecated in favor of using `CategoryTheory.Grpd.id_eq_id`" (since := "2025-09-04")]
theorem id_to_functor {C : Grpd.{v, u}} : 𝟭 C = 𝟙 C :=
  rfl

section Products

/-- Construct the product over an indexed family of groupoids, as a fan. -/
def piLimitFan ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (∀ j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j

/-- The product fan over an indexed family of groupoids, is a limit cone. -/
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.mkFanLimit (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dsimp only [piLimitFan]
      simp [comp_eq_comp])
    (by
      intro s m w
      apply Functor.pi_ext
      intro j; specialize w j
      simpa)

instance has_pi : Limits.HasProducts.{u} Grpd.{u, u} :=
  Limits.hasProducts_of_limit_fans (by apply piLimitFan) (by apply piLimitFanIsLimit)

/-- The product of a family of groupoids is isomorphic
to the product object in the category of Groupoids -/
noncomputable def piIsoPi (J : Type u) (f : J → Grpd.{u, u}) : @of (∀ j, f j) _ ≅ ∏ᶜ f :=
  Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))

@[simp]
theorem piIsoPi_hom_π (J : Type u) (f : J → Grpd.{u, u}) (j : J) :
    (piIsoPi J f).hom ≫ Limits.Pi.π f j = CategoryTheory.Pi.eval _ j := by
  simp [piIsoPi]
  rfl

end Products

end Grpd

end CategoryTheory
