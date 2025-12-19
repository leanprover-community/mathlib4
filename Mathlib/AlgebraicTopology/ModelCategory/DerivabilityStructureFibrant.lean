/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The fundamental lemma of homotopical algebra

In this file, we show that if `C` is a model category, then
the localization of the full subcategory of cofibrant objects in `C` with
respect to weak equivalences identifies to the localization of `C` with
respect to weak equivalences.

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type*) [Category C] [ModelCategory C]

namespace FibrantObject

def homRel : HomRel (FibrantObject C) :=
  fun _ _ f g ↦ LeftHomotopyRel f.hom g.hom

lemma homRel_iff_leftHomotopyRel {X Y : FibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel f.hom g.hom := Iff.rfl

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p.hom).precomp i.hom

abbrev π := Quotient (FibrantObject.homRel C)

variable {C}

def toπ : FibrantObject C ⥤ π C := Quotient.functor _

lemma toπ_obj_surjective : Function.Surjective (toπ (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

instance : Functor.Full (toπ (C := C)) := by dsimp [toπ]; infer_instance

lemma toπ_map_eq {X Y : FibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toπ.map f = toπ.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toπ_map_eq_iff {X Y : FibrantObject C} [IsCofibrant X.1] (f g : X ⟶ Y) :
    toπ.map f = toπ.map g ↔ homRel C f g := by
  dsimp [toπ]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    compClosure_homRel]
  refine ⟨?_, .rel _ _⟩
  rw [homRel_iff_leftHomotopyRel]
  intro h
  induction h with
  | rel _ _ h => exact h
  | refl => exact .refl _
  | symm _ _ _ h => exact .symm h
  | trans _ _ _ _ _ h h' => exact .trans h h'

-- dualize the rest..

end FibrantObject

end HomotopicalAlgebra
