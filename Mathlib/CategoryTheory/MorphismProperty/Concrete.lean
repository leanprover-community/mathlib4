/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Morphism properties defined in concrete categories

In this file, we define the class of morphisms `MorphismProperty.injective`,
`MorphismProperty.surjective`, `MorphismProperty.bijective` in concrete
categories, and show that it is stable under composition and respect isomorphisms.

-/

universe v u

namespace CategoryTheory

namespace MorphismProperty

variable (C : Type u) [Category.{v} C] [ConcreteCategory C]

open Function

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

/-- Injectiveness (in a concrete category) as a `MorphismProperty` -/
protected def injective : MorphismProperty C := fun _ _ f => Injective f
#align category_theory.morphism_property.injective CategoryTheory.MorphismProperty.injective

/-- Surjectiveness (in a concrete category) as a `MorphismProperty` -/
protected def surjective : MorphismProperty C := fun _ _ f => Surjective f
#align category_theory.morphism_property.surjective CategoryTheory.MorphismProperty.surjective

/-- Bijectiveness (in a concrete category) as a `MorphismProperty` -/
protected def bijective : MorphismProperty C := fun _ _ f => Bijective f
#align category_theory.morphism_property.bijective CategoryTheory.MorphismProperty.bijective

theorem bijective_eq_sup :
    MorphismProperty.bijective C = MorphismProperty.injective C ⊓ MorphismProperty.surjective C :=
  rfl
#align category_theory.morphism_property.bijective_eq_sup CategoryTheory.MorphismProperty.bijective_eq_sup

theorem injective_stableUnderComposition : (MorphismProperty.injective C).StableUnderComposition :=
  fun X Y Z f g hf hg => by
  delta MorphismProperty.injective
  rw [coe_comp]
  exact hg.comp hf
#align category_theory.morphism_property.injective_stable_under_composition CategoryTheory.MorphismProperty.injective_stableUnderComposition

theorem surjective_stableUnderComposition :
    (MorphismProperty.surjective C).StableUnderComposition := fun X Y Z f g hf hg => by
  delta MorphismProperty.surjective
  rw [coe_comp]
  exact hg.comp hf
#align category_theory.morphism_property.surjective_stable_under_composition CategoryTheory.MorphismProperty.surjective_stableUnderComposition

theorem bijective_stableUnderComposition : (MorphismProperty.bijective C).StableUnderComposition :=
  fun X Y Z f g hf hg => by
  delta MorphismProperty.bijective
  rw [coe_comp]
  exact hg.comp hf
#align category_theory.morphism_property.bijective_stable_under_composition CategoryTheory.MorphismProperty.bijective_stableUnderComposition

theorem injective_respectsIso : (MorphismProperty.injective C).RespectsIso :=
  (injective_stableUnderComposition C).respectsIso
    (fun e => ((forget C).mapIso e).toEquiv.injective)
#align category_theory.morphism_property.injective_respects_iso CategoryTheory.MorphismProperty.injective_respectsIso

theorem surjective_respectsIso : (MorphismProperty.surjective C).RespectsIso :=
  (surjective_stableUnderComposition C).respectsIso
    (fun e => ((forget C).mapIso e).toEquiv.surjective)
#align category_theory.morphism_property.surjective_respects_iso CategoryTheory.MorphismProperty.surjective_respectsIso

theorem bijective_respectsIso : (MorphismProperty.bijective C).RespectsIso :=
  (bijective_stableUnderComposition C).respectsIso
    (fun e => ((forget C).mapIso e).toEquiv.bijective)
#align category_theory.morphism_property.bijective_respects_iso CategoryTheory.MorphismProperty.bijective_respectsIso

end MorphismProperty

end CategoryTheory
