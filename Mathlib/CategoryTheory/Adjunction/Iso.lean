/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.MorphismProperty
/-!

# Isomorphisms via the unit and counit

This file proves the following result `CategoryTheory.Adjunction.isIso_counit_of_iso`:
Given an adjunction `L ⊣ R` and an isomorphism `X ≅ L.obj Y`, with `L` fully faithful,
the counit `L.obj (R.obj X) ⟶ X` is an isomorphism.

We also prove the dual result about the unit in the case where the right adjoint is fully faithful.
-/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

instance [L.Faithful] [L.Full] {Y : C} : IsIso (adj.counit.app (L.obj Y)) :=
  isIso_of_hom_comp_eq_id _ (adj.left_triangle_components Y)

lemma isIso_counit_app_of_iso [L.Faithful] [L.Full] (X : D) (Y : C) (e : X ≅ L.obj Y) :
    IsIso (adj.counit.app X) := by
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  infer_instance

instance [R.Faithful] [R.Full] {Y : D} : IsIso (adj.unit.app (R.obj Y)) :=
  isIso_of_comp_hom_eq_id _ (adj.right_triangle_components Y)

lemma isIso_unit_app_of_iso [R.Faithful] [R.Full] (X : D) (Y : C) (e : Y ≅ R.obj X) :
    IsIso (adj.unit.app Y) := by
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  infer_instance

end CategoryTheory.Adjunction
