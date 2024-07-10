/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Closed.Ideal
import Mathlib.CategoryTheory.Sites.Limits
/-!

# Sheaf categories are cartesian closed

...if the underlying presheaf category is cartesian closed, the target category has finite products,
and there exists a sheafification functor.
-/

noncomputable section

open CategoryTheory Limits

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (A : Type*) [Category A]

instance [HasWeakSheafify J A] : Reflective (sheafToPresheaf J A) where
  map_surjective := (fullyFaithfulSheafToPresheaf _ _).map_surjective
  map_injective := (fullyFaithfulSheafToPresheaf _ _).map_injective
  adj := sheafificationAdjunction _ _

instance [HasSheafify J A] :  PreservesLimitsOfShape (Discrete (WalkingPair))
    (reflector (sheafToPresheaf J A)) :=
  inferInstanceAs (PreservesLimitsOfShape _ (presheafToSheaf _ _))

instance [HasFiniteProducts A] : HasFiniteProducts (Cᵒᵖ ⥤ A) := ⟨inferInstance⟩

instance [HasSheafify J A] [HasFiniteProducts A] [CartesianClosed (Cᵒᵖ ⥤ A)] :
    CartesianClosed (Sheaf J A) :=
  cartesianClosedOfReflective (sheafToPresheaf _ _)
