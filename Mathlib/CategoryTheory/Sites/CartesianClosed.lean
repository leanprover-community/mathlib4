/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Closed.Ideal
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Sites.Sheafification
/-!

# Sheaf categories are cartesian closed

...if the underlying presheaf category is cartesian closed, the target category has
(chosen) finite products, and there exists a sheafification functor.
-/

noncomputable section

open CategoryTheory Limits

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (A : Type*) [Category A]

#adaptation_note /-- Added instance. -/
instance [HasSheafify J A] [ChosenFiniteProducts A] : ChosenFiniteProducts (Sheaf J A) :=
  reflectiveChosenFiniteProducts (sheafToPresheaf _ _)

instance [HasSheafify J A] [ChosenFiniteProducts A] [CartesianClosed (Cᵒᵖ ⥤ A)] :
    CartesianClosed (Sheaf J A) :=
  cartesianClosedOfReflective (sheafToPresheaf _ _)
