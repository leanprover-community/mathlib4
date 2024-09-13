/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Closed.Ideal
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Sites.Limits
/-!

# Sheaf categories are cartesian closed

...if the underlying presheaf category is cartesian closed, the target category has finite products,
and there exists a sheafification functor.
-/

noncomputable section

open CategoryTheory Limits

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (A : Type*) [Category A]

instance [HasSheafify J A] [HasFiniteProducts A] [CartesianClosed (Cᵒᵖ ⥤ A)] :
    CartesianClosed (Sheaf J A) :=
  cartesianClosedOfReflective (sheafToPresheaf _ _)
