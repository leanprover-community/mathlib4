/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Closed.Ideal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Sheafification

@[expose] public section
/-!

# Sheaf categories are Cartesian closed

...if the underlying presheaf category is Cartesian closed, the target category has
(chosen) finite products, and there exists a sheafification functor.
-/

noncomputable section

open CategoryTheory Limits

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (A : Type*) [Category A]

instance [HasSheafify J A] [CartesianMonoidalCategory A] [CartesianClosed (Cᵒᵖ ⥤ A)] :
    CartesianClosed (Sheaf J A) :=
  cartesianClosedOfReflective (sheafToPresheaf _ _)
