/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Preadditive monoidal structure on functor categories
-/

public section

namespace CategoryTheory

variable {C A : Type*} [Category C] [Category A] [Preadditive A]
    [MonoidalCategory A] [MonoidalPreadditive A]

instance : MonoidalPreadditive (C ⥤ A) where

end CategoryTheory
