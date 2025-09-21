/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Discrete.Basic
/-!

# Discrete categories are groupoids
-/

namespace CategoryTheory

variable {C : Type*}

instance : Groupoid (Discrete C) := { inv := fun h ↦ ⟨⟨h.1.1.symm⟩⟩ }

instance [Category C] [IsDiscrete C] : IsGroupoid C where

end CategoryTheory
