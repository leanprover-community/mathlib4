/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Basic

/-!
# Properties of objects in a category

Given a category `C`, we introduce an abbreviation `ObjectProperty C`
for predicated `C → Prop`.

-/

universe v u

namespace CategoryTheory

/-- A property of objects in a category `C` is a predicate `C → Prop`. -/
abbrev ObjectProperty (C : Type u) [Category.{v} C] : Type u := C → Prop

end CategoryTheory
