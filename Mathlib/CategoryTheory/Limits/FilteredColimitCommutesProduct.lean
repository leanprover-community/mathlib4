/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Filtered

/-!
Filtered colimits
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasProducts.{v} C] [HasFilteredColimits C]
  {α : Type v}

end CategoryTheory.Limits
