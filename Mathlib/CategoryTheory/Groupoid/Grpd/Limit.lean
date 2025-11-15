/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Groupoid.Grpd.Free
import Mathlib.CategoryTheory.Monad.Limits

/-!
# The category of small groupoids has all small limits.

The category of small groupoids `Grpd` is a reflective subcategory of the category
of small categories `Cat`. Hence it inherits all limits that exist in `Cat`.
Since the `Cat` has all small limits, `Grpd` also has all small limits.

-/
noncomputable section

universe u

namespace CategoryTheory

namespace Grpd

instance : Limits.HasLimits Grpd.{u,u} := hasLimits_of_reflective forgetToCat

end Grpd

end CategoryTheory

end
