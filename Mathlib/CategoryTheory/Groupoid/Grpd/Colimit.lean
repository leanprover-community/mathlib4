/-
Copyright (c) 2019 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Category.Cat.Colimit
import Mathlib.CategoryTheory.Groupoid.Grpd.Core

/-!
# The category of small groupoids has all small colimits

The category of small categories `Cat` has all small colimits.
The category of small groupoids `Grpd` is a coreflective subcategory of `Cat`,
and therefore inherits all colimits from `Cat`.
The right adjoint to the forgetful functor is the core functor `CategoryTheory.Core.functor`.
-/

noncomputable section

universe v

open CategoryTheory.Limits

namespace CategoryTheory

namespace Grpd

/-- The category of small categories has all small colimits as a reflective subcategory of the
category of simplicial sets, which has all small colimits. -/
instance : HasColimits Grpd.{v, v} :=
  hasColimits_of_coreflective forgetToCat

end Grpd

end CategoryTheory
