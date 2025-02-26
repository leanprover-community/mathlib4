/-
Copyright (c) 2025 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Monad.Limits


/-!
# The category of small categories has all small colimits.

A reflective subcategory inherits any colimits present in the ambient category, constructed
by applying the reflector. Thus the fully faithful nerve embedding into simplicial sets and
its left adjoint provide a construction of colimits in the category of small categories.
-/


noncomputable section

universe v

open CategoryTheory.Limits

namespace CategoryTheory

namespace Cat

/-- The category of small categories has all small colimits as a reflective subcategory of the
category of simplicial sets, which has all small colimits.-/

instance : HasColimits Cat.{v, v} :=
  hasColimits_of_reflective nerveFunctor

end Cat

end CategoryTheory
