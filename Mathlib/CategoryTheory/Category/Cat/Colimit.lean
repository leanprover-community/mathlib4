import Mathlib.CategoryTheory.Limits.HasLimits


/-!
# The category of small categories has all small colimits.

In this file, the existence of colimits in `Cat` is deduced from the existence of colimits in the
category of simplicial sets. Indeed, `Cat` identifies to a reflective subcategory of the category
of simplicial sets (see `AlgebraicTopology.SimplicialSet.NerveAdjunction`), so that colimits in
`Cat` can be computed by passing to nerves, taking the colimit in `SSet` and finally applying the
homotopy category functor `SSet ⥤ Cat`.
-/

@[expose] public section


noncomputable section

universe v

open CategoryTheory.Limits

namespace CategoryTheory

namespace Cat

/-- The category of small categories has all small colimits as a reflective subcategory of the
category of simplicial sets, which has all small colimits. -/
instance : HasColimits Cat.{v, v} :=
  hasColimits_of_reflective nerveFunctor

end Cat

end CategoryTheory
