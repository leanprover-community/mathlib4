
/-!
# The category of simplicial sets is a regular epi category

-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

instance : IsRegularEpiCategory SSet.{u} :=
  inferInstanceAs (IsRegularEpiCategory (_ ⥤ _))

end SSet
