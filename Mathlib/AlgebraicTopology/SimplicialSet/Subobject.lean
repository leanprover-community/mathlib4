import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Sites.Subsheaf

universe u

open CategoryTheory

namespace SSet

variable (X Y : SSet.{u})

abbrev Subobject := GrothendieckTopology.Subpresheaf X

namespace Subobject

variable {X Y}

variable (S : X.Subobject) (T : Y.Subobject)

abbrev toSSet : SSet.{u} := S.toPresheaf

abbrev ι : S.toSSet ⟶ X := GrothendieckTopology.Subpresheaf.ι S

instance : Mono S.ι := by
  change Mono (GrothendieckTopology.Subpresheaf.ι S)
  infer_instance

def prod : (X ⊗ Y).Subobject := sorry

end Subobject

end SSet
