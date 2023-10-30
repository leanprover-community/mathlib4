import Mathlib.CategoryTheory.Sites.RegularExtensive
import Mathlib.Topology.Category.TopCat.Basic

universe w w' v u

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w})
    (Y : Type w') [TopologicalSpace Y]

namespace ContinuousMap

def yoneda : C ⥤ Type (max w w') where
  obj X := C(Y, F.obj X)
  map f g := ContinuousMap.comp (F.map f) g

def coyoneda : Cᵒᵖ ⥤ Type (max w w') where
  obj X := C(F.obj (unop X), Y)
  map f g := ContinuousMap.comp g (F.map f.unop)

end ContinuousMap
