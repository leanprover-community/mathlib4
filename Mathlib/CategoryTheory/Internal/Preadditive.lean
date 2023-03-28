import Mathlib.CategoryTheory.Internal.AddCommGroup
import Mathlib.CategoryTheory.Preadditive.Basic

universe v u

namespace CategoryTheory

namespace Preadditive

variable {C : Type u} [Category.{v} C] (G : C ⥤ Internal AddCommGroupCat C)
  (iso : G ⋙ Internal.objFunctor _ _ ≅ 𝟭 C)

def ofInternalAddCommGroup : Preadditive C where
  homGroup P Q := Internal.addCommGroup ((Internal.ofNatIsoObj G iso).obj Q) (Opposite.op P)
  add_comp := sorry
  comp_add := sorry

end Preadditive

end CategoryTheory
