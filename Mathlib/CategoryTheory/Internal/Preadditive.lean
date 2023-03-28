import Mathlib.CategoryTheory.Internal.Basic
import Mathlib.CategoryTheory.Preadditive.Basic

universe v u

namespace CategoryTheory

namespace Preadditive

variable {C : Type u} [Category.{v} C] (G : C ⥤ Internal AddCommGroupCat C)
  (iso : G ⋙ Internal.objFunctor _ _ ≅ 𝟭 C)

def ofInternalAddCommGroup : Preadditive C := sorry

end Preadditive

end CategoryTheory
