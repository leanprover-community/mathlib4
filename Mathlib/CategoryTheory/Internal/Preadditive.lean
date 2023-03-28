import Mathlib.CategoryTheory.Internal.AddCommGroup
import Mathlib.CategoryTheory.Preadditive.Basic

universe v u

namespace CategoryTheory

open ConcreteCategory

namespace Preadditive

variable {C : Type u} [Category.{v} C] (G : C ⥤ Internal AddCommGroupCat C)
  (iso : G ⋙ Internal.objFunctor _ _ ≅ 𝟭 C)

def ofInternalAddCommGroup : Preadditive C := by
  letI : ∀ (P Q : C), AddCommGroup (P ⟶ Q) := fun P Q =>
    Internal.addCommGroup ((Internal.ofNatIsoObj G iso).obj Q) (Opposite.op P)
  exact
    { homGroup := inferInstance
      add_comp := fun P Q Q' f f' g => by
        sorry
      comp_add := fun P P' Q f g g' =>
        (Internal.addCommGroup_addMonoidHom
          ((Internal.ofNatIsoObj G iso).obj Q) f.op).map_add g g' }

end Preadditive

end CategoryTheory
