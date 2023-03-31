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
    Internal.addCommGroup (Internal.ofIsoObj (G.obj Q) (iso.app Q)) (Opposite.op P)
  exact
    { homGroup := inferInstance
      add_comp := fun P Q Q' f f' g => by
        let φ : Internal.ofIsoObj (G.obj Q) (iso.app Q) ⟶
          Internal.ofIsoObj (G.obj Q') (iso.app Q') := G.map g
        refine' (Internal.addCommGroup_addMonoidHom' φ g _ (Opposite.op P)).map_add f f'
        erw [← cancel_epi (iso.hom.app Q), ← iso.hom.naturality g]
        apply yoneda.map_injective
        simp [Internal.objFunctor]
      comp_add := fun P P' Q f g g' =>
        (Internal.addCommGroup_addMonoidHom
          (Internal.ofIsoObj (G.obj Q) (iso.app Q)) f.op).map_add g g' }

variable {X Y : C} (f : X ⟶ Y)

open Opposite

end Preadditive

end CategoryTheory
