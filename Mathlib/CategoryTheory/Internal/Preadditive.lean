import Mathlib.CategoryTheory.Internal.AddCommGroup
import Mathlib.CategoryTheory.Preadditive.Basic

universe v u

namespace CategoryTheory

open ConcreteCategory

namespace Preadditive

variable {C : Type u} [Category.{v} C] (G : C ⥤ Internal AddCommGroupCat C)
  (iso : G ⋙ Internal.objFunctor _ _ ≅ 𝟭 C)

def ofInternalAddCommGroupCat : Preadditive C := by
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

variable (C)

def toInternalAddCommGroupCatFunctor [Preadditive C] : C ⥤ Internal AddCommGroupCat C where
  obj X :=
  { obj := X
    presheaf :=
    { obj := fun Y => AddCommGroupCat.of (Y.unop ⟶ X)
      map := fun f => AddCommGroupCat.ofHom
        (AddMonoidHom.mk' (fun g => f.unop ≫ g) (by simp)) }
    iso := Iso.refl _ }
  map f :=
  { app := fun Z => by
      dsimp
      exact AddCommGroupCat.ofHom (AddMonoidHom.mk' (fun g => g ≫ f) (by simp)) }
  map_comp := fun f g => by
    apply NatTrans.ext
    ext1 Z
    ext1
    exact (Category.assoc _ _ _).symm


end Preadditive

end CategoryTheory
