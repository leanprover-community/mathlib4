/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Internal.AddCommGroup
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Characterization of additive categories
-/

universe v u

namespace CategoryTheory

open ConcreteCategory

namespace Preadditive

variable {C : Type u} [Category.{v} C] (G : C ⥤ Internal Ab C)
  (iso : G ⋙ Internal.objFunctor _ _ ≅ 𝟭 C)

noncomputable def ofInternalAddCommGroupCat : Preadditive C := by
  letI : ∀ (P Q : C), AddCommGroup (P ⟶ Q) := fun P Q =>
    Internal.addCommGroup (Internal.ofIsoObj (G.obj Q) (iso.app Q)) P
  exact
    { homGroup := inferInstance
      add_comp := fun P Q Q' f f' g => by
        let φ : Internal.ofIsoObj (G.obj Q) (iso.app Q) ⟶
          Internal.ofIsoObj (G.obj Q') (iso.app Q') := G.map g
        refine (Internal.addCommGroup_addMonoidHom' φ g ?_ P).map_add f f'
        erw [← cancel_epi (iso.hom.app Q), ← iso.hom.naturality g]
        apply yoneda.map_injective
        simp [Internal.objFunctor]
      comp_add := fun P P' Q f g g' =>
        (Internal.addCommGroup_addMonoidHom
          (Internal.ofIsoObj (G.obj Q) (iso.app Q)) f).map_add g g' }

variable (C)

@[simps]
def toInternalAddCommGroupCatFunctor [Preadditive C] : C ⥤ Internal Ab C where
  obj X :=
  { obj := X
    presheaf :=
    { obj := fun Y => AddCommGrp.of (Y.unop ⟶ X)
      map := fun f => AddCommGrp.ofHom
        (AddMonoidHom.mk' (fun g => f.unop ≫ g) (by simp)) }
    iso := Iso.refl _ }
  map {X Y} f :=
  { app := fun Z => by
      dsimp
      exact AddCommGrp.ofHom (AddMonoidHom.mk' (fun g => g ≫ f) (by simp))
    naturality := fun A B g ↦ by
      ext h
      simp [AddCommGrp.ofHom] }
  map_comp := fun f g => by
    apply NatTrans.ext
    ext1 Z
    ext1
    exact (Category.assoc _ _ _).symm

noncomputable def toInternalAddCommGroupCatFunctor_comp_objFunctor [Preadditive C] :
    toInternalAddCommGroupCatFunctor C ⋙ Internal.objFunctor _ _ ≅ 𝟭 C :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (fun f => yoneda.map_injective (by aesop_cat))

end Preadditive

end CategoryTheory
