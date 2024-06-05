/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The monoidal category structure on R-algebras
-/

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R]

namespace AlgebraCat

noncomputable section

namespace instMonoidalCategory

open scoped TensorProduct

/-- Auxiliary definition used to fight a timeout when building
`AlgebraCat.instMonoidalCategory`. -/
@[simps!]
noncomputable abbrev tensorObj (X Y : AlgebraCat.{u} R) : AlgebraCat.{u} R :=
  of R (X ⊗[R] Y)

/-- Auxiliary definition used to fight a timeout when building
`AlgebraCat.instMonoidalCategory`. -/
noncomputable abbrev tensorHom {W X Y Z : AlgebraCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  Algebra.TensorProduct.map f g

open MonoidalCategory

end instMonoidalCategory

open instMonoidalCategory

instance : MonoidalCategoryStruct (AlgebraCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R R
  associator X Y Z := (Algebra.TensorProduct.assoc R X Y Z).toAlgebraIso
  leftUnitor X := (Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toAlgebraIso

theorem forget₂_map_associator_hom (X Y Z : AlgebraCat.{u} R) :
    (forget₂ (AlgebraCat R) (ModuleCat R)).map (α_ X Y Z).hom =
      (α_
        (forget₂ _ (ModuleCat R) |>.obj X)
        (forget₂ _ (ModuleCat R) |>.obj Y)
        (forget₂ _ (ModuleCat R) |>.obj Z)).hom := by
  rfl

theorem forget₂_map_associator_inv (X Y Z : AlgebraCat.{u} R) :
    (forget₂ (AlgebraCat R) (ModuleCat R)).map (α_ X Y Z).inv =
      (α_
        (forget₂ _ (ModuleCat R) |>.obj X)
        (forget₂ _ (ModuleCat R) |>.obj Y)
        (forget₂ _ (ModuleCat R) |>.obj Z)).inv := by
  rfl

set_option maxHeartbeats 800000 in
noncomputable instance instMonoidalCategory : MonoidalCategory (AlgebraCat.{u} R) :=
  Monoidal.induced
    (forget₂ (AlgebraCat R) (ModuleCat R))
    { μIso := fun X Y => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun X Y Z => by
        dsimp only [forget₂_module_obj, forget₂_map_associator_hom]
        simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, MonoidalCategory.tensor_id]
        erw [Category.id_comp, Category.comp_id, MonoidalCategory.tensor_id, Category.id_comp]
      leftUnitor_eq := fun X => by
        dsimp only [forget₂_module_obj, forget₂_module_map, Iso.refl_symm, Iso.trans_hom,
          Iso.refl_hom, tensorIso_hom]
        erw [Category.id_comp, MonoidalCategory.tensor_id, Category.id_comp]
        rfl
      rightUnitor_eq := fun X => by
        dsimp
        erw [Category.id_comp, MonoidalCategory.tensor_id, Category.id_comp]
        exact congr_arg LinearEquiv.toLinearMap <|
          TensorProduct.AlgebraTensorModule.rid_eq_rid R X }

variable (R) in
/-- `forget₂ (AlgebraCat R) (ModuleCat R)` as a monoidal functor. -/
def toModuleCatMonoidalFunctor : MonoidalFunctor (AlgebraCat.{u} R) (ModuleCat.{u} R) := by
  unfold instMonoidalCategory
  exact Monoidal.fromInduced (forget₂ (AlgebraCat R) (ModuleCat R)) _

instance : (toModuleCatMonoidalFunctor R).Faithful :=
  forget₂_faithful _ _

end

end AlgebraCat
