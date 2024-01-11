/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.TensorProduct

/-!
# The monoidal category structure on R-algebras
-/

open CategoryTheory

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

/-- Auxiliary definition used to fight a timeout when building
`AlgebraCat.instMonoidalCategory`. -/
@[simps!]
abbrev tensorUnit : AlgebraCat.{u} R := of R R

/-- Auxiliary definition used to fight a timeout when building
`AlgebraCat.instMonoidalCategory`. -/
noncomputable abbrev associator (X Y Z : AlgebraCat.{u} R) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  (Algebra.TensorProduct.assoc R X Y Z).toAlgebraIso

open MonoidalCategory

theorem forget₂_map_associator_hom (X Y Z : AlgebraCat.{u} R) :
    (forget₂ (AlgebraCat R) (ModuleCat R)).map (associator X Y Z).hom =
      (α_
        (forget₂ _ (ModuleCat R) |>.obj X)
        (forget₂ _ (ModuleCat R) |>.obj Y)
        (forget₂ _ (ModuleCat R) |>.obj Z)).hom := by
  rfl

theorem forget₂_map_associator_inv (X Y Z : AlgebraCat.{u} R) :
    (forget₂ (AlgebraCat R) (ModuleCat R)).map (associator X Y Z).inv =
      (α_
        (forget₂ _ (ModuleCat R) |>.obj X)
        (forget₂ _ (ModuleCat R) |>.obj Y)
        (forget₂ _ (ModuleCat R) |>.obj Z)).inv := by
  rfl

end instMonoidalCategory

open instMonoidalCategory

set_option maxHeartbeats 800000 in
noncomputable instance instMonoidalCategory : MonoidalCategory (AlgebraCat.{u} R) :=
  Monoidal.induced
    (forget₂ (AlgebraCat R) (ModuleCat R))
    { tensorObj := instMonoidalCategory.tensorObj
      μIsoSymm := fun X Y => Iso.refl _
      whiskerLeft := fun X _ _ f => tensorHom (𝟙 _) f
      whiskerRight := @fun X₁ X₂ (f : X₁ ⟶ X₂) Y => tensorHom f (𝟙 _)
      tensorHom := tensorHom
      tensorUnit' := tensorUnit
      εIsoSymm := Iso.refl _
      associator := associator
      associator_eq := fun X Y Z => by
        dsimp only [forget₂_module_obj, forget₂_map_associator_hom]
        simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, MonoidalCategory.tensor_id]
        erw [Category.id_comp, Category.comp_id, MonoidalCategory.tensor_id, Category.comp_id]
      leftUnitor := fun X => (Algebra.TensorProduct.lid R X).toAlgebraIso
      rightUnitor := fun X => (Algebra.TensorProduct.rid R R X).toAlgebraIso
      rightUnitor_eq := fun X => by
        dsimp
        erw [Category.id_comp, MonoidalCategory.tensor_id, Category.id_comp]
        exact congr_arg LinearEquiv.toLinearMap <|
          TensorProduct.AlgebraTensorModule.rid_eq_rid R X }

variable (R) in
/-- `forget₂ (AlgebraCat R) (ModuleCat R)` as a monoidal functor. -/
def toModuleCatMonoidalFunctor : MonoidalFunctor (AlgebraCat.{u} R) (ModuleCat.{u} R) :=
  Monoidal.fromInduced (forget₂ (AlgebraCat R) (ModuleCat R)) _

instance : Faithful (toModuleCatMonoidalFunctor R).toFunctor :=
  forget₂_faithful _ _

end

end AlgebraCat
