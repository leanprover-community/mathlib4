/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries

/-!
# The monoidal category structure on quadratic R-modules

The monoidal structure is simply the structure on the underlying modules, where the tensor product
of two modules is equipped with the form constructed via `QuadraticForm.tmul`.

As with the monoidal structure on `ModuleCat`,
the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

## Implementation notes

This file essentially mirrors `Mathlib/Algebra/Category/AlgebraCat/Monoidal.lean`.
-/

suppress_compilation

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticForm

namespace instMonoidalCategory

/-- Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`. -/
@[simps! form]
noncomputable abbrev tensorObj (X Y : QuadraticModuleCat.{u} R) : QuadraticModuleCat.{u} R :=
  of (X.form.tmul Y.form)

/-- Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`.

We want this up front so that we can re-use it to define `whiskerLeft` and `whiskerRight`. -/
noncomputable abbrev tensorHom {W X Y Z : QuadraticModuleCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ⟨f.toIsometry.tmul g.toIsometry⟩

open MonoidalCategory

end instMonoidalCategory

open instMonoidalCategory


instance : MonoidalCategoryStruct (QuadraticModuleCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of (sq (R := R))
  associator X Y Z := ofIso (tensorAssoc X.form Y.form Z.form)
  leftUnitor X := ofIso (tensorLId X.form)
  rightUnitor X := ofIso (tensorRId X.form)

@[simp] theorem toModuleCat_tensor (X Y : QuadraticModuleCat.{u} R) :
    (X ⊗ Y).toModuleCat = X.toModuleCat ⊗ Y.toModuleCat := rfl

theorem forget₂_map_associator_hom (X Y Z : QuadraticModuleCat.{u} R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (α_ X Y Z).hom =
      (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).hom := rfl

theorem forget₂_map_associator_inv (X Y Z : QuadraticModuleCat.{u} R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (α_ X Y Z).inv =
      (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).inv := rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (QuadraticModuleCat.{u} R) :=
  Monoidal.induced
    (forget₂ (QuadraticModuleCat R) (ModuleCat R))
    { μIso := fun X Y => Iso.refl _
      εIso := Iso.refl _
      leftUnitor_eq := fun X => by
        simp only [forget₂_obj, forget₂_map, Iso.refl_symm, Iso.trans_assoc, Iso.trans_hom,
          Iso.refl_hom, tensorIso_hom, MonoidalCategory.tensorHom_id]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        erw [MonoidalCategory.id_whiskerRight]
        simp
        rfl
      rightUnitor_eq := fun X => by
        simp only [forget₂_obj, forget₂_map, Iso.refl_symm, Iso.trans_assoc, Iso.trans_hom,
          Iso.refl_hom, tensorIso_hom, MonoidalCategory.id_tensorHom]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        erw [MonoidalCategory.whiskerLeft_id]
        simp
        rfl
      associator_eq := fun X Y Z => by
        dsimp only [forget₂_obj, forget₂_map_associator_hom]
        simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, MonoidalCategory.tensor_id]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        rw [Category.id_comp, Category.id_comp, Category.comp_id, MonoidalCategory.tensor_id,
          Category.id_comp] }


variable (R) in
/-- `forget₂ (QuadraticModuleCat R) (ModuleCat R)` as a monoidal functor. -/
def toModuleCatMonoidalFunctor : MonoidalFunctor (QuadraticModuleCat.{u} R) (ModuleCat.{u} R) := by
  unfold instMonoidalCategory
  exact Monoidal.fromInduced (forget₂ (QuadraticModuleCat R) (ModuleCat R)) _

instance : (toModuleCatMonoidalFunctor R).Faithful :=
  forget₂_faithful _ _

end QuadraticModuleCat
