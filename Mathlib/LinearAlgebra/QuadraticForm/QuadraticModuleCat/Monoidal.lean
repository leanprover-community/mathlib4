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
-/

open CategoryTheory

universe v u

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticForm

noncomputable section

namespace instMonoidalCategory

/-- Auxiliary definition used to fight a tmieout when building
`QuadraticModuleCat.instMonoidalCategory`. -/
@[simps! form]
noncomputable abbrev tensorObj (X Y : QuadraticModuleCat.{u} R) : QuadraticModuleCat.{u} R :=
  of (X.form.tmul Y.form)

/-- Auxiliary definition used to fight a tmieout when building
`QuadraticModuleCat.instMonoidalCategory`. -/
noncomputable abbrev tensorHom {W X Y Z : QuadraticModuleCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ⟨(f.toIsometry.tmul g.toIsometry :)⟩

/-- Auxiliary definition used to fight a tmieout when building
`QuadraticModuleCat.instMonoidalCategory`. -/
@[simps! form]
abbrev tensorUnit : QuadraticModuleCat.{u} R := of (sq (R := R))

set_option maxHeartbeats 3200000 in

/-- Auxiliary definition used to fight a tmieout when building
`QuadraticModuleCat.instMonoidalCategory`. -/
noncomputable abbrev associator (X Y Z : QuadraticModuleCat.{u} R) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) := by
  refine ofIso ?_
  dsimp [tensorObj, of, instModuleCarrierToRingToModuleCatToSemiringToCommSemiringToAddCommMonoidInstAddCommGroupCarrierToRingToModuleCat]
  exact tensorAssoc X.form Y.form Z.form

open MonoidalCategory

@[simp] theorem forget₂_map_associator_hom (X Y Z : QuadraticModuleCat.{u} R) :
  (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (associator X Y Z).hom
    = (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).hom := rfl

@[simp] theorem forget₂_map_associator_inv (X Y Z : QuadraticModuleCat.{u} R) :
  (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (associator X Y Z).inv
    = (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).inv := rfl
end instMonoidalCategory

open instMonoidalCategory

set_option maxHeartbeats 1600000 in
noncomputable instance instMonoidalCategory : MonoidalCategory (QuadraticModuleCat.{u} R) :=
  Monoidal.induced
    (F := forget₂ (QuadraticModuleCat R) (ModuleCat R))
    (tensorObj := instMonoidalCategory.tensorObj)
    (μIsoSymm := fun X Y => eqToIso rfl)
    (whiskerLeft := fun X _ _ f => tensorHom (𝟙 _) f)
    -- (whiskerLeft_eq := sorry)
    (whiskerRight := @fun X₁ X₂ (f : X₁ ⟶ X₂) Y => tensorHom f (𝟙 _))
    -- (whiskerRight_eq := sorry)
    (tensorHom := tensorHom)
    -- (tensorHom_eq := sorry)
    (tensorUnit' := tensorUnit)
    (εIsoSymm := eqToIso rfl)
    (associator := associator)
    (associator_eq := fun X Y Z => by
      dsimp only [forget₂_obj, forget₂_map_associator_hom]
      simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
        MonoidalCategory.tensor_id]
      erw [Category.id_comp, Category.comp_id, MonoidalCategory.tensor_id, Category.comp_id]
      rfl)
    (leftUnitor := fun X => ofIso (tensorLId X.form))
    -- (leftUnitor_eq := sorry)
    (rightUnitor := fun X => ofIso (tensorRId X.form))
    -- (rightUnitor_eq := sorry)

end

end QuadraticModuleCat
