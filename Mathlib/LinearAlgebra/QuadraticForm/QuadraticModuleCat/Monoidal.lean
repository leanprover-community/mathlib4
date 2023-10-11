/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Monoidal.Braided
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

/-- Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`. -/
@[simps! form]
noncomputable abbrev tensorObj (X Y : QuadraticModuleCat.{u} R) : QuadraticModuleCat.{u} R :=
  of (X.form.tmul Y.form)

/-- Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`.

We want this up front so that we can re-use it to define `whiskerLeft` and `whiskerRight`. -/
noncomputable abbrev tensorHom {W X Y Z : QuadraticModuleCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ⟨f.toIsometry.tmul g.toIsometry⟩

/-- Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`. -/
noncomputable abbrev associator (X Y Z : QuadraticModuleCat.{u} R) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  ofIso (tensorAssoc X.form Y.form Z.form)

open MonoidalCategory

theorem forget₂_map_associator_hom (X Y Z : QuadraticModuleCat.{u} R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (associator X Y Z).hom
    = (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).hom := rfl

theorem forget₂_map_associator_inv (X Y Z : QuadraticModuleCat.{u} R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (associator X Y Z).inv
    = (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).inv := rfl

end instMonoidalCategory

open instMonoidalCategory

set_option maxHeartbeats 400000 in
noncomputable instance instMonoidalCategory : MonoidalCategory (QuadraticModuleCat.{u} R) :=
  Monoidal.induced
    (forget₂ (QuadraticModuleCat R) (ModuleCat R))
    { tensorObj := instMonoidalCategory.tensorObj
      μIsoSymm := fun X Y => eqToIso rfl
      whiskerLeft := fun X _ _ f => tensorHom (𝟙 _) f
      whiskerRight := @fun X₁ X₂ (f : X₁ ⟶ X₂) Y => tensorHom f (𝟙 _)
      tensorHom := tensorHom
      tensorUnit' := of (sq (R := R))
      εIsoSymm := eqToIso rfl
      associator := associator
      associator_eq := fun X Y Z => by
        dsimp only [forget₂_obj, forget₂_map_associator_hom]
        simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, MonoidalCategory.tensor_id]
        erw [Category.id_comp, Category.comp_id, MonoidalCategory.tensor_id, Category.comp_id]
        rfl
      leftUnitor := fun X => ofIso (tensorLId X.form)
      rightUnitor := fun X => ofIso (tensorRId X.form)
      -- uncomment these lines to avoid running slow proofs while editing the proof above
      -- whiskerLeft_eq := sorry
      -- whiskerRight_eq := sorry
      -- tensorHom_eq := sorry
      -- leftUnitor_eq := sorry
      -- rightUnitor_eq := sorry
      }

variable (R) in
/-- `forget₂ (QuadraticModuleCat R) (ModuleCat R)` as a monoidal functor. -/
def toModuleCatMonoidalFunctor : MonoidalFunctor (QuadraticModuleCat.{u} R) (ModuleCat.{u} R) :=
  Monoidal.fromInduced (forget₂ (QuadraticModuleCat R) (ModuleCat R)) _

instance : Faithful (toModuleCatMonoidalFunctor R).toFunctor :=
  forget₂_faithful _ _

end

end QuadraticModuleCat
