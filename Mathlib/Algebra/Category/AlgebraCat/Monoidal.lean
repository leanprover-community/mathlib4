/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The monoidal category structure on R-algebras
-/

open CategoryTheory
open scoped MonoidalCategory

universe v u w v₁ w₁

variable {R : Type u} [CommRing R]

/-- The `R`-algebra equivalence between `ULift A` and `A`. -/
@[simps apply symm_apply]
def ULift.algebraEquiv {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [Algebra R A] :
    ULift A ≃ₐ[R] A :=
  { ULift.ringEquiv with
    toFun := ULift.down
    invFun := ULift.up
    commutes' := fun _ => rfl}

namespace AlgebraCat

noncomputable section

namespace instSemigroupalCategory

open scoped TensorProduct

/-- Auxiliary definition used to fight a timeout when building
`AlgebraCat.instMonoidalCategory`. -/
@[simps!]
noncomputable abbrev tensorObj (X Y : AlgebraCat R) : AlgebraCat R :=
  of R (X ⊗[R] Y)

/-- Auxiliary definition used to fight a timeout when building
`AlgebraCat.instMonoidalCategory`. -/
noncomputable abbrev tensorHom {W X Y Z : AlgebraCat R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  Algebra.TensorProduct.map f g

open SemigroupalCategory

end instSemigroupalCategory

open instSemigroupalCategory

instance : SemigroupalCategoryStruct (AlgebraCat R) where
  tensorObj := tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  associator X Y Z := (Algebra.TensorProduct.assoc R X Y Z).toAlgebraIso

end

open SemigroupalCategory

-- why is it slowwww
theorem forget₂_map_associator_hom (X Y Z : AlgebraCat.{v} R) :
    (forget₂ (AlgebraCat.{v} R) (ModuleCat R)).map (α_ X Y Z).hom =
      (α_
        (forget₂ _ (ModuleCat R) |>.obj X)
        (forget₂ _ (ModuleCat R) |>.obj Y)
        (forget₂ _ (ModuleCat R) |>.obj Z)).hom := by
  rfl

theorem forget₂_map_associator_inv (X Y Z : AlgebraCat.{v} R) :
    (forget₂ (AlgebraCat R) (ModuleCat R)).map (α_ X Y Z).inv =
      (α_
        (forget₂ _ (ModuleCat R) |>.obj X)
        (forget₂ _ (ModuleCat R) |>.obj Y)
        (forget₂ _ (ModuleCat R) |>.obj Z)).inv := by
  rfl

noncomputable def semigroupalInducingFunctorData : Semigroupal.InducingFunctorData
    (forget₂ (AlgebraCat R) (ModuleCat R)) :=
  { μIso := fun X Y => Iso.refl _
    associator_eq := fun X Y Z => TensorProduct.ext_threefold fun x y z => rfl }

noncomputable instance instSemigroupalCategory :
     SemigroupalCategory (AlgebraCat.{v} R) :=
  Semigroupal.induced (forget₂ (AlgebraCat R) (ModuleCat R)) semigroupalInducingFunctorData

/- wouldn't have to give the fData if I hadn't made `SemigroupalFunctor`
work for `SemigroupalCategoryStruct`s and this would be quicker.... -/
variable (R) in
/-- `forget₂ (AlgebraCat R) (ModuleCat R)` as a Semigroupal functor. -/
noncomputable def toModuleCatSemigroupalFunctor :
    SemigroupalFunctor (AlgebraCat R) (ModuleCat R) :=
  Semigroupal.fromInduced (forget₂ (AlgebraCat R) (ModuleCat R)) semigroupalInducingFunctorData

instance : (toModuleCatSemigroupalFunctor R).Faithful :=
  forget₂_faithful _ _

noncomputable instance (priority := high) instMonoidalCategoryStruct :
    MonoidalCategoryStruct (AlgebraCat.{u} R) where
  toSemigroupalCategoryStruct := instSemigroupalCategoryStruct
  tensorUnit := of R R
  leftUnitor X := (Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toAlgebraIso

noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (AlgebraCat R) (ModuleCat R)) :=
  { toInducingFunctorData := semigroupalInducingFunctorData
    εIso := Iso.refl _
    leftUnitor_eq := fun X => by apply TensorProduct.ext; rfl
    rightUnitor_eq := fun X => by apply TensorProduct.ext; rfl }

noncomputable instance (priority := high) instMonoidalCategory :
    MonoidalCategory (AlgebraCat.{u} R) :=
  Monoidal.induced (forget₂ (AlgebraCat R) (ModuleCat R)) inducingFunctorData

variable (R) in
/-- `forget₂ (AlgebraCat R) (ModuleCat R)` as a monoidal functor. -/
noncomputable def toModuleCatMonoidalFunctor :
    MonoidalFunctor (AlgebraCat.{u} R) (ModuleCat.{u} R) :=
  Monoidal.fromInduced (forget₂ (AlgebraCat R) (ModuleCat R)) inducingFunctorData

instance : (toModuleCatMonoidalFunctor R).Faithful :=
  forget₂_faithful _ _

namespace Max

noncomputable instance :
    MonoidalCategoryStruct (AlgebraCat.{max v u} R) where
  toSemigroupalCategoryStruct := instSemigroupalCategoryStruct
  tensorUnit := of R (ULift R)
  leftUnitor X := ((Algebra.TensorProduct.congr ULift.algebraEquiv AlgEquiv.refl).trans <|
    Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := ((Algebra.TensorProduct.congr AlgEquiv.refl ULift.algebraEquiv).trans <|
    Algebra.TensorProduct.rid R R X).toAlgebraIso

noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (AlgebraCat.{max v u} R) (ModuleCat.{max v u} R)) :=
  { toInducingFunctorData := semigroupalInducingFunctorData
    εIso := Iso.refl _
    leftUnitor_eq := fun X => by apply TensorProduct.ext; rfl
    rightUnitor_eq := fun X => by apply TensorProduct.ext; rfl }

noncomputable instance instMonoidalCategory : MonoidalCategory (AlgebraCat.{max v u} R) :=
  Monoidal.induced (forget₂ (AlgebraCat R) (ModuleCat R)) inducingFunctorData

variable (R) in
/-- `forget₂ (AlgebraCat R) (ModuleCat R)` as a monoidal functor. -/
noncomputable def toModuleCatMonoidalFunctor :
    MonoidalFunctor (AlgebraCat.{max v u} R) (ModuleCat.{max v u} R) :=
  Monoidal.fromInduced (forget₂ (AlgebraCat R) (ModuleCat R)) inducingFunctorData

instance : (toModuleCatMonoidalFunctor.{max v u} R).Faithful :=
  forget₂_faithful _ _

end Max
end AlgebraCat
