import Mathlib.RingTheory.Coalgebra.Monoidal

universe v u

namespace CoalgCat
variable (R : Type u) [CommRing R]
open CategoryTheory Coalgebra
open scoped TensorProduct MonoidalCategory

@[simps] noncomputable instance : MonoidalCategoryStruct.{u} (CoalgCat R) where
  tensorObj := fun X Y => CoalgCat.of R (X ⊗[R] Y)
  whiskerLeft := fun X _ _ f => CoalgCat.ofHom (lTensor X f)
  whiskerRight := fun f X => CoalgCat.ofHom (rTensor X f)
  tensorHom := fun f g => CoalgCat.ofHom (Coalgebra.TensorProduct.map f g)
  tensorUnit := CoalgCat.of R R
  associator := fun X Y Z => (Coalgebra.TensorProduct.assoc R X Y Z).toCoalgIso
  leftUnitor := fun X => (Coalgebra.TensorProduct.lid R X).toCoalgIso
  rightUnitor := fun X => (Coalgebra.TensorProduct.rid R X).toCoalgIso

set_option profiler true

@[simps] noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (CoalgCat R) (ModuleCat R)) where
  μIso := fun X Y => Iso.refl _
  whiskerLeft_eq := fun X Y Z f => by ext; rfl
  whiskerRight_eq := fun X f => by ext; rfl
  tensorHom_eq := fun f g => by ext; rfl
  εIso := Iso.refl _
  associator_eq := fun X Y Z => TensorProduct.ext <| TensorProduct.ext <| by ext; rfl
  leftUnitor_eq := fun X => TensorProduct.ext <| by ext; rfl
  rightUnitor_eq := fun X => TensorProduct.ext <| by ext; rfl

noncomputable instance : MonoidalCategory (CoalgCat R) :=
  Monoidal.induced (forget₂ _ (ModuleCat R)) (inducingFunctorData R)

end CoalgCat
