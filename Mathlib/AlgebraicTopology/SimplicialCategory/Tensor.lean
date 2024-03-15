import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject

universe v u

/-namespace CategoryTheory

open Simplicial SimplicialCategory MonoidalCategory

namespace SSet

open SimplicialObject

def sHomEquiv (K X Y : SSet.{v}) : (K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y) := sorry

def sHomIso (K X Y : SSet.{v}) : sHom (K ⊗ X) Y ≅ sHom K (sHom X Y) := sorry

end SSet

namespace SimplicialCategory

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

class SimplicialTensor (K : SSet.{v}) (X : C) where
  obj : C
  iso : (sHomFunctor C).obj (Opposite.op obj) ≅
    (sHomFunctor C).obj (Opposite.op X) ⋙ (sHomFunctor SSet.{v}).obj (Opposite.op K)
  α' : K ⟶ sHom X obj
  fac (Y : C) : (SSet.sHomEquiv _ _ _).symm (iso.hom.app Y) =
    _ ◁ α' ≫ (β_ _ _).hom ≫ sHomComp X obj Y

section

variable (K : SSet.{v}) (X Y : C) [SimplicialTensor K X]

scoped infixr:70 " ⊗ₛ " => SimplicialTensor.obj

def sTensorα : K ⟶ sHom X (K ⊗ₛ X) := SimplicialTensor.α'

noncomputable def sTensorIso : sHom (K ⊗ₛ X) Y ≅ sHom K (sHom X Y) :=
  SimplicialTensor.iso.app Y

noncomputable def sTensorEquiv : (K ⊗ₛ X ⟶ Y) ≃ (K ⟶ sHom X Y) :=
  (homEquiv' _ _).trans (((sTensorIso K X Y).app (Opposite.op [0])).toEquiv.trans
    (homEquiv' _ _).symm)

variable {K X Y} in
noncomputable abbrev sTensorDesc (f : K ⟶ sHom X Y) : K ⊗ₛ X ⟶ Y :=
  (sTensorEquiv _ _ _).symm f

end

section

variable {K L : SSet.{v}} (f : K ⟶ L) {X Y : C} (g : X ⟶ Y)
  [SimplicialTensor K X] [SimplicialTensor L Y]

noncomputable def sTensorMap :
    K ⊗ₛ X ⟶ L ⊗ₛ Y := sTensorDesc (f ≫ sTensorα L Y ≫ sHomWhiskerRight g _)

scoped infixr:70 " ⊗ₛ " => sTensorMap

end

end SimplicialCategory

end CategoryTheory-/
