import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Functor.CurryingThree

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

open MonoidalCategory Functor

namespace BraidedCategory

namespace Hexagon

variable (C)

/-- (X₁ ⊗ X₂) ⊗ X₂ -/
@[simps!]
def functor₁ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)

/-- X₁ ⊗ (X₂ ⊗ X₃) -/
@[simps!]
def functor₂ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)

/-- (X₂ ⊗ X₃) ⊗ X₁ -/
@[simps!]
def functor₃ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C))

/-- X₂ ⊗ (X₃ ⊗ X₁) -/
@[simps!]
def functor₄ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₁₃

/-- (X₂ ⊗ X₁) ⊗ X₃ -/
@[simps!]
def functor₅ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)

/-- X₂ ⊗ (X₁ ⊗ X₃) -/
@[simps!]
def functor₆ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip

end Hexagon

open Hexagon

namespace ofBifunctor

-- We use the following two defeq abuses
example : (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip =
    (bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)) := by
  rfl

example : (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip =
    (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip).flip.flip₁₃ := by
  rfl

@[simps!]
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₂ C ⟶ functor₃ C :=
  (bifunctorComp₂₃Functor.map β.hom).app _

variable (C) in
@[simps!]
def firstMap₃ : functor₃ C ⟶ functor₄ C where
  app _ := { app _ := { app _ := (α_ _ _ _).hom } }

@[simps!]
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁ C ⟶ functor₅ C :=
  (bifunctorComp₁₂Functor.map β.hom).app _

variable (C) in
@[simps!]
def secondMap₂ : functor₅ C ⟶ functor₆ C where
  app _ := { app _ := { app _ := (α_ _ _ _).hom } }

@[simps!]
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₆ C ⟶ functor₄ C :=
  flip₁₃Functor.map ((flipFunctor _ _ _).map
    ((bifunctorComp₂₃Functor.obj (curriedTensor C)).map ((flipFunctor _ _ _).map β.hom)))


end ofBifunctor

open ofBifunctor

variable (β : curriedTensor C ≅ (curriedTensor C).flip)
  (hexagon_forward : (curriedAssociatorNatIso C).hom ≫ firstMap₂ β ≫ firstMap₃ C =
    secondMap₁ β ≫ secondMap₂ C ≫ secondMap₃ β)
  (hexagon_reverse : _)

def ofBifunctor : BraidedCategory C where
  braiding X Y := (β.app X).app Y
  braiding_naturality_right _ _ _ _ := (β.app _).hom.naturality _
  braiding_naturality_left _ _ := NatTrans.congr_app (β.hom.naturality _) _
  hexagon_forward X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_forward X) Y) Z
  hexagon_reverse := sorry

end CategoryTheory.BraidedCategory
