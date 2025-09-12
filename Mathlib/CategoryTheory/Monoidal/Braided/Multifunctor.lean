/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Functor.CurryingThree
/-!

# Constructing braided categories from natural transformations between multifunctors

This file provides an alternative constructor braided categories, given a braiding
`β : -₁ ⊗ -₂ ≅ -₂ ⊗ -₁` as a natural isomorphism between bifunctors. The hexagon identities are
phrased as equalities of natural transformations between trifunctors
`(-₁ ⊗ -₂) ⊗ -₃ ⟶ -₂ ⊗ (-₃ ⊗ -₁)` and `-₁ ⊗ (-₂ ⊗ -₃) ⟶ (-₃ ⊗ -₁) ⊗ -₂`.

Once we have more API for quadrifunctors, we can add constructors for monoidal category structures
by phrasing the pentagon axiom as an equality of natural transformations between quadrifunctors.
-/

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

open MonoidalCategory Functor

namespace BraidedCategory

namespace Hexagon

variable (C)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₁ ⊗ X₂) ⊗ X₃ -/
@[simps!]
def functor₁ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ X₁ ⊗ (X₂ ⊗ X₃) -/
@[simps!]
def functor₂ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₂ ⊗ X₃) ⊗ X₁ -/
@[simps!]
def functor₃ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C))

/-- The trifunctor `X₁ X₂ X₃ ↦ X₂ ⊗ (X₃ ⊗ X₁) -/
@[simps!]
def functor₄ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₁₃

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₂ ⊗ X₁) ⊗ X₃ -/
@[simps!]
def functor₅ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ X₂ ⊗ (X₁ ⊗ X₃) -/
@[simps!]
def functor₆ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip

/-- The trifunctor `X₁ X₂ X₃ ↦ X₃ ⊗ (X₁ ⊗ X₂) -/
@[simps!]
def functor₇ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₃ ⊗ X₁) ⊗ X₂ -/
@[simps!]
def functor₈ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

/-- The trifunctor `X₁ X₂ X₃ ↦ X₁ ⊗ (X₃ ⊗ X₂) -/
@[simps!]
def functor₉ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₁ ⊗ X₃) ⊗ X₂ -/
@[simps!]
def functor₁₀ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip₂₃

end Hexagon

open Hexagon

namespace ofBifunctor

-- We use the following three defeq abuses, together with `F.flip.flip = F`
example : (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip =
    (bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)) := by
  rfl

example : (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip =
    (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip).flip.flip₁₃ := by
  rfl

example : (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)) =
    (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C)).flip.flip₂₃ := by
  rfl

namespace Forward

/-- The middle left map in the forward hexagon identity. -/
@[simps!]
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₂ C ⟶ functor₃ C :=
  (bifunctorComp₂₃Functor.map β.hom).app _

variable (C) in
/-- The bottom left map in the forward hexagon identity. -/
@[simps!]
def firstMap₃ : functor₃ C ⟶ functor₄ C where
  app _ := { app _ := { app _ := (α_ _ _ _).hom } }

/-- The top right map in the forward hexagon identity. -/
@[simps!]
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁ C ⟶ functor₅ C :=
  (bifunctorComp₁₂Functor.map β.hom).app _

variable (C) in
/-- The middle right map in the forward hexagon identity. -/
@[simps!]
def secondMap₂ : functor₅ C ⟶ functor₆ C where
  app _ := { app _ := { app _ := (α_ _ _ _).hom } }

/-- The bottom right map in the forward hexagon identity. -/
@[simps!]
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₆ C ⟶ functor₄ C :=
  flip₁₃Functor.map ((flipFunctor _ _ _).map
    ((bifunctorComp₂₃Functor.obj (curriedTensor C)).map ((flipFunctor _ _ _).map β.hom)))

end Forward

namespace Reverse

/-- The middle left map in the reverse hexagon identity. -/
@[simps!]
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁ C ⟶ functor₇ C :=
  flip₂₃Functor.map ((flipFunctor _ _ _).map ((bifunctorComp₂₃Functor.map
    ((flipFunctor _ _ _).map β.hom)).app _))

variable (C) in
/-- The bottom left map in the reverse hexagon identity. -/
@[simps!]
def firstMap₃ : functor₇ C ⟶ functor₈ C :=
  flip₂₃Functor.map ((flipFunctor _ _ _).map (curriedAssociatorNatIso C).inv)

/-- The top right map in the reverse hexagon identity. -/
@[simps!]
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₂ C ⟶ functor₉ C :=
  (bifunctorComp₂₃Functor.obj _).map β.hom

variable (C) in
/-- The middle right map in the reverse hexagon identity. -/
@[simps!]
def secondMap₂ : functor₉ C ⟶ functor₁₀ C where
  app _ := { app _ := { app _ := (α_ _ _ _).inv } }

/-- The bottom right map in the reverse hexagon identity. -/
@[simps!]
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₀ C ⟶ functor₈ C :=
  flip₂₃Functor.map ((bifunctorComp₁₂Functor.map β.hom).app _)

end Reverse

end ofBifunctor

open ofBifunctor

variable (β : curriedTensor C ≅ (curriedTensor C).flip)
  (hexagon_forward : (curriedAssociatorNatIso C).hom ≫
    Forward.firstMap₂ β ≫ Forward.firstMap₃ C =
    Forward.secondMap₁ β ≫ Forward.secondMap₂ C ≫ Forward.secondMap₃ β)
  (hexagon_reverse : (curriedAssociatorNatIso C).inv ≫
    Reverse.firstMap₂ β ≫ Reverse.firstMap₃ C =
    Reverse.secondMap₁ β ≫ Reverse.secondMap₂ C ≫ Reverse.secondMap₃ β)

/--
Given a braiding `β : curriedTensor C ≅ (curriedTensor C).flip` as a natural isomorphism between
bifunctors, and the two equalities `hexagon_forward` and `hexagon_reverse` of natural
transformations between trifunctors, we obtain a braided category structure.
-/
def ofBifunctor : BraidedCategory C where
  braiding X Y := (β.app X).app Y
  braiding_naturality_right _ _ _ _ := (β.app _).hom.naturality _
  braiding_naturality_left _ _ := NatTrans.congr_app (β.hom.naturality _) _
  hexagon_forward X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_forward X) Y) Z
  hexagon_reverse X Y Z :=
    (NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_reverse X) Y) Z)

end CategoryTheory.BraidedCategory
