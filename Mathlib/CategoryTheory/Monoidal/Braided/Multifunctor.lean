/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Functor.CurryingThree
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!

# Constructing braided categories from natural transformations between multifunctors

This file provides an alternative constructor for braided categories, given a braiding
`β : -₁ ⊗ -₂ ≅ -₂ ⊗ -₁` as a natural isomorphism between bifunctors. The hexagon identities are
phrased as equalities of natural transformations between trifunctors
`(-₁ ⊗ -₂) ⊗ -₃ ⟶ -₂ ⊗ (-₃ ⊗ -₁)` and `-₁ ⊗ (-₂ ⊗ -₃) ⟶ (-₃ ⊗ -₁) ⊗ -₂`.

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C]

open MonoidalCategory Functor

namespace BraidedCategory

namespace Hexagon

variable (C)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₁ ⊗ X₂) ⊗ X₃` -/
@[simps!]
def functor₁₂₃ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ X₁ ⊗ (X₂ ⊗ X₃)` -/
@[simps!]
def functor₁₂₃' : C ⥤ C ⥤ C ⥤ C := bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₂ ⊗ X₃) ⊗ X₁` -/
@[simps!]
def functor₂₃₁ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C))

/-- The trifunctor `X₁ X₂ X₃ ↦ X₂ ⊗ (X₃ ⊗ X₁)` -/
@[simps!]
def functor₂₃₁' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₁₃

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₂ ⊗ X₁) ⊗ X₃` -/
@[simps!]
def functor₂₁₃ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ X₂ ⊗ (X₁ ⊗ X₃)` -/
@[simps!]
def functor₂₁₃' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip

/-- The trifunctor `X₁ X₂ X₃ ↦ X₃ ⊗ (X₁ ⊗ X₂)` -/
@[simps!]
def functor₃₁₂' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₃ ⊗ X₁) ⊗ X₂` -/
@[simps!]
def functor₃₁₂ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

/-- The trifunctor `X₁ X₂ X₃ ↦ X₁ ⊗ (X₃ ⊗ X₂)` -/
@[simps!]
def functor₁₃₂' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₁ ⊗ X₃) ⊗ X₂` -/
@[simps!]
def functor₁₃₂ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip₂₃

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

/-!

### The forward hexagon identity

Given a braiding in the form of a natural isomorphism of bifunctors
`β : curriedTensor C ≅ (curriedTensor C).flip` (i.e. `(β.app X₁).app X₂ : X₁ ⊗ X₂ ≅ X₂ ⊗ X₁`),
we phrase the forward hexagon identity as an equality of natural transformations between trifunctors
(the hexagon on the left is the diagram we require to commute, the hexagon on the right is the
same on the object level on three objects `X₁ X₂ X₃`).

```
            functor₁₂₃                        (X₁ ⊗ X₂) ⊗ X₃
associator /          \ secondMap₁             /           \
          v            v                      v             v
     functor₁₂₃'    functor₂₁₃          X₁ ⊗ (X₂ ⊗ X₃)    (X₂ ⊗ X₁) ⊗ X₃
firstMap₂ |            |secondMap₂            |             |
          v            v                      v             v
     functor₂₃₁     functor₂₁₃'         (X₂ ⊗ X₃) ⊗ X₁    X₂ ⊗ (X₁ ⊗ X₃)
  firstMap₃\           / secondMap₃            \            /
            v         v                         v          v
             functor₂₃₁'                        X₂ ⊗ (X₃ ⊗ X₁)
```
-/

/-- The middle left map in the forward hexagon identity. -/
@[simps!]
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃' C ⟶ functor₂₃₁ C :=
  (bifunctorComp₂₃Functor.map β.hom).app _

variable (C) in
/-- The bottom left map in the forward hexagon identity. -/
@[simps!]
def firstMap₃ : functor₂₃₁ C ⟶ functor₂₃₁' C where
  app _ := { app _ := { app _ := (α_ _ _ _).hom } }

/-- The top right map in the forward hexagon identity. -/
@[simps!]
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃ C ⟶ functor₂₁₃ C :=
  (bifunctorComp₁₂Functor.map β.hom).app _

variable (C) in
/-- The middle right map in the forward hexagon identity. -/
@[simps!]
def secondMap₂ : functor₂₁₃ C ⟶ functor₂₁₃' C where
  app _ := { app _ := { app _ := (α_ _ _ _).hom } }

/-- The bottom right map in the forward hexagon identity. -/
@[simps!]
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₂₁₃' C ⟶ functor₂₃₁' C :=
  flip₁₃Functor.map ((flipFunctor _ _ _).map
    ((bifunctorComp₂₃Functor.obj (curriedTensor C)).map ((flipFunctor _ _ _).map β.hom)))

end Forward

namespace Reverse

/-!

### The reverse hexagon identity

Given a braiding in the form of a natural isomorphism of bifunctors
`β : curriedTensor C ≅ (curriedTensor C).flip` (i.e. `(β.app X₁).app X₂ : X₁ ⊗ X₂ ≅ X₂ ⊗ X₁`),
we phrase the reverse hexagon identity as an equality of natural transformations between trifunctors
(the hexagon on the left is the diagram we require to commute, the hexagon on the right is the
same on the object level on three objects `X₁ X₂ X₃`).

```
            functor₁₂₃'                       X₁ ⊗ (X₂ ⊗ X₃)
associator /          \ secondMap₁             /           \
          v            v                      v             v
     functor₁₂₃    functor₁₃₂'          (X₁ ⊗ X₂) ⊗ X₃    X₁ ⊗ (X₃ ⊗ X₂)
firstMap₂ |            |secondMap₂            |             |
          v            v                      v             v
     functor₃₁₂'    functor₁₃₂          X₃ ⊗ (X₁ ⊗ X₂)    (X₁ ⊗ X₃) ⊗ X₂
  firstMap₃\           / secondMap₃            \            /
            v         v                         v          v
             functor₃₁₂                        (X₃ ⊗ X₁) ⊗ X₂
```
-/

/-- The middle left map in the reverse hexagon identity. -/
@[simps!]
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃ C ⟶ functor₃₁₂' C :=
  flip₂₃Functor.map ((flipFunctor _ _ _).map ((bifunctorComp₂₃Functor.map
    ((flipFunctor _ _ _).map β.hom)).app _))

variable (C) in
/-- The bottom left map in the reverse hexagon identity. -/
@[simps!]
def firstMap₃ : functor₃₁₂' C ⟶ functor₃₁₂ C :=
  flip₂₃Functor.map ((flipFunctor _ _ _).map (curriedAssociatorNatIso C).inv)

/-- The top right map in the reverse hexagon identity. -/
@[simps!]
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃' C ⟶ functor₁₃₂' C :=
  (bifunctorComp₂₃Functor.obj _).map β.hom

variable (C) in
/-- The middle right map in the reverse hexagon identity. -/
@[simps!]
def secondMap₂ : functor₁₃₂' C ⟶ functor₁₃₂ C where
  app _ := { app _ := { app _ := (α_ _ _ _).inv } }

/-- The bottom right map in the reverse hexagon identity. -/
@[simps!]
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₃₂ C ⟶ functor₃₁₂ C :=
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
@[implicit_reducible]
def ofBifunctor : BraidedCategory C where
  braiding X Y := (β.app X).app Y
  braiding_naturality_right _ _ _ _ := (β.app _).hom.naturality _
  braiding_naturality_left _ _ := NatTrans.congr_app (β.hom.naturality _) _
  hexagon_forward X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_forward X) Y) Z
  hexagon_reverse X Y Z :=
    (NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_reverse X) Y) Z)

end BraidedCategory

open BraidedCategory

/--
Alternative constructor for symmetric categories, where the symmetry of the braiding is phrased
as an equality of natural transformation of bifunctors.
-/
@[implicit_reducible]
def SymmetricCategory.ofCurried [BraidedCategory C]
    (h : (curriedBraidingNatIso C).hom ≫ (flipFunctor _ _ _).map (curriedBraidingNatIso C).hom =
      𝟙 _) :
    SymmetricCategory C where
  symmetry X Y := NatTrans.congr_app (NatTrans.congr_app h X) Y

end CategoryTheory
