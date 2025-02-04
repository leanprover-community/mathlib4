/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Data.Fin.SuccPred

/-!
# A structure to describe transfinite compositions

Given a well-ordered type `J` and a morphisms `f : X ⟶ Y` in a category,
we introduce a structure `TransfiniteCompositionOfShape J f` expressing
that `f` is a transfinite composition of shape `J`.
This allows to extend this structure in order to require
more properties or data for the morphisms `F.obj j ⟶ F.obj (Order.succ j)`
which appear in the transfinite composition.
See `MorphismProperty.TransfiniteCompositionOfShape` in the
file `MorphismProperty.TransfiniteComposition`.

## TODO (@joelriou)
* define relative cell complexes by extending `TransfiniteCompositionOfShape`
and refactor the definition of CW-complexes

-/

universe w w' v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (J : Type w) [LinearOrder J] [OrderBot J]
  {X Y : C} (f : X ⟶ Y)

/-- Given a well-ordered type `J`, a morphism `f : X ⟶ Y` in a category `C`
is a transfinite composition of shape if we have a well order continuous
functor `F : J ⥤ C`, an isomorphism `F.obj ⊥ ≅ X`, a colimit cocone for `F`
whose point is `Y`, such that the composition `X ⟶ F.obj ⊥ ⟶ Y` is `f`. -/
structure TransfiniteCompositionOfShape [SuccOrder J] [WellFoundedLT J] where
  /-- a well order continuous functor `F : J ⥤ C` -/
  F : J ⥤ C
  /-- the isomorphism `F.obj ⊥ ≅ X` -/
  isoBot : F.obj ⊥ ≅ X
  isWellOrderContinuous : F.IsWellOrderContinuous := by infer_instance
  /-- the natural morphism `F.obj j ⟶ Y` -/
  incl : F ⟶ (Functor.const _).obj Y
  /-- the colimit of `F` identifies to `Y` -/
  isColimit : IsColimit (Cocone.mk Y incl)
  fac : isoBot.inv ≫ incl.app ⊥ = f := by aesop_cat

namespace TransfiniteCompositionOfShape

attribute [reassoc (attr := simp)] fac
attribute [instance] isWellOrderContinuous

variable {J f} [SuccOrder J] [WellFoundedLT J] (c : TransfiniteCompositionOfShape J f)

/-- If `f` and `f'` are two isomorphic morphisms, and `f` is a transfinite composition
of shape `J`, then `f'` also is. -/
@[simps]
def ofArrowIso {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    TransfiniteCompositionOfShape J f' where
  F := c.F
  isoBot := c.isoBot ≪≫ Arrow.leftFunc.mapIso e
  incl := c.incl ≫ (Functor.const J).map e.hom.right
  isColimit := IsColimit.ofIsoColimit c.isColimit
    (Cocones.ext (Arrow.rightFunc.mapIso e))

-- to be moved
instance (n : ℕ) (i : Fin (n + 1)) : Unique (i ⟶ Fin.last n) where
  default := homOfLE i.le_last
  uniq _ := rfl

def Fin.lastIsTerminal (n : ℕ) : IsTerminal (Fin.last n) :=
  IsTerminal.ofUnique (Fin.last n)

/-- If `G : ComposableArrows C n`, then `G.hom : G.left ⟶ G.right` is a
transfinite composition of shape `Fin (n + 1)`. -/
@[simps]
def ofComposableArrows {n : ℕ} (G : ComposableArrows C n) :
    TransfiniteCompositionOfShape (Fin (n + 1)) G.hom where
  F := G
  isoBot := Iso.refl _
  isColimit := colimitOfDiagramTerminal (Fin.lastIsTerminal n) G
  fac := Category.id_comp _

/-- If `f` is a transfinite composition of shape `J`, then it is
also a transfinite composition of shape `J'` if `J' ≃o J`. -/
@[simps]
def ofOrderIso {J' : Type w'} [LinearOrder J'] [OrderBot J']
    [SuccOrder J'] [WellFoundedLT J']
    (e : J' ≃o J) :
    TransfiniteCompositionOfShape J' f where
  F := e.equivalence.functor ⋙ c.F
  isoBot := c.F.mapIso (eqToIso sorry) ≪≫ c.isoBot
  incl := whiskerLeft e.equivalence.functor c.incl
  isColimit := IsColimit.whiskerEquivalence (c.isColimit) e.equivalence

end TransfiniteCompositionOfShape

end CategoryTheory
