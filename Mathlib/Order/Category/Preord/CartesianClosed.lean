/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.Preord.Reflective
public import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.Ideal

/-!
# Cartesian closed structure on `Preord`

`Preord` is a reflective exponential ideal in `Cat`: functor categories with thin codomain
are thin. Hence `Preord` is cartesian closed.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CartesianClosed

noncomputable section

instance : ExponentialIdeal preordToCat.{u} := by
  apply ExponentialIdeal.mk'
  intro P C
  exact ⟨Preord.ofCat (C ⥤ P), ⟨Preord.ofCatIso (C ⥤ P)⟩⟩

namespace Preord

instance : CartesianMonoidalCategory Preord.{u} :=
  .ofReflective preordToCat

instance : BraidedCategory Preord.{u} := .ofCartesianMonoidalCategory

instance : MonoidalClosed Preord.{u} :=
  cartesianClosedOfReflective preordToCat

end Preord

instance : Limits.PreservesFiniteProducts catToPreord.{u} :=
  .of_exponentialIdeal preordToCat
