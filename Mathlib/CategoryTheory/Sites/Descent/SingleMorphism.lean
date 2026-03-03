/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent data along a single morphism (Mathlib singleton family)

Mathlib’s descent theory is formulated for families of morphisms `f i : X i ⟶ S` via the
category `CategoryTheory.Pseudofunctor.DescentData F f` and the comparison functor
`CategoryTheory.Pseudofunctor.toDescentData F f`.

For a single morphism `p : E ⟶ B`, the relevant family is the singleton family
`fun _ : PUnit => p`. This file provides abbreviations for this special case, together with the
associated “descent” and “effective descent” predicates.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

namespace Pseudofunctor

universe t v' v u' u

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

section

variable {E B : C} (p : E ⟶ B)

/-- The category of descent data for a single morphism `p : E ⟶ B`,
as `F.DescentData` for the singleton family `fun _ : PUnit => p`. -/
abbrev SingleMorphismDescentData : Type _ :=
  F.DescentData (f := fun _ : PUnit.{1} ↦ p)

/-- The comparison functor for descent data along `p : E ⟶ B`,
i.e. `F.toDescentData` for the singleton family. -/
abbrev singleMorphismComparisonFunctor :
    F.obj (.mk (op B)) ⥤ F.DescentData (f := fun _ : PUnit.{1} ↦ p) :=
  F.toDescentData (f := fun _ : PUnit.{1} ↦ p)

/-- `p` is a descent morphism for `F` if the comparison functor is fully faithful. -/
abbrev IsDescentMorphism : Prop :=
  Nonempty (singleMorphismComparisonFunctor (F := F) p).FullyFaithful

/-- `p` is an effective descent morphism for `F` if the comparison functor is an equivalence. -/
abbrev IsEffectiveDescentMorphism : Prop :=
  (singleMorphismComparisonFunctor (F := F) p).IsEquivalence

end

end Pseudofunctor

end CategoryTheory
