/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory

/-!
# Composition of edges in quasicategories

In this file, we define the notions of left and right homotopies on
edges of simplicial sets, and we show that if `X` is a quasicategory,
then edges can be composed (see `SSet.Edge.comp` and `SSet.Edge.compStruct`)
and that this composition satisfies some form of associativity.
The results are deduced from similar results for `2`-truncated quasicategories.

-/

@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial

namespace SSet

variable {X : SSet.{u}}

namespace Edge

variable {x₀ x₁ x₂ : X _⦋0⦌}

/-- A left homotopy between two edges `e` and `e'` is a `CompStruct e (id _) e'`. -/
abbrev HomotopyL (e e' : Edge x₀ x₁) := CompStruct e (.id x₁) e'

/-- A right homotopy between two edges `e` and `e'` is a `CompStruct (id _) e e'`. -/
abbrev HomotopyR (e e' : Edge x₀ x₁) := CompStruct (.id x₀) e e'

variable [Quasicategory X]

/-- The composition of two edges in a quasicategory. -/
@[no_expose]
noncomputable def comp (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
    Edge x₀ x₂ :=
  Truncated.Edge.comp e₀₁ e₁₂

/-- If `e₀₁ : Edge x₀ x₁` and `e₁₂ : Edge x₁ x₂` are edges in a quasicategory,
this is a structure exhibiting the fact that `e₀₁.edge e₁₂` is a composition
of `e₀₁` and `e₁₂`. -/
@[no_expose]
noncomputable def compStruct (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
    CompStruct e₀₁ e₁₂ (e₀₁.comp e₁₂) :=
  Truncated.Edge.compStruct e₀₁ e₁₂

/-- The associativity of the composition of edges in a quasicategory. -/
@[no_expose]
noncomputable def assoc
    {x₀ x₁ x₂ x₃ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂) (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₁ e₁₃ e₀₃) :
    CompStruct e₀₂ e₂₃ e₀₃ :=
  Truncated.Edge.assoc h₀₂ h₁₃ h

/-- The associativity of the composition of edges in a quasicategory. -/
@[no_expose]
noncomputable def assoc'
    {x₀ x₁ x₂ x₃ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂) (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₂ e₂₃ e₀₃) :
    CompStruct e₀₁ e₁₃ e₀₃ :=
  Truncated.Edge.assoc' h₀₂ h₁₃ h

/-- In quasicategory, two left homotopic edges are also right homotopic. -/
noncomputable def HomotopyL.homotopyR {e e' : Edge x₀ x₁} (h : HomotopyL e e') :
    HomotopyR e e' :=
  assoc' (.idComp e) (.compId e) h

/-- In quasicategory, two right homotopic edges are also left homotopic. -/
noncomputable def HomotopyR.homotopyL {e e' : Edge x₀ x₁} (h : HomotopyR e e') :
    HomotopyL e e' :=
  assoc (.idComp e) (.compId e) h

/-- If we have structures `CompStruct e₀₁ e₁₂ e₀₂` and
`CompStruct e₀₁' e₁₂' e₀₂'` involving edges in a quasicategory,
`e₀₁` and `e₀₁'` are left homotopic and `e₁₂` and `e₁₂'` are left homotopic,
then `e₀₂` and `e₀₂'` are left homotopic. -/
@[no_expose]
noncomputable def CompStruct.unique
    {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂)
    {e₀₁' : Edge x₀ x₁} {e₁₂' : Edge x₁ x₂} {e₀₂' : Edge x₀ x₂}
    (h' : CompStruct e₀₁' e₁₂' e₀₂')
    (h₀₁ : HomotopyL e₀₁ e₀₁') (h₁₂ : HomotopyL e₁₂ e₁₂') :
    HomotopyL e₀₂ e₀₂' :=
  Truncated.Edge.CompStruct.unique h h' h₀₁ h₁₂

/-- If we have a structure `CompStruct e₀₁ e₁₂ e₀₂` and `e₀₂` is
left homotopic to `e₀₂'`, then there is a `CompStruct e₀₁ e₁₂ e₀₂'` structure. -/
@[no_expose]
noncomputable def CompStruct.unique'
    {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) {e₀₂' : Edge x₀ x₂}
    (h' : HomotopyL e₀₂ e₀₂') :
    CompStruct e₀₁ e₁₂ e₀₂' :=
  Edge.assoc' h (.compId _) h'

end Edge

end SSet
