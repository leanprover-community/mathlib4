/-
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.CategoryTheory.Category.Basic

import ProofWidgets.Component.Panel
import ProofWidgets.Component.SelectionPanel
import ProofWidgets.Component.PenroseDiagram

/-! This module defines tactic/meta infrastructure for displaying commutative diagrams in the
infoview. -/

open Lean in
/-- If the expression is a function application of `fName` with 7 arguments, return those arguments.
Otherwise return `none`. -/
@[inline] def _root_.Lean.Expr.app7? (e : Expr) (fName : Name)
    : Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 7 then
    some (
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appArg!,
      e.appFn!.appArg!,
      e.appArg!
    )
  else
    none

namespace Mathlib.Tactic.Widget
open Lean Meta
open ProofWidgets
open CategoryTheory

/-! ## Metaprogramming utilities for breaking down category theory expressions -/

/-- Given a Hom type `α ⟶ β`, return `(α, β)`. Otherwise `none`. -/
def homType? (e : Expr) : Option (Expr × Expr) := do
  let some (_, _, A, B) := e.app4? ``Quiver.Hom | none
  return (A, B)

/-- Given composed homs `g ≫ h`, return `(g, h)`. Otherwise `none`. -/
def homComp? (f : Expr) : Option (Expr × Expr) := do
  let some (_, _, _, _, _, f, g) := f.app7? ``CategoryStruct.comp | none
  return (f, g)

/-- Expressions to display as labels in a diagram. -/
abbrev ExprEmbeds := Array (String × Expr)

/-! ## Widget for general commutative diagrams -/

open scoped Jsx in
/-- Construct a commutative diagram from a Penrose `sub`stance program and expressions `embeds` to
display as labels in the diagram. -/
def mkCommDiag (sub : String) (embeds : ExprEmbeds) : MetaM Html := do
  let embeds ← embeds.mapM fun (s, h) =>
      return (s, Html.ofTHtml <InteractiveCode fmt={← Widget.ppExprTagged h} />)
  return Html.ofTHtml
    <PenroseDiagram
      embeds={embeds}
      dsl={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"commutative.dsl"}
      sty={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"commutativeOpt.sty"}
      sub={sub} />

/-! ## Commutative triangles -/

/--
Triangle with `homs = [f,g,h]` and `objs = [A,B,C]`
```
A f B
  h g
    C
``` -/
def subTriangle := include_str ".."/".."/".."/"widget"/"src"/"penrose"/"triangle.sub"

/-- Given a commutative triangle `f ≫ g = h` or `e ≡ h = f ≫ g`, return a triangle diagram.
Otherwise `none`. -/
def commTriangleM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  if let some (f, g) := homComp? lhs then
    let some (A, C) := homType? (← inferType rhs) | return none
    let some (_, B) := homType? (← inferType f) | return none
    return some <| ← mkCommDiag subTriangle
      #[("A", A), ("B", B), ("C", C),
        ("f", f), ("g", g), ("h", rhs)]
  let some (f, g) := homComp? rhs | return none
  let some (A, C) := homType? (← inferType lhs) | return none
  let some (_, B) := homType? (← inferType f) | return none
  return some <| ← mkCommDiag subTriangle
    #[("A", A), ("B", B), ("C", C),
      ("f", f), ("g", g), ("h", lhs)]

@[expr_presenter]
def commutativeTrianglePresenter : ExprPresenter where
  userName := "Commutative triangle"
  layoutKind := .block
  present type := do
    if let some d ← commTriangleM? type then
      return d
    throwError "Not a commutative triangle."

/-! ## Commutative squares -/

/--
Square with `homs = [f,g,h,i]` and `objs = [A,B,C,D]`
```
A f B
i   g
D h C
``` -/
def subSquare := include_str ".."/".."/".."/"widget"/"src"/"penrose"/"square.sub"

/-- Given a commutative square `f ≫ g = i ≫ h`, return a square diagram. Otherwise `none`. -/
def commSquareM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some (f, g) := homComp? lhs | return none
  let some (i, h) := homComp? rhs | return none
  let some (A, B) := homType? (← inferType f) | return none
  let some (D, C) := homType? (← inferType g) | return none
  some <$> mkCommDiag subSquare
    #[("A", A), ("B", B), ("C", C), ("D", D),
      ("f", f), ("g", g), ("h", h), ("i", i)]

@[expr_presenter]
def commutativeSquarePresenter : ExprPresenter where
  userName := "Commutative square"
  layoutKind := .block
  present type := do
    if let some d ← commSquareM? type then
      return d
    throwError "Not a commutative square."

/-! ## Example diagrams -/

/-- Local instance to make examples work. -/
local instance : Category (Type u) where
  Hom α β := α → β
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

example {f g : Nat ⟶ Bool}: f = g → (f ≫ 𝟙 Bool) = (g ≫ 𝟙 Bool) := by
  withPanelWidgets [SelectionPanel]
    intro h
    exact h

example {fButActuallyTheNameIsReallyLong g : Nat ⟶ Bool}: fButActuallyTheNameIsReallyLong = g →
    fButActuallyTheNameIsReallyLong = (g ≫ 𝟙 Bool) := by
  withPanelWidgets [SelectionPanel]
    intro h
    conv =>
      rhs
      enter [1]
      rw [← h]

-- from Sina Hazratpour
example {X Y Z : Type} {f g : X ⟶ Y} {k : Y ⟶ Y} {f' : Y ⟶ Z} {i : X ⟶ Z}
    (h': g ≫ f' = i) :
    (f ≫ k) = g → ((f ≫ k) ≫ f') = (g ≫ 𝟙 Y ≫ f') := by
  withPanelWidgets [SelectionPanel]
    intro h
    rw [
      h,
      ← Category.assoc g (𝟙 Y) f',
      h',
      Category.comp_id g, h'
    ]

example {X Y Z : Type} {f i : X ⟶ Y}
    {g j : Y ⟶ Z} {h : X ⟶ Z} :
    h = f ≫ g →
    i ≫ j = h →
    f ≫ g = i ≫ j := by
  withPanelWidgets [SelectionPanel]
    intro h₁ h₂
    rw [← h₁, h₂]
