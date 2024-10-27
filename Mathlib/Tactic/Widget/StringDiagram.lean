/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Presentation.Expr
import Mathlib.Tactic.CategoryTheory.Monoidal

/-!
# String Diagram Widget

This file provides meta infrastructure for displaying string diagrams for morphisms in monoidal
categories in the infoview. To enable the string diagram widget, you need to import this file and
inserting `with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]` at the beginning of the
proof. Alternatively, you can also write
```lean
open Mathlib.Tactic.Widget
show_panel_widgets [local StringDiagram]
```
to enable the string diagram widget in the current section.

String diagrams are graphical representations of morphisms in monoidal categories, which are
useful for rewriting computations. More precisely, objects in a monoidal category is represented
by strings, and morphisms between two objects is represented by nodes connecting two strings
associated with the objects. The tensor product `X ⊗ Y` corresponds to putting strings associated
with `X` and `Y` horizontally (from left to right), and the composition of morphisms `f : X ⟶ Y`
and `g : Y ⟶ Z` corresponds to connecting two nodes associated with `f` and `g` vertically (from
top to bottom) by strings associated with `Y`.

Currently, the string diagram widget provided in this file deals with equalities of morphisms
in monoidal categories. It displays string diagrams corresponding to the morphisms for the
left-hand and right-hand sides of the equality.

Some examples can be found in `test/StringDiagram.lean`.

When drawing string diagrams, it is common to ignore associators and unitors. We follow this
convention. To do this, we need to extract non-structural morphisms that are not associators
and unitors from lean expressions. This operation is performed using the `Tactic.Monoidal.eval`
function.

A monoidal category can be viewed as a bicategory with a single object. The program in this
file can also be used to display the string diagram for general bicategories (see the wip
PR #12107). With this in mind we will sometimes refer to objects and morphisms in monoidal
categories as 1-morphisms and 2-morphisms respectively, borrowing the terminology of bicategories.
Note that the relation between monoidal categories and bicategories is formalized in
`Mathlib.CategoryTheory.Bicategory.SingleObj`, although the string diagram widget does not use
it directly.

-/

namespace Mathlib.Tactic

open Lean Meta Elab
open CategoryTheory

open Mathlib.Tactic.Monoidal

namespace Widget.StringDiagram

/-! ## Objects in string diagrams -/

/-- Nodes for 2-morphisms in a string diagram. -/
structure AtomNode : Type where
  /-- The vertical position of the node in the string diagram. -/
  vPos : ℕ
  /-- The horizontal position of the node in the string diagram, counting strings in domains. -/
  hPosSrc : ℕ
  /-- The horizontal position of the node in the string diagram, counting strings in codomains. -/
  hPosTar : ℕ
  /-- The underlying expression of the node. -/
  atom : Atom

/-- Nodes for identity 2-morphisms in a string diagram. -/
structure IdNode : Type where
  /-- The vertical position of the node in the string diagram. -/
  vPos : ℕ
  /-- The horizontal position of the node in the string diagram, counting strings in domains. -/
  hPosSrc : ℕ
  /-- The horizontal position of the node in the string diagram, counting strings in codomains. -/
  hPosTar : ℕ
  /-- The underlying expression of the node. -/
  id : Atom₁

/-- Nodes in a string diagram. -/
inductive Node : Type
  | atom : AtomNode → Node
  | id : IdNode → Node

/-- The underlying expression of a node. -/
def Node.e : Node → Expr
  | Node.atom n => n.atom.e
  | Node.id n => n.id.e

/-- The domain of the 2-morphism associated with a node as a list
(the first component is the node itself). -/
def Node.srcList : Node → MetaM (List (Node × Atom₁))
  | Node.atom n => return (← n.atom.src).toList.map (fun f ↦ (.atom n, f))
  | Node.id n => return [(.id n, n.id)]

/-- The codomain of the 2-morphism associated with a node as a list
(the first component is the node itself). -/
def Node.tarList : Node → MetaM (List (Node × Atom₁))
  | Node.atom n => return (← n.atom.tgt).toList.map (fun f ↦ (.atom n, f))
  | Node.id n => return [(.id n, n.id)]

/-- The vertical position of a node in a string diagram. -/
def Node.vPos : Node → ℕ
  | Node.atom n => n.vPos
  | Node.id n => n.vPos

/-- The horizontal position of a node in a string diagram, counting strings in domains. -/
def Node.hPosSrc : Node → ℕ
  | Node.atom n => n.hPosSrc
  | Node.id n => n.hPosSrc

/-- The horizontal position of a node in a string diagram, counting strings in codomains. -/
def Node.hPosTar : Node → ℕ
  | Node.atom n => n.hPosTar
  | Node.id n => n.hPosTar

/-- The list of nodes at the top of a string diagram. -/
def topNodes (η : WhiskerLeftExpr) : MetaM (List Node) := do
  return (← η.src).toList.enum.map (fun (i, f) => .id ⟨0, i, i, f⟩)

/-- Strings in a string diagram. -/
structure Strand : Type where
  /-- The horizontal position of the strand in the string diagram. -/
  hPos : ℕ
  /-- The start point of the strand in the string diagram. -/
  startPoint : Node
  /-- The end point of the strand in the string diagram. -/
  endPoint : Node
  /-- The underlying expression of the strand. -/
  atom₁ : Atom₁

/-- The vertical position of a strand in a string diagram. -/
def Strand.vPos (s : Strand) : ℕ :=
  s.startPoint.vPos

end Widget.StringDiagram

namespace Monoidal

open Widget.StringDiagram

/-- The list of nodes associated with a 2-morphism. The position is counted from the
specified natural numbers. -/
def WhiskerRightExpr.nodes (v h₁ h₂ : ℕ) : WhiskerRightExpr → MetaM (List Node)
  | WhiskerRightExpr.of η => do
    return [.atom ⟨v, h₁, h₂, η⟩]
  | WhiskerRightExpr.whisker η f => do
    let ηs ← η.nodes v h₁ h₂
    let k₁ := (← ηs.mapM (fun n ↦ n.srcList)).join.length
    let k₂ := (← ηs.mapM (fun n ↦ n.tarList)).join.length
    let s : Node := .id ⟨v, h₁ + k₁, h₂ + k₂, f⟩
    return ηs ++ [s]

/-- The list of nodes associated with a 2-morphism. The position is counted from the
specified natural numbers. -/
def WhiskerLeftExpr.nodes (v h₁ h₂ : ℕ) : WhiskerLeftExpr → MetaM (List Node)
  | WhiskerLeftExpr.of η => η.nodes v h₁ h₂
  | WhiskerLeftExpr.whisker f η => do
    let s : Node := .id ⟨v, h₁, h₂, f⟩
    let ss ← η.nodes v (h₁ + 1) (h₂ + 1)
    return s :: ss

/-- The list of nodes at the top of a string diagram. The position is counted from the
specified natural number. -/
def NormalExpr.nodesAux (v : ℕ) : NormalExpr → MetaM (List (List Node))
  | NormalExpr.nil α => return [(α.src).toList.enum.map (fun (i, f) => .id ⟨v, i, i, f⟩)]
  | NormalExpr.cons _ η ηs => do
    let s₁ ← η.nodes v 0 0
    let s₂ ← ηs.nodesAux (v + 1)
    return s₁ :: s₂

/-- The list of nodes associated with a 2-morphism. -/
def NormalExpr.nodes (e : NormalExpr) : MetaM (List (List Node)) := do
  match e with
  | NormalExpr.nil _ => return []
  | NormalExpr.cons _ η _ => return (← topNodes η) :: (← e.nodesAux 1)

/-- `pairs [a, b, c, d]` is `[(a, b), (b, c), (c, d)]`. -/
def pairs {α : Type} : List α → List (α × α) :=
  fun l => l.zip (l.drop 1)

/-- The list of strands associated with a 2-morphism. -/
def NormalExpr.strands (e : NormalExpr) : MetaM (List (List Strand)) := do
  let l ← e.nodes
  (pairs l).mapM fun (x, y) ↦ do
    let xs := (← x.mapM (fun n ↦ n.tarList)).join
    let ys := (← y.mapM (fun n ↦ n.srcList)).join
    if xs.length ≠ ys.length then
      throwError "The number of the start and end points of a string does not match."
    (xs.zip ys).enum.mapM fun (k, (n₁, f₁), (n₂, _)) => do
      return ⟨n₁.hPosTar + k, n₁, n₂, f₁⟩

end Monoidal

namespace Widget.StringDiagram

/-- A type for Penrose variables. -/
structure PenroseVar : Type where
  /-- The identifier of the variable. -/
  ident : String
  /-- The indices of the variable. -/
  indices : List ℕ
  /-- The underlying expression of the variable. -/
  e : Expr

instance : ToString PenroseVar :=
  ⟨fun v => v.ident ++ v.indices.foldl (fun s x => s ++ s!"_{x}") ""⟩

/-- The penrose variable associated with a node. -/
def Node.toPenroseVar (n : Node) : PenroseVar :=
  ⟨"E", [n.vPos, n.hPosSrc, n.hPosTar], n.e⟩

/-- The penrose variable associated with a strand. -/
def Strand.toPenroseVar (s : Strand) : PenroseVar :=
  ⟨"f", [s.vPos, s.hPos], s.atom₁.e⟩

/-! ## Widget for general string diagrams -/

open ProofWidgets Penrose DiagramBuilderM Lean.Server

open scoped Jsx in
/-- Add the variable `v` with the type `tp` to the substance program. -/
def addPenroseVar (tp : String) (v : PenroseVar) :
    DiagramBuilderM Unit := do
  let h := <InteractiveCode fmt={← Widget.ppExprTagged v.e} />
  addEmbed (toString v) tp h

/-- Add constructor `tp v := nm (vs)` to the substance program. -/
def addConstructor (tp : String) (v : PenroseVar) (nm : String) (vs : List PenroseVar) :
    DiagramBuilderM Unit := do
  let vs' := ", ".intercalate (vs.map (fun v => toString v))
  addInstruction s!"{tp} {v} := {nm} ({vs'})"

open scoped Jsx in
/-- Construct a string diagram from a Penrose `sub`stance program and expressions `embeds` to
display as labels in the diagram. -/
def mkStringDiagram (e : NormalExpr) : DiagramBuilderM PUnit := do
  let nodes ← e.nodes
  let strands ← e.strands
  /- Add 2-morphisms. -/
  for x in nodes.join do
    match x with
    | .atom _ => do addPenroseVar "Atom" x.toPenroseVar
    | .id _ => do addPenroseVar "Id" x.toPenroseVar
  /- Add constraints. -/
  for l in nodes do
    for (x₁, x₂) in pairs l do
      addInstruction s!"Left({x₁.toPenroseVar}, {x₂.toPenroseVar})"
  /- Add constraints. -/
  for (l₁, l₂) in pairs nodes do
    if let .some x₁ := l₁.head? then
      if let .some x₂ := l₂.head? then
        addInstruction s!"Above({x₁.toPenroseVar}, {x₂.toPenroseVar})"
  /- Add 1-morphisms as strings. -/
  for l in strands do
    for s in l do
      addConstructor "Mor1" s.toPenroseVar
        "MakeString" [s.startPoint.toPenroseVar, s.endPoint.toPenroseVar]

/-- Penrose dsl file for string diagrams. -/
def dsl :=
  include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.dsl"

/-- Penrose sty file for string diagrams. -/
def sty :=
  include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.sty"

open scoped Jsx in
/-- Construct a string diagram from the expression of a 2-morphism. -/
def fromExpr (e : Expr) : MonoidalM Html := do
  let e' := (← eval e).expr
  DiagramBuilderM.run do
    mkStringDiagram e'
    match ← DiagramBuilderM.buildDiagram dsl sty with
    | some html => return html
    | none => return <span>No non-structural morphisms found.</span>

/-- Given a 2-morphism, return a string diagram. Otherwise `none`. -/
def stringM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some ctx ← mkContext? e | return none
  return some <| ← MonoidalM.run ctx <| fromExpr e

open scoped Jsx in
/-- Help function for displaying two string diagrams in an equality. -/
def mkEqHtml (lhs rhs : Html) : Html :=
  <div className="flex">
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram for LHS</summary> {lhs}
      </details>
    </div>
    <div className="w-50">
      <details «open»={true}>
        <summary className="mv2 pointer">String diagram for RHS</summary> {rhs}
      </details>
    </div>
  </div>

/-- Given an equality between 2-morphisms, return a string diagram of the LHS and RHS.
Otherwise `none`. -/
def stringEqM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | return none
  let some lhs ← stringM? lhs | return none
  let some rhs ← stringM? rhs | return none
  return some <| mkEqHtml lhs rhs

/-- Given an 2-morphism or equality between 2-morphisms, return a string diagram.
Otherwise `none`. -/
def stringMorOrEqM? (e : Expr) : MetaM (Option Html) := do
  if let some html ← stringM? e then
    return some html
  else if let some html ← stringEqM? e then
    return some html
  else
    return none

/-- The `Expr` presenter for displaying string diagrams. -/
@[expr_presenter]
def stringPresenter : ExprPresenter where
  userName := "String diagram"
  layoutKind := .block
  present type := do
    if let some html ← stringMorOrEqM? type then
      return html
    throwError "Couldn't find a 2-morphism to display a string diagram."

open scoped Jsx in
/-- The RPC method for displaying string diagrams. -/
@[server_rpc_method]
def rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let html : Option Html ← (do
      if props.goals.isEmpty then
        return none
      let some g := props.goals[0]? | unreachable!
      g.ctx.val.runMetaM {} do
        g.mvarId.withContext do
          let type ← g.mvarId.getType
          stringEqM? type)
    match html with
    | none => return <span>No String Diagram.</span>
    | some inner => return inner

end StringDiagram

open ProofWidgets

/-- Display the string diagrams if the goal is an equality of morphisms in a monoidal category. -/
@[widget_module]
def StringDiagram : Component PanelWidgetProps :=
  mk_rpc_widget% StringDiagram.rpc

end Mathlib.Tactic.Widget
