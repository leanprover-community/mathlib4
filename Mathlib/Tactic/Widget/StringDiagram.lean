/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Presentation.Expr
import Mathlib.Tactic.CategoryTheory.Monoidal

/-!
# String Diagrams

This file provides tactic/meta infrastructure for displaying string diagrams for morphisms
in monoidal categories in the infoview.

-/

namespace Mathlib.Tactic

open Lean Meta Elab
open CategoryTheory
open Mathlib.Tactic.Coherence

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
def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | [_] => []
  | (x :: y :: ys) => (x, y) :: pairs (y :: ys)

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

/-- The penrose variable assciated with a node. -/
def Node.toPenroseVar (n : Node) : PenroseVar :=
  ⟨"E", [n.vPos, n.hPosSrc, n.hPosTar], n.e⟩

/-- The penrose variable assciated with a strand. -/
def Strand.toPenroseVar (s : Strand) : PenroseVar :=
  ⟨"f", [s.vPos, s.hPos], s.atom₁.e⟩

/-! ## Widget for general string diagrams -/

open ProofWidgets Penrose

-- TODO: Make a PR on ProofWidget4 about the contents of this section.
section DiagramBuilderM

/-! # `DiagramBuilderM` -/

/-- A monad to easily build Penrose diagrams in. -/
abbrev DiagramBuilderM (m : Type → Type) := StateT DiagramState m

namespace DiagramBuilderM

variable {m : Type → Type}

open scoped Jsx in
/-- Assemble the diagram using the provided domain and style programs.

`none` is returned iff nothing was added to the diagram. -/
def buildDiagram [Monad m] (dsl sty : String) (maxOptSteps : Nat := 500) :
    DiagramBuilderM m (Option Html) := do
  let st ← get
  if st.sub == "" && st.embeds.isEmpty then
    return none
  let mut sub := "AutoLabel All\n"
  let mut embedHtmls := #[]
  for (n, (tp, h)) in st.embeds.toArray do
    sub := sub ++ s!"{tp} {n}\n"
    embedHtmls := embedHtmls.push (n, h)
  -- Note: order matters here, embed variables are declared first.
  sub := sub ++ st.sub
  return <Diagram
    embeds={embedHtmls}
    dsl={dsl} sty={sty} sub={sub}
    maxOptSteps={maxOptSteps} />

/-- Add an object `nm` of Penrose type `tp`,
labelled by `h`, to the substance program. -/
def addEmbed [Monad m] (nm : String) (tp : String) (h : Html) : DiagramBuilderM m Unit := do
  modify fun st => { st with embeds := st.embeds.insert nm (tp, h) }

open scoped Jsx in
/-- Add an object of Penrose type `tp`,
corresponding to (and labelled by) the expression `e`,
to the substance program.
Return its Penrose name. -/
def addExpr [Monad m] [MonadLiftT MetaM m] (tp : String) (e : Expr) : DiagramBuilderM m String := do
  let nm ← toString <$> Lean.Meta.ppExpr e
  let h := <InteractiveCode fmt={← Widget.ppExprTagged e} />
  addEmbed nm tp h
  return nm

/-- Add an instruction `i` to the substance program. -/
def addInstruction [Monad m] (i : String) : DiagramBuilderM m Unit := do
  modify fun st => { st with sub := st.sub ++ s!"{i}\n" }

/-- Run a computation in the `DiagramBuilderM` monad. -/
def run {α : Type} [Monad m] (x : DiagramBuilderM m α) : m α :=
  x.run' {}

open scoped Jsx in
/-- Add the variable `v` with the type `tp` to the substance program. -/
def addPenroseVar [Monad m] [MonadLiftT MetaM m] (tp : String) (v : PenroseVar) :
    DiagramBuilderM m Unit := do
  let h := <InteractiveCode fmt={← Widget.ppExprTagged v.e} />
  addEmbed (toString v) tp h

/-- Add constructor `tp v := nm (vs)` to the substance program. -/
def addConstructor [Monad m] (tp : String) (v : PenroseVar) (nm : String) (vs : List PenroseVar) :
    DiagramBuilderM m Unit := do
  let vs' := ", ".intercalate (vs.map (fun v => toString v))
  addInstruction s!"{tp} {v} := {nm} ({vs'})"

end DiagramBuilderM

end DiagramBuilderM

open DiagramBuilderM

open scoped Jsx in
/-- Construct a string diagram from a Penrose `sub`stance program and expressions `embeds` to
display as labels in the diagram. -/
def mkStringDiag (e : Expr) : MonoidalM Html := do
  DiagramBuilderM.run do
    let e' := (← eval e).expr
    let nodes ← e'.nodes
    let strands ← e'.strands
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
    let dsl := include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.dsl"
    let sty := include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.sty"
    match ← buildDiagram dsl sty with
    | some html => return html
    | none => return <span>No 2-morphisms.</span>

/-- Given a 2-morphism, return a string diagram. Otherwise `none`. -/
def stringM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  return some <| ← MonoidalM.run (← mkContext e) <| mkStringDiag e

/-- Given an equality between 2-morphisms, return a string diagram of the LHS. Otherwise `none`. -/
def stringLeftM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, _) := e.eq? | return none
    return some <| ← MonoidalM.run (← mkContext lhs) <| mkStringDiag lhs

/-- Given an equality between 2-morphisms, return a string diagram of the RHS. Otherwise `none`. -/
def stringRightM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, _, rhs) := e.eq? | return none
    return some <| ← MonoidalM.run (← mkContext rhs) <| mkStringDiag rhs

/-- The string diagram widget. -/
@[expr_presenter]
def stringPresenter : ExprPresenter where
  userName := "String diagram"
  layoutKind := .block
  present type := do
    if let some d ← stringM? type then
      return d
    throwError "Couldn't find a string diagram."

open scoped Jsx in
/-- The string diagram widget. -/
@[expr_presenter]
def stringEqPresenter : ExprPresenter where
  userName := "Equality of string diagrams"
  layoutKind := .block
  present type := do
    let some d ← stringLeftM? type
      | throwError "Couldn't find a string diagram."
    let some e ← stringRightM? type
      | throwError "Couldn't find a string diagram."
    return <div className="flex">
      <div className="w-50">{d}</div>
      <div className="w-50">{e}</div>
    </div>

end Mathlib.Tactic.Widget.StringDiagram
