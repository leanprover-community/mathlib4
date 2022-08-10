/-
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Lean.Server.Requests
import Lean.Server.Rpc.Basic
import Lean.Server.Rpc.RequestHandling
import Lean.Elab
import Lean.Widget.UserWidget

-- Please install Node.js and run `lake build widgetCommDiag` before running the rest of this file.
#exit

-- TODO(WN): Remove when category theory is ported
class quiver (V : Type u) where
  hom : V → V → Sort v

infixr:10 " ⟶ " => quiver.hom -- type as \h

class category_struct (obj : Type u) extends quiver.{u,v+1} obj : Type (max u (v+1)) where
  id   : ∀ X : obj, hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

-- https://github.com/leanprover/lean4/issues/1367
prefix:max "𝟙 " => category_struct.id -- type as \b1
infixr:80 " ≫ " => category_struct.comp -- type as \gg

class category (obj : Type u) extends category_struct.{u,v} obj : Type (max u (v+1)) where
  id_comp' : ∀ {X Y : obj} (f : hom X Y), 𝟙 X ≫ f = f
  comp_id' : ∀ {X Y : obj} (f : hom X Y), f ≫ 𝟙 Y = f
  assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
    (f ≫ g) ≫ h = f ≫ (g ≫ h)

instance : category (Type u) where
  hom α β := α → β
  id _ := id
  comp f g := g ∘ f
  id_comp' _ := rfl
  comp_id' _ := rfl
  assoc' _ _ _ := rfl

open Lean.Widget in
@[widget]
def squares : UserWidgetDefinition where
  name := "Commutative diagram"
  javascript := include_str ".." / ".." / ".." / "widget" / "dist" / "commDiag.js"

/-- If the current goal is a commutative diagram, displays that in the infoview. -/
syntax (name := squaresTacStx) "squares!" : tactic
open Lean Elab Tactic in
@[tactic squaresTacStx]
def squaresTac : Tactic
  | stx@`(tactic| squares!) => do
    if let some _ := stx.getPos? then
      Lean.Widget.saveWidgetInfo "squares" Json.null stx
  | _ => throwUnsupportedSyntax

open Lean Widget Server

@[inline] def Lean.Expr.app7? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
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

/-- Given a hom `f : α ⟶ β`, return `(α, β)`. Otherwise `none`. -/
def homTypesM? (f : Expr) : MetaM (Option (Expr × Expr)) := do
  let fTp ← Meta.inferType f >>= instantiateMVars
  let some (_, _, A, B) := fTp.app4? ``quiver.hom | return none
  return (A, B)

/-- Given composed homs `f ≡ g ≫ h`, return `(g, h)`. Otherwise `none`. -/
def homComp? (f : Expr) : Option (Expr × Expr) :=
  if let some (_, _, _, _, _, f, g) := f.app7? ``category_struct.comp then
    some (f, g)
  else none

inductive DiagramKind | square | triangle
deriving Inhabited, FromJson, ToJson

/--
Square with `homs = [f,g,h,i]` and `objs = [A,B,C,D]`
```
A f B
i   g
D h C
```
Triangle with `homs = [f,g,h]` and `objs = [A,B,C]`
```
A f B
  h g
    C
```
-/
structure DiagramData where
  objs : Array CodeWithInfos
  homs : Array CodeWithInfos
  kind : DiagramKind
  deriving Inhabited, RpcEncoding

/-- Given a commutative square `e ≡ f ≫ g = i ≫ h`, return a square diagram. Otherwise `none`. -/
def homSquareM? (e : Expr) : MetaM (Option DiagramData) := do
  let some (_, lhs, rhs) := e.eq? | return none
  let some (f, g) := homComp? lhs | return none
  let some (i, h) := homComp? rhs | return none
  let some (A, B) ← homTypesM? f | return none
  let some (C, D) ← homTypesM? h | return none
  let pp (e : Expr) := ppExprTagged e
  return some {
    objs := #[← pp A, ← pp B, ← pp C, ← pp D]
    homs := #[← pp f, ← pp g, ← pp h, ← pp i]
    kind := .square
  }

/-- Given a commutative triangle `e ≡ f ≫ g = h` or `e ≡ h = f ≫ g`, return a triangle diagram.
Otherwise `none`. -/
def homTriangleM? (e : Expr) : MetaM (Option DiagramData) := do
  let some (_, lhs, rhs) := e.eq? | return none
  let pp (e : Expr) := ppExprTagged e
  if let some (f, g) := homComp? lhs then
    let some (A, C) ← homTypesM? rhs | return none
    let some (_, B) ← homTypesM? f | return none
    return some {
      objs := #[← pp A, ← pp B, ← pp C]
      homs := #[← pp f, ← pp g, ← pp rhs]
      kind := .triangle
    }
  let some (f, g) := homComp? rhs | return none
  let some (A, C) ← homTypesM? lhs | return none
  let some (_, B) ← homTypesM? f | return none
  return some {
    objs := #[← pp A, ← pp B, ← pp C]
    homs := #[← pp f, ← pp g, ← pp lhs]
    kind := .triangle
  }

open Lean Server RequestM in
@[serverRpcMethod]
def getCommutativeDiagram (args : Lean.Lsp.Position) : RequestM (RequestTask (Option DiagramData)) := do
  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos args
  withWaitFindSnapAtPos args fun snap => do
    let g :: _ := snap.infoTree.goalsAt? doc.meta.text pos | return none
    let { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } := g
    let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
    let g :: _ := if useAfter then ti.goalsAfter else ti.goalsBefore | return none
    ci.runMetaM {} <| do
      let some mvarDecl := (← getMCtx).findDecl? g
        | throwError "unknown goal {g.name}"
      let lctx := mvarDecl.lctx
      let lctx := lctx.sanitizeNames.run' { options := (← getOptions) }
      Meta.withLCtx lctx mvarDecl.localInstances do
        let type ← g.getType >>= instantiateMVars
        if let some d ← homSquareM? type then
          return some d
        if let some d ← homTriangleM? type then
          return some d
        return none

example {f g : Nat ⟶ Bool}: f = g → (f ≫ 𝟙 Bool) = (g ≫ 𝟙 Bool) := by
  intro h
  squares!
  exact h

example {f g : Nat ⟶ Bool}: f = g → f = (g ≫ 𝟙 Bool) := by
  intro h
  squares!
  exact h
