/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import Lean.Attributes
import Mathlib.Mathport.Syntax
import Mathlib.Control.SimpSet

/-!
# HigherOrder attribute

This file defines the `@[higher_order]` attribute that applies to lemmas of the shape
`∀ x, f (g x) = h x`. It derives an auxiliary lemma of the form `f ∘ g = h` for reasoning about
higher-order functions.
-/

open Lean Name Meta Elab Expr Term

namespace Tactic

/-- `mkComp v e` checks whether `e` is a sequence of nested applications `f (g (h v))`, and if so,
returns the expression `f ∘ g ∘ h`. -/
def mkComp (v : Expr) : Expr → MetaM Expr
| .app f e =>
  if e.equal v then pure f
  else do
    guard !(v.occurs f) <|> throwError "bad guard"
    let e' ← mkComp v e >>= instantiateMVars
    let f ← instantiateMVars f
    mkAppM ``Function.comp #[f, e']
| e => do
  guard (e.equal v)
  let t ← inferType e
  mkAppOptM ``id #[t]

/--
From a lemma of the shape `∀ x, f (g x) = h x`
derive an auxiliary lemma of the form `f ∘ g = h`
for reasoning about higher-order functions.
-/
partial def mkHigherOrderType : Expr → MetaM Expr
| .forallE n d b@(.forallE _ _ _ _) bi =>
  withLocalDecl n bi d fun fvr ↦ do
    let b' := instantiate1 b fvr
    mkHigherOrderType b' >>= fun exp ↦ mkForallFVars #[fvr] exp false true bi
| .forallE n d b bi =>
  withLocalDecl n bi d fun fvr ↦ do
    let b' := instantiate1 b fvr
    let some (_, l, r) ← matchEq? b' | throwError f!"not an equality {b'}"
    let l' ← mkComp fvr l
    let r' ← mkComp fvr r
    mkEq l' r'
| _e =>
  throwError "failed"

/-- A user attribute that applies to lemmas of the shape `∀ x, f (g x) = h x`.
It derives an auxiliary lemma of the form `f ∘ g = h` for reasoning about higher-order functions.
-/
def higherOrderGetParam (thm : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| higher_order $[$id]?) =>
    let onm := id.map TSyntax.getId
    MetaM.run' <| TermElabM.run' <| do
      let inf ← getConstInfo thm
      let lvl := inf.levelParams
      let cst ← mkConst thm (lvl.map mkLevelParam)
      let typ ← inferType cst
      let hot ← mkHigherOrderType typ
      let mex ← mkFreshExprMVar hot
      let mvr₁ := mex.mvarId!
      let (_, mvr₂) ← mvr₁.intros
      let [mvr₃] ← mvr₂.apply (← mkConst ``funext) | throwError "failed"
      let (_, mvr₄) ← mvr₃.intro1
      let lmvr ← mvr₄.apply (← mkConst thm)
      lmvr.forM fun mvr₅ ↦ mvr₅.assumption
      let prf ← instantiateMVars mex
      let thm' := Option.getD (flip updatePrefix thm.getPrefix <$> onm) (thm.appendAfter "\'")
      addDecl <| .thmDecl {
        name := thm',
        levelParams := lvl,
        type := hot,
        value := prf }
      let ref := (id : Option Syntax).getD stx[0]
      addDeclarationRanges thm' {
        range := ← getDeclarationRange (← getRef)
        selectionRange := ← getDeclarationRange ref }
      discard <| addTermInfo (isBinder := true) ref <| ← mkConstWithLevelParams thm'
      let hsm := simpExtension.getState (← getEnv) |>.lemmaNames.contains <| .decl thm
      if hsm then
        addSimpTheorem simpExtension thm' true false .global 1000
      let some fcn ← getSimpExtension? `functor_norm | failure
      let hfm := fcn.getState (← getEnv) |>.lemmaNames.contains <| .decl thm
      if hfm then
        addSimpTheorem fcn thm' true false .global 1000
      return thm'
  | _ => throwUnsupportedSyntax

/-- `higher_order` attribute. -/
initialize higherOrderAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `higherOrder,
    descr :=
"From a lemma of the shape `∀ x, f (g x) = h x` derive an auxiliary lemma of the
form `f ∘ g = h` for reasoning about higher-order functions.",
    getParam := higherOrderGetParam }

end Tactic
