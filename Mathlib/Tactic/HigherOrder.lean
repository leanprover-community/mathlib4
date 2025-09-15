/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assumption
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Intro
import Lean.Elab.DeclarationRange
import Mathlib.Tactic.Attr.Register

/-!
# HigherOrder attribute

This file defines the `@[higher_order]` attribute that applies to lemmas of the shape
`∀ x, f (g x) = h x`. It derives an auxiliary lemma of the form `f ∘ g = h` for reasoning about
higher-order functions.
-/

open Lean Name Meta Elab Expr Term

namespace Lean.Parser.Attr

syntax (name := higherOrder) "higher_order" (ppSpace ident)? : attr

end Lean.Parser.Attr

namespace Tactic

/-- `mkComp v e` checks whether `e` is a sequence of nested applications `f (g (h v))`, and if so,
returns the expression `f ∘ g ∘ h`. If `e = v` it returns `id`. -/
def mkComp (v : Expr) : Expr → MetaM Expr
  | .app f e =>
    if e.equal v then
      return f
    else do
      if v.occurs f then
        throwError "mkComp failed occurs check"
      let e' ← mkComp v e
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
partial def mkHigherOrderType (e : Expr) : MetaM Expr := do
  if not e.isForall then
    throwError "not a forall"
  withLocalDecl e.bindingName! e.binderInfo e.bindingDomain! fun fvar => do
    let body := instantiate1 e.bindingBody! fvar
    if body.isForall then
      let exp ← mkHigherOrderType body
      mkForallFVars #[fvar] exp (binderInfoForMVars := e.binderInfo)
    else
      let some (_, lhs, rhs) ← matchEq? body | throwError "not an equality {← ppExpr body}"
      mkEq (← mkComp fvar lhs) (← mkComp fvar rhs)

/-- A user attribute that applies to lemmas of the shape `∀ x, f (g x) = h x`.
It derives an auxiliary lemma of the form `f ∘ g = h` for reasoning about higher-order functions.
-/
def higherOrderGetParam (thm : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| higher_order $[$name]?) =>
    let ref := (name : Option Syntax).getD stx[0]
    let hothmName :=
      if let some sname := name then
        updatePrefix sname.getId thm.getPrefix
      else
        thm.appendAfter "\'"
    MetaM.run' <| TermElabM.run' <| do
      let lvl := (← getConstInfo thm).levelParams
      let typ ← instantiateMVars (← inferType <| .const thm (lvl.map mkLevelParam))
      let hot ← mkHigherOrderType typ
      let prf ← do
        let mvar ← mkFreshExprMVar hot
        let (_, mvarId) ← mvar.mvarId!.intros
        let [mvarId] ← mvarId.apply (← mkConst ``funext) | throwError "failed"
        let (_, mvarId) ← mvarId.intro1
        let lmvr ← mvarId.apply (← mkConst thm)
        lmvr.forM fun mv ↦ mv.assumption
        instantiateMVars mvar
      addDecl <| .thmDecl
        { name := hothmName
          levelParams := lvl
          type := hot
          value := prf }
      addDeclarationRangesFromSyntax hothmName (← getRef) ref
      _ ← addTermInfo (isBinder := true) ref <| ← mkConstWithLevelParams hothmName
      let hsm := simpExtension.getState (← getEnv) |>.lemmaNames.contains (.decl thm)
      if hsm then
        addSimpTheorem simpExtension hothmName true false .global 1000
      let some fcn ← getSimpExtension? `functor_norm | failure
      let hfm := fcn.getState (← getEnv) |>.lemmaNames.contains <| .decl thm
      if hfm then
        addSimpTheorem fcn hothmName true false .global 1000
      return hothmName
  | _ => throwUnsupportedSyntax

/-- The `higher_order` attribute. From a lemma of the shape `∀ x, f (g x) = h x` derive an
auxiliary lemma of the form `f ∘ g = h` for reasoning about higher-order functions.

Syntax: `[higher_order]` or `[higher_order name]` where the given name is used for the
generated theorem. -/
initialize higherOrderAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `higherOrder,
    descr :=
"From a lemma of the shape `∀ x, f (g x) = h x` derive an auxiliary lemma of the
form `f ∘ g = h` for reasoning about higher-order functions.

Syntax: `[higher_order]` or `[higher_order name]`, where the given name is used for the
generated theorem.",
    getParam := higherOrderGetParam }

end Tactic
