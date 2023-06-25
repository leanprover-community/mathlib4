/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Edward Ayers, Mario Carneiro
-/
import Lean
import Mathlib.Data.Array.Defs

namespace Mathlib.Tactic
open Lean Elab.Tactic Meta Parser Term Syntax.MonadTraverser

section deleteme -- once lean4#2262 is merged

def hygieneInfoFn : ParserFn := fun c s =>
  let input := c.input
  let finish pos str trailing s :=
    let info  := SourceInfo.original str pos trailing pos
    let ident := mkIdent info str .anonymous
    let stx   := mkNode hygieneInfoKind #[ident]
    s.pushSyntax stx
  let els s :=
    let str := mkEmptySubstringAt input s.pos
    finish s.pos str str s
  if s.stxStack.isEmpty then els s else
    let prev := s.stxStack.back
    if let .original leading pos trailing endPos := prev.getTailInfo then
      let str := mkEmptySubstringAt input endPos
      let s := s.popSyntax.pushSyntax <| prev.setTailInfo (.original leading pos str endPos)
      finish endPos str trailing s
    else els s

def hygieneInfoNoAntiquot : Parser := {
  fn   := hygieneInfoFn
  info := nodeInfo hygieneInfoKind epsilonInfo
}

@[combinator_formatter hygieneInfoNoAntiquot]
def hygieneInfoNoAntiquot.formatter : PrettyPrinter.Formatter := goLeft
@[combinator_parenthesizer hygieneInfoNoAntiquot]
def hygieneInfoNoAntiquot.parenthesizer : PrettyPrinter.Parenthesizer := goLeft
@[run_parser_attribute_hooks] def hygieneInfo : Parser :=
  withAntiquot (mkAntiquot "hygieneInfo" hygieneInfoKind (anonymous := false)) hygieneInfoNoAntiquot

end deleteme

def optBinderIdent : Parser := leading_parser
  -- Note: the withResetCache is because leading_parser seems to add a cache boundary,
  -- which causes the `hygieneInfo` parser not to be able to undo the trailing whitespace
  (ppSpace >> Term.binderIdent) <|> withResetCache hygieneInfo

def optBinderIdent.name (id : TSyntax ``optBinderIdent) : Name :=
  if id.raw[0].isIdent then id.raw[0].getId else HygieneInfo.mkIdent ⟨id.raw[0]⟩ `this |>.getId

/--
Uses `checkColGt` to prevent

```lean
have h
exact Nat
```

From being interpreted as
```lean
have h
  exact Nat
```
-/
def haveIdLhs' : Parser :=
  optBinderIdent >> many (ppSpace >>
    checkColGt "expected to be indented" >> letIdBinder) >> optType

syntax "have" haveIdLhs' : tactic
syntax "let " haveIdLhs' : tactic
syntax "suffices" haveIdLhs' : tactic

open Elab Term in
def haveLetCore (goal : MVarId) (name : TSyntax ``optBinderIdent)
  (bis : Array (TSyntax ``letIdBinder))
  (t : Option Term) (keepTerm : Bool) : TermElabM (MVarId × MVarId) :=
  let declFn := if keepTerm then MVarId.define else MVarId.assert
  goal.withContext do
    let n := optBinderIdent.name name
    let elabBinders k := if bis.isEmpty then k #[] else elabBinders bis k
    let (goal1, t, p) ← elabBinders fun es ↦ do
      let t ← match t with
      | none => mkFreshTypeMVar
      | some stx => withRef stx do
          let e ← Term.elabTerm stx none
          Term.synthesizeSyntheticMVars false
          instantiateMVars e
      let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
      pure (p.mvarId!, ← mkForallFVars es t, ← mkLambdaFVars es p)
    let (fvar, goal2) ← (← declFn goal n t p).intro1P
    goal2.withContext do
      Term.addTermInfo' (isBinder := true) name.raw[0] (mkFVar fvar)
    pure (goal1, goal2)

elab_rules : tactic
| `(tactic| have $n:optBinderIdent $bs* $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false
  replaceMainGoal [goal1, goal2]

elab_rules : tactic
| `(tactic| suffices $n:optBinderIdent $bs* $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false
  replaceMainGoal [goal2, goal1]

elab_rules : tactic
| `(tactic| let $n:optBinderIdent $bs* $[: $t:term]?) => withMainContext do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t true
  replaceMainGoal [goal1, goal2]
