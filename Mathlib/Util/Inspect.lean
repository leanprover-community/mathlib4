/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Init
-- `import Lean.Elab.Command` would be enough

/-!
This file defines various `inspect`-like commands and tactics.
They all essentially represent a tree-like structure using indentation to represent direct
dependencies.

In particular, there are tailor-made functions to display
* `Syntax` trees,
* `Expr`ession trees,
* `InfoTree`s.

Note that, while printing a `Syntax` and an `Expr`ession tree can be reasonably faithful,
`InfoTree`s contain way too much information to actually print them "in full".
The commands defined here make some choices of what to print and what to hide.

### `Syntax`

There is a *command* `inspect_syntax` that can be applied to a command:
`inspect_syntax [command]` prints the command and elaborates it.

There is also a *tactic* `inspect_syntax` that can be applied to a tactic sequence:
it prints the sequence and evaluates it:
```lean
example : True ∧ True := by
  inspect_syntax
    refine ?_
    constructor
  · trivial
  · trivial
```
prints the tacticSeq `refine ?_; constructor` (technically, without the `;` in-between!) and
evaluates the tactic.

### `Expr`

These are only *tactics*. Within tactic-mode,
* `inspect` prints the first goal;
* `inspect h` prints the expression associated to the local variable `h`;
* the `inspect_lhs` and `inspect_rhs` variants assume that there are "meaningful" notions of
  left/right-hand sides and prints only those.

### `InfoTree`

This is only a *command*. `inspectIT [command]` elaborates the command and prints the resulting
`InfoTree`s.
-/
open Lean Elab Command Tactic

namespace InspectGeneric

/--
`treeR printNode recurse a` expects two function inputs and a term `a : α`.

The type `α` admits the functions
* `printNode : α → MessageData` representing some way of converting `a : α` as a
  message.
* `recurse : α → Array α` taking elements of `α` to elements that are "smaller".
  For instance, if `α` is an inductive type whose constructors involve `α` itself,
  the `recurse` function could take each `a : α` to the array of terms of `α` that
  `a` contains.

The function then combines the "tree" starting from `a` obtained by repeatedly
applying `recurse` and prints it all out in a tree-like diagram, using `printNode`
on each element of `α` that `recurse` visits.
-/
partial
def treeR {α} (printNode : α → MessageData) (recurse : α → Array α) (stx : α)
    (sep : MessageData := "\n") (indent : MessageData := "  ") :
    MessageData :=
  let (msg, es) := (printNode stx, recurse stx)
  let mes := es.map (treeR (sep := sep ++ indent) (indent := indent) printNode recurse)
  mes.foldl (fun x y => (x.compose sep).compose ((m!"|-").compose y)) msg

/-- The brackets corresponding to a given `BinderInfo`. Copied from `Mathlib.Lean.Expr.Basic`. -/
def bracks : BinderInfo → String × String
  | .implicit       => ("{", "}")
  | .strictImplicit => ("{{", "}}")
  | .instImplicit   => ("[", "]")
  | _               => ("(", ")")

/--
Replace the line breaks in the input string `s` with the unicode `⏎`
for better formatting of syntax that includes line breaks.
-/
def replaceLinebreaks (s : String) : String :=
  s.replace "\n" "⏎"

run_meta
  guard ("hi⏎⏎" == replaceLinebreaks "hi\n
")

/--
`showStx stx replaceLineBreaks flapLth` is a string representation of `stx` that shows at most
`flapLth` characters on either side of the string.

If `replaceLineBreaks` is `true`, then line breaks are replaced with `⏎` and the whole string
is enclosed in `'`.

If `flapLth` is `0`, then the entire string is shown.
-/
def showStx (stx : Syntax) (replaceLineBreaks : Bool := true) (flapLth : Nat := 10) : String :=
  let cand := stx.getSubstring?.getD default |>.toString.trim
  let cand := if replaceLineBreaks then replaceLinebreaks cand else cand
  let tick := if replaceLineBreaks then "'" else ""
  if flapLth != 0 && 2 * flapLth + 1 < cand.length then
    s!"{tick}{cand.take flapLth}…{cand.takeRight flapLth}{tick}"
  else
    s!"{tick}{cand}{tick}"

end InspectGeneric

namespace InspectSyntax

open InspectGeneric

/-- Print a `SourceInfo`. -/
def printSourceInfo : SourceInfo → MessageData
  | .original leading _pos trailing _endPos =>
    m!"{.ofConstName ``SourceInfo.original}: \
      ⟨{replaceLinebreaks leading.toString}⟩⟨{replaceLinebreaks trailing.toString}⟩"
  | .synthetic _pos _endPos canonical => m!"{.ofConstName ``SourceInfo.synthetic} {canonical}"
  | .none => m!"{.ofConstName ``SourceInfo.none}"

/-- Print a `Syntax.Preresolved`. -/
def preRes : Syntax.Preresolved → MessageData
  | .namespace ns => m!"{ns.eraseMacroScopes}"
  | .decl name fields => m!"{.ofConstName name.eraseMacroScopes}: {fields}"

/-- Convert a `Syntax` node to a `MessageData`. -/
def printNode : Syntax → MessageData
  | .node info kind .. =>
    m!"{.ofConstName ``Syntax.node} {.ofConstName kind}, {printSourceInfo info}"
  | .atom info val =>
    m!"{.ofConstName ``Syntax.atom} {printSourceInfo info}-- '{val}'"
  | .ident info rawVal val pr =>
    m!"{.ofConstName ``Syntax.ident} {printSourceInfo info}-- \
      ({rawVal},{val.eraseMacroScopes}) -- {pr.map preRes}"
  | .missing =>
    m!"{.ofConstName ``Syntax.missing}"

/--
`toMessageData stx` returns the default formatting of `Syntax` using `treeR stx`.
It prepends a printing of the input `Syntax` as well.
-/
def toMessageData (stx : Syntax) (indent : String := "|   ") (sep : String := "\n") : MessageData :=
  m!"inspect syntax:\n---\n{stx}\n---\n\n".compose <|
    treeR InspectSyntax.printNode Syntax.getArgs stx (indent := indent) (sep := sep)

/--
`inspect_syntax cmd` displays the tree structure of the `Syntax` of the command `cmd`.

The variant `inspect_syntax compact cmd` reduces the horizontal spacing of the output.
-/
elab (name := inspectSyntaxCmd) "inspect_syntax " cpct:("compact ")? cmd:command : command => do
  let msg := if cpct.isSome then toMessageData cmd "| " else toMessageData cmd
  logInfo msg
  elabCommand cmd

/--
`inspect_syntax tacs` displays the tree structure of the `Syntax` of the tactic sequence `tacs`.
-/
elab (name := inspectTacticCmd) "inspect_syntax " tacs:tacticSeq : tactic => do
  logInfo (toMessageData tacs)
  Tactic.evalTactic tacs

end InspectSyntax

namespace Lean.Expr

open InspectGeneric

/-- `recurse ex` returns the array of maximal sub-expressions of the input expression `ex`. -/
def recurse : Expr → Array Expr
  | ex@(.app ..)        => ex.getAppArgs
  | .lam _na t b _i     => #[t, b]
  | .forallE _na t b _i => #[t, b]
  | .letE _na t v b _i  => #[t, v, b]
  | .mdata _md e        => #[e]
  | .proj _na _id e     => #[e]
  | _ => #[]

/-- `printNode ctor? e` takes as input a `Bool`ean `ctor?` and an `Expr`ession `e` and returns
a `MessageData` that tries to represent faithfully all the data contained in the head of `e`.

If `ctor?` is `true`, then it also appends the name of the head constructor of `e`.
-/
def printNode (ctor? : Bool) (e : Expr) : MessageData :=
  let ctorN := if ctor? then m!" -- {e.ctorName}" else m!""
  (match e with
  | .bvar n                 => m!"'{n}'"
  | .fvar fv                => m!"'{fv.name}'"
  | .mvar mv                => m!"'{mv.name}'"
  | .sort u                 => m!"'{u}'"
  | .const na lv            => m!"'{na}' '{lv}'"
  | ex@(.app ..)            => m!"'{.ofConstName ex.getAppFn.constName}'"
  | .lam na _t _b i         => m!"{(bracks i).1}'{na}'{(bracks i).2}"
  | .forallE na _t _b i     => m!"{(bracks i).1}'{na}'{(bracks i).2}"
  | .letE na t v b i        => m!"'{na}' {t} {v} {b} {i}"
  | .lit (Literal.natVal n) => m!"'{n}'"
  | .lit (Literal.strVal n) => m!"'{n}'"
  | .mdata md e             => m!"'{md}' '{e}'"
  | .proj na id e           => m!"'{.ofConstName na}' {id} {e}") ++ ctorN

/-- `Lean.Expr.mle? p` takes `e : Expr` as input.
If `e` represents `a ≤ b`, then it returns `some (t, a, b)`, where `t` is the Type of `a`,
otherwise, it returns `none`. -/
@[inline] def mle? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LE.le
  pure (type, lhs, rhs)

/-- `Lean.Expr.mlt? p` takes `e : Expr` as input.
If `e` represents `a < b`, then it returns `some (t, a, b)`, where `t` is the Type of `a`,
otherwise, it returns `none`. -/
@[inline] def mlt? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LT.lt
  pure (type, lhs, rhs)

/-- `lhsrhs ex` returns the Type, lhs, rhs of `ex`, assuming that `ex` is of one of the forms
`a = b`, `a ≠ b`, `a ≤ b`, `a < b`. -/
def lhsrhs (ex : Expr) : Option (Expr × Expr × Expr) :=
  if let some x := ex.eq?  then x else
  if let some x := ex.ne?  then x else
  if let some x := ex.mle? then x else
  if let some x := ex.iff? then some (default, x) else
  if let some x := ex.and? then some (default, x) else
  if let .mdata _ e := ex  then lhsrhs e else
  ex.mlt?

end Lean.Expr

namespace InspectExpr

open Expr InspectGeneric

/--
`toMessageData ex` returns the default formatting of `Expr`ession using `treeR ex`.
It prepends a printing of the input `Expr`ession as well.
-/
partial
def toMessageData (ex : Expr)
    (ctor? : Bool := true) (sep : MessageData := "\n") (indent : MessageData := "|   ") :
    MessageData :=
  m!"inspect expr: '{ex}'\n\n" ++
    treeR (Expr.printNode ctor?) Expr.recurse ex (indent := indent) (sep := sep)

/-- A convenience function: simply logs the output of `InspectExpr.toMessageData` with the
default values adjusted to what the `inspect` command expects. -/
def inspectM {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (ex : Expr)
    (ctor? : Bool := true) (sep : MessageData := "\n") (indent : MessageData := "|   ") :
    m Unit :=
  logInfo <| toMessageData ex ctor? (indent := indent) (sep := sep)

/--
`inspect id?` displays the tree structure of the `Expr`ession in the goal.
If the optional identifier `id?` is passed, then `inspect` shows the tree-structure for the
`Expr`ession at the given identifier.

The variants `inspect_lhs` and `inspect_rhs` do what you imagine, when the goal is
`a = b`, `a ≠ b`, `a ≤ b`, `a < b`.
-/
elab (name := tacticInspect) "inspect" bang:(colGt ppSpace ident)? : tactic => withMainContext do
  let expr ← match bang with
    | none => getMainTarget
    | some id => do
      let loc ← Term.elabTerm id none
      let some decl := (← getLCtx).findFVar? loc | throwError m!"not found"
      pure decl.type
  inspectM expr

@[inherit_doc tacticInspect]
elab "inspect_lhs" : tactic => withMainContext do focus do
  let some (_, x, _) := lhsrhs (← getMainTarget) | throwError "Try 'inspect'"
  inspectM x

@[inherit_doc tacticInspect]
elab "inspect_rhs" : tactic => withMainContext do focus do
  let some (_, _, x) := lhsrhs (← getMainTarget) | throwError "Try 'inspect'"
  inspectM x

end InspectExpr

open InspectGeneric

namespace Lean.Elab

/-- Printing out a `CompletionInfo`. -/
def CompletionInfo.ctor : CompletionInfo → MessageData
  | .dot ti eType?      => m!"{.ofConstName ``dot} {.ofConstName ti.elaborator}, {ti.stx}, {eType?}"
  | .id name nm _ _ e?  => m!"{.ofConstName ``id} {name} '{nm.eraseMacroScopes}' {e?}"
  | .dotId _ nm _ e?    => m!"{.ofConstName ``dotId} '{.ofConstName nm}' {e?}"
  | .fieldId _ nm? _ sn => m!"{.ofConstName ``fieldId} '{nm?.map MessageData.ofConstName}' '{sn}'"
  | .namespaceId stx    => m!"{.ofConstName ``namespaceId} {showStx stx}"
  | .option stx         => m!"{.ofConstName ``option} {showStx stx}"
  | .errorName sn pid   => m!"{.ofConstName ``errorName} stx: '{sn}' pid '{pid}'"
  | .endSection stx _id? _ sn => m!"{.ofConstName ``endSection} {sn} '{showStx stx}'"
  | .tactic stx         => m!"{.ofConstName ``tactic} {showStx stx}"

/-- Printing out a `PartialContextInfo`. -/
def ContextInfo.toMessageData : (pci : ContextInfo) → MessageData
    | ci =>
      m!"{.ofConstName ``ContextInfo} {ci.parentDecl?.map MessageData.ofConstName}"

/-- Printing out a `Info`. -/
def Info.toMessageData : Info → MessageData
  | .ofTacticInfo ti         =>
    m!"{.ofConstName ``ofTacticInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}"
  | .ofTermInfo ti           =>
    m!"{.ofConstName ``ofTermInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}, {ti.expr}"
  | .ofPartialTermInfo ti    =>
    m!"{.ofConstName ``ofPartialTermInfo}: {.ofConstName ti.elaborator}, {showStx ti.stx}, \
                                                                                {ti.expectedType?}"
  | .ofCommandInfo ci        =>
    m!"{.ofConstName ``ofCommandInfo}: {.ofConstName ci.elaborator}, {showStx ci.stx}"
  | .ofMacroExpansionInfo me =>
    m!"{.ofConstName ``ofMacroExpansionInfo}: {showStx me.stx} --> {me.output}"
  | .ofOptionInfo oi         =>
    m!"{.ofConstName ``ofOptionInfo}: {.ofConstName oi.optionName}, {.ofConstName oi.declName}"
  | .ofFieldInfo fi          =>
    m!"{.ofConstName ``ofFieldInfo}: {fi.projName}, {fi.fieldName}"
  | .ofCompletionInfo ci     =>
    m!"{.ofConstName ``ofCompletionInfo}.{ci.ctor}"
  | .ofUserWidgetInfo _      =>
    m!"{.ofConstName ``UserWidgetInfo}"
  | .ofCustomInfo ci         =>
    m!"{.ofConstName ``ofCustomInfo}: {showStx ci.stx}"
  | .ofFVarAliasInfo fv      =>
    m!"{.ofConstName ``ofFVarAliasInfo}: {fv.userName}, {fv.id.name}, {fv.baseId.name}"
  | .ofFieldRedeclInfo _     =>
    m!"{.ofConstName ``FieldRedeclInfo}"
  | .ofDelabTermInfo _       =>
    m!"{.ofConstName ``DelabTermInfo}"
  | .ofChoiceInfo ci         =>
    m!"{.ofConstName ``ofChoiceInfo}: {.ofConstName ci.elaborator}, {showStx ci.stx}"
  | .ofDocElabInfo i =>
    m!"{.ofConstName ``ofDocElabInfo}: {.ofConstName i.elaborator}, {showStx i.stx}"
  | .ofDocInfo i =>
    m!"{.ofConstName ``ofDocInfo}: {.ofConstName i.elaborator}, {showStx i.stx}"
  | .ofErrorNameInfo i =>
    m!"{.ofConstName ``ofErrorNameInfo}: {i.errorName} {showStx i.stx}"

/-- Converts a fragment of a `Lean.Elab.PartialContextInfo` into a `MessageData`. -/
def PartialContextInfo.toMessageData : PartialContextInfo → MessageData
  | commandCtx _ci => m!"{.ofConstName ``commandCtx}"
  | parentDeclCtx parentDecl => m!"{.ofConstName ``parentDeclCtx} {.ofConstName parentDecl}"
  | autoImplicitCtx exs => m!"{.ofConstName ``autoImplicitCtx}: {exs}"

end Lean.Elab

namespace InspectInfoTree

/-- Convert an `InfoTree` node to a `MessageData`. -/
def printNode : InfoTree → MessageData
  | .context i _t => i.toMessageData
  | .node i _children => i.toMessageData
  | .hole mvarId => m!"hole {mvarId.name}"

/-- `recurse it` returns the array of maximal `InfoTree`s containes in the input `InfoTree` `it`. -/
def recurse : InfoTree → Array InfoTree
  | .context _i t => #[t]
  | .node _i children => children.toArray
  | .hole _mvarId => #[]

/--
`toMessageData it` is the default formatting of the output of `treeR it` that
uses `| ` to separate nodes.
-/
def inspectIT (it : InfoTree) (sep : MessageData := "\n") (indent : MessageData := "|   ") :
    MessageData :=
  treeR printNode recurse it (indent := indent) (sep := sep)

/-- `inspectIT cmd` displays the tree structure of the `InfoTree` when elaborating `cmd`.

The variant `inspectIT compact cmd` reduces the horizontal spacing of the output.
-/
elab "inspectIT " cpct:("compact ")? cmd:command : command => do
  let indent := if cpct.isSome then "| " else "|   "
  elabCommand cmd
  let mut msgs := #[m!"inspectIT:", m!"{showStx cmd false 0}"]
  for i in ← getInfoTrees do
    msgs := msgs.push <| inspectIT i (indent := indent)
  logInfo <| m!"\n---\n".joinSep msgs.toList

end InspectInfoTree
