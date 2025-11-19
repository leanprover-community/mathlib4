import Mathlib.Tactic.Linter.Indentation.Defs

open Lean Parser Elab Command Meta Linter

namespace Mathlib.Linter.Indentation

/-- docstring TODO -/
def ensureIndentationAt (treeInfo : SyntaxTreeInfo) (limit : Limit)
    (checkAddition? : Option Bool := true)
    (msgLtAtLeast : Option (Nat → MessageData) :=
      .some (m!"too few spaces, which should be at least {·}"))
    (msgGtAtMost : Option (Nat → MessageData) :=
      .some (m!"too many spaces, which should be at most {·}")) :
    LinterM Unit := do
  let .some indent := treeInfo.getIndentation? | return
  let checkAddition :=
    if let .some c := checkAddition? then c
    else treeInfo.stx.isAtom || treeInfo.stx.isIdent || (← categoriesContain treeInfo.stx)
  let atLeast := limit.indentation + if checkAddition then limit.additionalIndentation else 0
  if indent < atLeast then
    if let .some msg := msgLtAtLeast then
      throwIndentationError treeInfo (msg atLeast)
  else if let .some atMost := limit.atMost then
    if indent > atMost then
      if let .some msg := msgGtAtMost then
        throwIndentationError treeInfo (msg atMost)

def Limit.forChildren (treeInfo : SyntaxTreeInfo) (limit : Limit) (updateIndentation : Bool) :
    CommandElabM Limit := do
  let limit := { limit with atMost := .none }
  if !updateIndentation then return limit
  if let .some indent := treeInfo.getIndentation? then
    pure { limit with indentation := indent, additionalIndentation := 0, isExactIndentation := true}
  else
    pure { limit with isExactIndentation := false }

def Limit.forHead (treeInfo : SyntaxTreeInfo) (limit : Limit) (updateIndentation : Bool) :
    CommandElabM Limit := do
  if updateIndentation then
    if let .some indent := treeInfo.getIndentation? then
      return { limit with
        indentation := indent,
        additionalIndentation := limit.indentation + limit.additionalIndentation - indent,
        isExactIndentation := true
      }
  return limit

/-- docstring TODO -/
def ensureIndentationAtNode (treeInfo : SyntaxTreeInfo) (limit : Limit)
    (checkAddition? : Option Bool := .none) (updateIndentation? : Option Bool := .none)
    (msgLtAtLeast : Option (Nat → MessageData) :=
      .some (m!"too few spaces, which should be at least {·}"))
    (msgGtAtMost : Option (Nat → MessageData) :=
      .some (m!"too many spaces, which should be at most {·}")) :
  LinterM (Limit × Limit) := do
  ensureIndentationAt treeInfo limit checkAddition? msgLtAtLeast msgGtAtMost
  let updateIndentation ← match updateIndentation? with
    | .some updateIndentation => pure updateIndentation
    | _ => treeInfo.needUpdatingIndentation
  let childrenLimit ← limit.forChildren treeInfo updateIndentation
  let headLimit ← limit.forHead treeInfo updateIndentation
  pure (headLimit, childrenLimit)

def defaultLinter : IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTail? := headTail, ..} =>
    let (headLimit, childrenLimit) ← ensureIndentationAtNode treeInfo limit
    let afterHead := headTail.elim children.size (·.getHeadIdxInChildren + 1)
    for child in children[:afterHead] do
      ensure child headLimit
    for child in children[afterHead:] do
      ensure child childrenLimit
    pure .finished
  | _ =>
    ensureIndentationAt treeInfo limit
    pure .finished

initialize addIndentationLinters { linters := #[(1, defaultLinter)] }

end Mathlib.Linter.Indentation
