import Mathlib.Tactic.Linter.Indentation.Defs

open Lean Parser Elab Command Meta Linter

namespace Mathlib.Linter.Indentation

/-- docstring TODO -/
def ensureIndentationAt (treeInfo : SyntaxTreeInfo) (limit : Limitation)
    (checkAddition? : Option Bool := true)
    (msgLtAtLeast : Option (Nat → MessageData) :=
      .some (m!"too few spaces, which should be at least {·}"))
    (msgGtAtMost : Option (Nat → MessageData) :=
      .some (m!"too many spaces, which should be at most {·}")) :
    LinterM Unit := do
  let .some pos := treeInfo.getPos? | return
  let .some spaces := indentationOfPos limit.src pos | return
  let checkAddition :=
    if let .some c := checkAddition? then c
    else treeInfo.stx.isAtom || treeInfo.stx.isIdent || (← isInCategories treeInfo.stx)
  let atLeast := limit.indentation + if checkAddition then limit.additionalIndentation else 0
  if spaces < atLeast then
    if let .some msg := msgLtAtLeast then
      throwIndentationError treeInfo.stx (msg atLeast) limit
  else if let .some atMost := limit.atMost then
    if spaces > atMost then
      if let .some msg := msgGtAtMost then
        throwIndentationError treeInfo.stx (msg atMost) limit

def limitForChildren (treeInfo : SyntaxTreeInfo) (limit : Limitation) (updateIndentation : Bool) :
    CommandElabM Limitation := do
  let limit := { limit with atMost := .none }
  if !updateIndentation then return limit
  if let .some indent := treeInfo.getIndentation? limit.src then
    pure { limit with indentation := indent, additionalIndentation := 0, isExactIndentation := true}
  else
    pure { limit with isExactIndentation := false }

def limitForHead (treeInfo : SyntaxTreeInfo) (limit : Limitation) (updateIndentation : Bool) :
    CommandElabM Limitation := do
  if updateIndentation then
    if let .some indent := treeInfo.getIndentation? limit.src then
      return { limit with
        indentation := indent,
        additionalIndentation := limit.indentation + limit.additionalIndentation - indent,
        isExactIndentation := true
      }
  return limit

/-- docstring TODO -/
def ensureIndentationAtNode (treeInfo : SyntaxTreeInfo) (limit : Limitation)
    (checkAddition? : Option Bool := .none) (updateIndentation? : Option Bool := .none)
    (msgLtAtLeast : Option (Nat → MessageData) :=
      .some (m!"too few spaces, which should be at least {·}"))
    (msgGtAtMost : Option (Nat → MessageData) :=
      .some (m!"too many spaces, which should be at most {·}")) :
  LinterM (Limitation × Limitation) := do
  ensureIndentationAt treeInfo limit checkAddition? msgLtAtLeast msgGtAtMost
  let updateIndentation ← match updateIndentation? with
    | .some updateIndentation => pure updateIndentation
    | _ => treeInfo.needUpdatingIndentation
  let childrenLimit ← limitForChildren treeInfo limit updateIndentation
  let headLimit ← limitForHead treeInfo limit updateIndentation
  pure (headLimit, childrenLimit)

def defaultLinter : IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTailIdxInChildren := headTailIdxInChildren, ..} =>
    let (headLimit, childrenLimit) ← ensureIndentationAtNode treeInfo limit
    let afterHead := headTailIdxInChildren.map (·.fst + 1) |>.getD children.size
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
