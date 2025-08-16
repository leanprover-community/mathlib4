import Mathlib.Tactic.Linter.Indentation.Basic

open Lean Parser Elab Command Meta Linter

universe u v in
@[inline, expose]
def _root_.Subarray.findSomeRev? {α : Type u} {β : Type v}
    (as : Subarray α) (p : α → Option β) : Option β :=
  Id.run <| as.findSomeRevM? (pure <| p ·)

universe u v w in
@[inline]
def _root_.Subarray.findSomeM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : Subarray α) (f : α → m (Option β)) : m (Option β) := do
  for a in as do
    if let .some b := (← f a) then
      return some b
  pure none

universe w in
@[inline]
def _root_.Subarray.findM? {α : Type} {m : Type → Type w} [Monad m] (as : Subarray α)
    (p : α → m Bool) : m (Option α) :=
  as.findSomeM? fun a => return if (← p a) then some a else none

@[inline, expose]
def _root_.Subarray.find? {α : Type} (as : Subarray α) (p : α → Bool) :
    Option α :=
  Id.run <| as.findM? (pure <| p ·)


namespace Mathlib.Linter.Indentation

/-- docstring TODO.
https://leanprover-community.github.io/contribute/style.html#structuring-definitions-and-theorems -/
def declarationLinter : IndentationLinter := fun treeInfo limit ↦ do
  let next := Result.nextLinter limit
  let { stx := stx, childrenInfo? := .some childrenInfo, .. } := treeInfo | unreachable!
  let .some indent := treeInfo.getIndentation? | return next
  let _ ← ensureIndentationAtNode treeInfo limit true true
  let limit := { indentation := indent, isExactIndentation := true }
  let kind := stx.getKind
  match kind with
    | ``declaration | `«lemma» => pure ()
    | _ => unreachable!
  let #[modifiers@(_), decl] := childrenInfo.children | unreachable!
  let { childrenInfo? := .some declArgs, stx := .node _ name _, .. } := decl | unreachable!
  match name with
  | ``«abbrev» | ``definition | ``«theorem» | ``«opaque» | ``«axiom» | ``«example»
  | ``«instance» | `group => pure ()
  | ``«inductive» => return next -- TODO
  | ``«structure» => return next -- TODO
  | ``«classInductive» => return next -- TODO
  | _ => panic! s!"unknown declaration `{name}`, please send us feedback"
  -- check indentation of modifiers. `atMost` isn't set here since it will be applied in
  -- `declModifiers` instead.
  ensure modifiers limit
  /- `idxOfDeclHead` is the index of the head (such as `theorem` and `instance`) in
  `declArgs.children`. It is not 0 in instance declaration, where the first (index 0) node is a
  `Lean.Parser.Term.attrKind`. -/
  let .some idxOfDeclHead :=
    declArgs.children.findFinIdx? (if let .atom .. := ·.stx then true else false) | unreachable!
  /- the declaration value (`:= ...`, `| ...`, and `where ...`) -/
  let value : Option SyntaxTreeInfo :=
    declArgs.children[idxOfDeclHead:].findSomeRev? (fun child ↦
      match child.stx with
      | .node _ ``declValSimple _ | .node _ ``declValEqns _ | .node _ ``whereStructInst _
      | .node _ `null #[.node _ ``declValSimple _] => .some child
      | _ => .none)
  /- `idxOfValue` is the index of the declaration value (`:= ...`, `| ...`, and `where ...`)
  in `declArgs.children`. It can be `none` in axiom declaration -/
  let idxOfValue := value.map (·.parentInfo?.get!.idxInChildren)
  for child in declArgs.children[: idxOfDeclHead + 1] do
    ensure child limit
  for child in declArgs.children[idxOfDeclHead + 1 : idxOfValue.getD declArgs.children.size] do
      -- + 2 instead of + 4 to allow something ignoring `additionalIndentation` like:
      -- example : by
      --     exact True := by trivial
    ensure child { limit with indentation := indent + 2, additionalIndentation := 2 }
    -- text-based check, since some nodes aren't enforced by `additionalIndentation`
    let .some headTail := child.childrenInfo?.bind (·.headTail?) | continue
    for i in forInTokens (← getFlatten)[headTail.headToken.idx : headTail.tailToken.idx + 1] do
      let .some tokenIndent := i.info.getIndentation? | continue
      if tokenIndent < indent + 4 then
        throwIndentationError i.info
          m!"too few spaces, which should be at least {indent + 4}"
  if let .some idxOfValue := idxOfValue then
    -- check the declaration value (`:= ...`, `| ...`, and `where ...`)
    ensure declArgs.children[idxOfValue]!
      { limit with
        additionalIndentation := limit.oneAdditionalIndentation,
        atMost := .some (indent + limit.oneAdditionalIndentation) }
    -- `deriving instance` may exists in `definition`.
    for child in declArgs.children[idxOfValue + 1 : ] do
      ensure child { limit with atMost := .some (indent + limit.oneAdditionalIndentation) }
  return .finished

/-- docstring TODO. -/
partial def passToChildren
    (childrenLinter : IndentationLinter := runLinterOn) : IndentationLinter :=
  fun treeInfo limit ↦ do
    match treeInfo.children? with
    | .some children =>
      for child in children do
        ensure child limit childrenLinter
      return .finished
    | _ => return .nextLinter limit

def stringLinter : IndentationLinter :=
  fun treeInfo limit ↦ do
    let .some indent := treeInfo.getIndentation? | return .nextLinter limit
    if treeInfo.getSubstring?.get!.contains '\n' then
      if indent = 0 then return .finished
      ensureIndentationAt treeInfo limit (msgLtAtLeast := .some
        (m!"multi-line literal here should be \
          either at the beginning of a line without indentation or \
          indented by at least {·} spaces"))
      passToChildren (treeInfo := treeInfo) (limit := {})
    else
      return .nextLinter limit

def notAfterLineBreak : IndentationLinter := fun treeInfo limit ↦ do
  if treeInfo.getIndentation?.isSome then
    throwIndentationError treeInfo "should not be at the beginning of a line"
  return .nextLinter limit

/-- docstring TODO. -/
def setAdditionalIndentation (childrenLinter : IndentationLinter := runLinterOn)
    (additionalIndentation? : Option Nat := .none) (strict := false) :
    IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTail? := headTail, ..} =>
    let additionalIndentation := additionalIndentation?.getD limit.oneAdditionalIndentation
    let atMost : Option Nat :=
      match strict, treeInfo.getIndentation? with
      | true, .some indent => .some <| indent + additionalIndentation
      | _, _ => .none
    let (headLimit, limit) ← ensureIndentationAtNode treeInfo limit (updateIndentation? := true)
    let afterHead := headTail.elim children.size (·.getHeadIdxInChildren + 1)
    for child in children[:afterHead] do
      ensure (linter := childrenLinter) child headLimit
    for child in children[afterHead:children.size] do
      ensure (linter := childrenLinter) child
        { limit with additionalIndentation := additionalIndentation, atMost := atMost }
    return .finished
  | _ => return .nextLinter limit

partial def setStrictAdditionalIndentation (childrenLinter : IndentationLinter := runLinterOn)
    (additionalIndentation? : Option Nat := .none) :
    IndentationLinter :=
  setAdditionalIndentation childrenLinter additionalIndentation? true

def alignToHead (childrenLinter : IndentationLinter := runLinterOn) :
    IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTail? := headTail, ..} =>
    let (headLimit, limit) ← ensureIndentationAtNode treeInfo limit (updateIndentation? := true)
    let limit := treeInfo.getIndentation?.elim limit fun i ↦
      { indentation := i, isExactIndentation := true, atMost := i}
    let afterHead := headTail.elim children.size (·.getHeadIdxInChildren + 1)
    for child in children[:afterHead] do
      ensure (linter := childrenLinter) child headLimit
    for child in children[afterHead:children.size] do
      ensure (linter := childrenLinter) child limit
    return .finished
  | _ => return .nextLinter limit

def byLinter : IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.prevTokenIdx?.map ((← getFlatten)[·]!)  with
  | .some (FlattenSyntaxTreeInfoElement.leaf { stx := .atom (val := ":=") .., .. }) =>
    (notAfterLineBreak >> passToChildren runLinterOn) treeInfo limit
  | _ => setStrictAdditionalIndentation (treeInfo := treeInfo) (limit := limit)

/-- docstring TODO. -/
def termAppLinter : IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTail? := headTail?..} =>
    let (headLimit, limit) ← ensureIndentationAtNode treeInfo limit (updateIndentation? := true)
    let afterHead := headTail?.elim children.size (·.getHeadIdxInChildren + 1) -- should be 1
    assert! afterHead == 1
    assert! children.size == 2
    assert! children[1]!.stx.isOfKind `null
    ensure children[0]! headLimit
    for child in children[1]!.children?.get! do
      ensure child { limit with additionalIndentation := limit.oneAdditionalIndentation }
    return .finished
  | _ => return .nextLinter limit

def ignoringAdditionalIndentationLinter : IndentationLinter :=
  fun _ => ( pure <| .nextLinter { · with additionalIndentation := 0 } )

/-- docstring TODO
-/
def nodeLinters : NameMap IndentationLinter :=
    .ofList [
    (``declModifiers, alignToHead),
    (``declaration, declarationLinter), (`«lemma», declarationLinter),
    (`str, stringLinter), (``termS!_, stringLinter), (``termM!_, stringLinter),
    (``Std.termF!_, stringLinter), (interpolatedStrKind, stringLinter),
    (``Term.typeSpec, notAfterLineBreak),
    (``Term.byTactic, byLinter), (``Term.byTactic', byLinter),
    (``Tactic.tacticSeq, alignToHead),
    (``Tactic.tacticSeq1Indented, alignToHead),
    (``Term.app, termAppLinter),
    (``whereStructInst, ignoringAdditionalIndentationLinter >> setStrictAdditionalIndentation),
    -- (``Term.structInstField, strictAdditionalIndentationLinter),
    (``Term.whereDecls, ignoringAdditionalIndentationLinter),
    (``Termination.partialFixpoint, setStrictAdditionalIndentation),
    (``Termination.terminationBy, setStrictAdditionalIndentation),
    (``Termination.coinductiveFixpoint, setStrictAdditionalIndentation),
    (``Termination.inductiveFixpoint, setStrictAdditionalIndentation),
    (``Termination.suffix, ignoringAdditionalIndentationLinter),
    (``ctor, ignoringAdditionalIndentationLinter),
    (``Term.matchAlts, passToChildren),
    (``Term.matchAlt, ignoringAdditionalIndentationLinter),
    (``declValSimple, notAfterLineBreak >> passToChildren)
  ]

def atomLinters : Std.HashMap String IndentationLinter :=
  .ofList [
    (":=", notAfterLineBreak),
    ("where", ignoringAdditionalIndentationLinter)
  ]

/--
from https://github.com/leanprover/vscode-lean4/blob/v0.0.209/vscode-lean4/language-configuration.json
-/
def brackets : Std.HashMap String (String × Nat) := .ofList [
  ("(", ")", 2), ("`(", ")", 2), ("``(", ")", 2), ("[", "]", 2), ("#[", "]", 2), ("@[", "]", 2),
  ("%[", "]", 2), ("{", "}", 2), ("⁅", "⁆", 2), ("⁽", "⁾", 2), ("₍", "₎", 2), ("〈", "〉", 2),
  ("⟮", "⟯", 2), ("⎴", "⎵", 2), ("⟅", "⟆", 2), ("⟦", "⟧", 2), ("⟨", "⟩", 1), ("⟪", "⟫", 2),
  ("⦃", "⦄", 2), ("〈", "〉", 2), ("《", "》", 2), ("‹", "›", 2), ("«", "»", 2), ("「", "」", 2),
  ("『", "』", 2), ("【", "】", 2), ("〔", "〕", 2), ("〖", "〗", 2), ("〚", "〛", 2),
  ("︵", "︶", 2), ("︷", "︸", 2), ("︹", "︺", 2), ("︻", "︼", 2), ("︽", "︾", 2),
  ("︿", "﹀", 2), ("﹁", "﹂", 2), ("﹃", "﹄", 2), ("﹙", "﹚", 2), ("﹛", "﹜", 2),
  ("﹝", "﹞", 2), ("（", "）", 2), ("［", "］", 2), ("｛", "｝", 2), ("｢", "｣", 2)]

def bracketPairLinter (allowRightBracketDeeper := false) :
    IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTail? := .some headTail, ..} =>
    let head := headTail.head
    let headStr := head.getSubstring?.get!.toString
    let tail := headTail.tail
    let tailStr := tail.getSubstring?.get!.toString
    let .some ⟨pairTailStr, indentInside⟩ := brackets.get? headStr | return .nextLinter limit
    let isPairOfBrackets := head.idx != tail.idx && pairTailStr = tailStr
    if !isPairOfBrackets then return .nextLinter limit
    let (headLimit, childrenLimit) ←
      ensureIndentationAtNode treeInfo limit (updateIndentation? := true)
    let headIdx' := headTail.getHeadIdxInChildren
    let tailIdx' := headTail.getTailIdxInChildren
    let .some contentHead := children[headIdx' + 1 : tailIdx'].find? (·.getPos?.isSome) |
      if treeInfo.getSubstring?.get!.contains '\n' then
        throwIndentationError treeInfo
          m!"`{head.getSubstring?.get!}` and `{tail.getSubstring?.get!}` without content \
            bracketed should not be splitted into two lines."
          .none
      return .nextLinter limit
    let newOneAdditionalIndent := min indentInside limit.oneAdditionalIndentation
    let headLimit := { headLimit with oneAdditionalIndentation := newOneAdditionalIndent }
    let childrenLimit := { childrenLimit with oneAdditionalIndentation := newOneAdditionalIndent }
    let headIsEndOfLine :=
      Substring.contains ⟨(← getSrc), head.getPos?.get!, contentHead.getPos?.get!⟩ '\n'
    let addition := if headIsEndOfLine then newOneAdditionalIndent else 0
    for child in children[: headIdx' + 1] do
      ensure child headLimit
    for child in children[headIdx' + 1 : tailIdx'] do
      ensure child { childrenLimit with additionalIndentation := addition }
    let tailAtMost : Option Nat ←
      if allowRightBracketDeeper then
        pure .none
      else
        pure <| head.getIndentation? <|>
        (← forIn (forInTokens (← getFlatten)[contentHead.idx : tail.idx]) (none : Option Nat)
          (return ForInStep.yield <| Option.merge min ·.info.getIndentation? ·))
    trace[Indentation] repr (contentHead.idx, tail.idx, tailAtMost)
    for child in children[tailIdx' : ] do
      ensure child { childrenLimit with additionalIndentation := 0, atMost := tailAtMost }
    return .finished
  | _ => return .nextLinter limit

initialize addIndentationLinters {
  nodeLinters := nodeLinters,
  atomLinters := atomLinters,
  linters := #[(2, bracketPairLinter)]
}

end Mathlib.Linter.Indentation
