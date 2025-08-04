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

/-- docstring TODO.
https://leanprover-community.github.io/contribute/style.html#structuring-definitions-and-theorems -/
def declarationLinter : IndentationLinter := fun treeInfo limit ↦ do
  let next := Result.nextLinter limit
  let { stx := stx, childrenInfo? := .some childrenInfo, .. } := treeInfo | unreachable!
  let .some indent := treeInfo.getIndentation? limit.src | return next
  let (_, limit) ← ensureIndentationAtNode treeInfo limit true true
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
  -- check indentation of modifiers
  ensure modifiers { limit with atMost := indent }
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
      -- + 2 instead of + 4 to allow something like:
      -- example : by
      --     exact True := by trivial
    ensure child { limit with indentation := indent + 2, additionalIndentation := 2 }
    -- text-based check, since some nodes aren't enforced by `additionalIndentation`
    let .some (first, last) := child.childrenInfo?.map (·.headTailIdxInChildren) |>.getD none |
      continue
    for i in limit.flatten[child.idx + first : child.idx + last + 1] do
      let .leaf i := i | continue
      let .some tokenIndent := i.getIndentation? limit.src | continue
      if tokenIndent < tokenIndent + 4 then
        throwIndentationError stx
          m!"too few spaces, which should be at least {tokenIndent + 4}" limit
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

def stringLinter : IndentationLinter :=
  fun treeInfo limit ↦ do
    let .some indent := treeInfo.getIndentation? limit.src | return .nextLinter limit
    if treeInfo.getSubstring? limit.src |>.get!.contains '\n' then
      if indent = 0 then return .finished
      ensureIndentationAt treeInfo limit (msgLtAtLeast := .some
        (m!"multi-line literal here should be \
          either at the beginning of a line without indentation or \
          indented by at least {·} spaces"))
      return .finished
    else
      return .nextLinter limit

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

def notAfterLineBreakLinter : IndentationLinter := fun treeInfo limit ↦ do
  if (treeInfo.getIndentation? limit.src).isSome then
    throwIndentationError treeInfo.stx "should not be at the beginning of a line" limit
  return .nextLinter limit

/-- docstring TODO. -/
def deeperIndentationLinter (childrenLinter : IndentationLinter := runLinterOn)
    (additionalIndentation? : Option Nat := .none) (strict := false) :
    IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTailIdxInChildren := headTailIdxInChildren, ..} =>
    let additionalIndentation := additionalIndentation?.getD limit.additionalIndentation
    let atMost : Option Nat :=
      match strict, treeInfo.getIndentation? limit.src with
      | true, .some indent => .some <| indent + additionalIndentation
      | _, _ => .none
    let (headLimit, limit) ← ensureIndentationAtNode treeInfo limit (updateIndentation? := true)
    let afterHead := headTailIdxInChildren.map (·.fst + 1) |>.getD children.size
    for child in children[:afterHead] do
      ensure (linter := childrenLinter) child headLimit
    for child in children[afterHead:children.size] do
      ensure (linter := childrenLinter) child
        { limit with
          additionalIndentation := limit.oneAdditionalIndentation, atMost := atMost }
    return .finished
  | _ => return .nextLinter limit

partial def strictDeeperIndentationLinter (childrenLinter : IndentationLinter := runLinterOn)
    (additionalIndentation? : Option Nat := .none) :
    IndentationLinter := deeperIndentationLinter childrenLinter additionalIndentation? true


def byLinter : IndentationLinter := fun treeInfo limit ↦ do
  let lastToken? := limit.flatten[0:treeInfo.idx].findRev?
    (match · with | .leaf { stx := stx, ..} => stx.isAtom || stx.isIdent | _ => false)
  match lastToken? with
  | .some (.leaf { stx := .atom (val := ":=") .., .. }) =>
    (notAfterLineBreakLinter >> passToChildren runLinterOn) treeInfo limit
  | _ => strictDeeperIndentationLinter (treeInfo := treeInfo) (limit := limit)

/-- docstring TODO. -/
def termAppLinter : IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTailIdxInChildren := headTailIdxInChildren, ..} =>
    let (headLimit, limit) ← ensureIndentationAtNode treeInfo limit (updateIndentation? := true)
    let afterHead := headTailIdxInChildren.map (·.fst + 1) |>.getD children.size -- should be 1
    for child in children[:afterHead] do
      ensure child headLimit
    for child in children[afterHead:children.size - 1] do
      ensure child { limit with additionalIndentation := limit.oneAdditionalIndentation }
    if children[children.size - 1]!.stx.getKind == ``Term.namedArgument then
      ensure children[children.size - 1]!
        { limit with additionalIndentation := limit.oneAdditionalIndentation }
    else
      -- don't force the last unnamed argument to have a deeper indentation -- it can be same
      -- with its parent's.
      ensure children[children.size - 1]! limit
    return .finished
  | _ => return .nextLinter limit

def ignoringAdditionalIndentationLinter : IndentationLinter :=
  fun _ => ( pure <| .nextLinter { · with additionalIndentation := 0 } )


/-- docstring TODO
-/
def nodeLinters : NameMap IndentationLinter :=
    .ofList [
    (``declModifiers, passToChildren),
    (``declaration, declarationLinter), (`«lemma», declarationLinter),
    (`str, stringLinter), (``termS!_, stringLinter), (``termM!_, stringLinter),
    (``Std.termF!_, stringLinter), (interpolatedStrKind, stringLinter),
    (``Term.typeSpec, notAfterLineBreakLinter),
    (``Term.byTactic, byLinter), (``Term.byTactic', byLinter),
    (``Tactic.tacticSeq, passToChildren),
    (``Term.app, termAppLinter),
    (``whereStructInst, ignoringAdditionalIndentationLinter >> strictDeeperIndentationLinter),
    (``Term.structInstField, strictDeeperIndentationLinter),
    (``Term.whereDecls, ignoringAdditionalIndentationLinter),
    (``Termination.partialFixpoint, strictDeeperIndentationLinter),
    (``Termination.terminationBy, strictDeeperIndentationLinter),
    (``Termination.coinductiveFixpoint, strictDeeperIndentationLinter),
    (``Termination.inductiveFixpoint, strictDeeperIndentationLinter),
    (``Termination.suffix, ignoringAdditionalIndentationLinter),
    (``ctor, ignoringAdditionalIndentationLinter),
    (``Term.matchAlts, passToChildren),
    (``Term.matchAlt, ignoringAdditionalIndentationLinter),
    (``declValSimple, notAfterLineBreakLinter >> passToChildren)
  ]

def atomLinters : Std.HashMap String IndentationLinter :=
  .ofList [
    (":=", notAfterLineBreakLinter),
    ("where", ignoringAdditionalIndentationLinter)
  ]

def bracketPairLinter : IndentationLinter := fun treeInfo limit ↦ do
  match treeInfo.childrenInfo? with
  | .some { children := children, headTailIdxInChildren := .some (headIdx, tailIdx), ..} =>
    let head := children[headIdx]!
    let headStr := head.getSubstring? limit.src |>.get!.toString
    let tail := children[tailIdx]!
    let tailStr := tail.getSubstring? limit.src |>.get!.toString
    let .some ⟨pairTailStr, indentInside⟩ := brackets.get? headStr | return .nextLinter limit
    let isPairOfBrackets := headIdx != tailIdx && pairTailStr = tailStr
    if !isPairOfBrackets then return .nextLinter limit
    let (headLimit, childrenLimit) ←
      ensureIndentationAtNode treeInfo limit (updateIndentation? := true)
    let .some contentHead := children[headIdx+1:tailIdx].find? (·.getPos?.isSome) |
      if (treeInfo.getSubstring? limit.src).get!.contains '\n' then
        throwIndentationError treeInfo.stx
          m!"`{(head.getSubstring? limit.src).get!}` and \
            `{(tail.getSubstring? limit.src).get!}` without content \
            should not be splitted into two lines."
          limit .none
      return .nextLinter limit
    let newOneAdditionalIndent := min indentInside limit.oneAdditionalIndentation
    let headLimit := { headLimit with oneAdditionalIndentation := newOneAdditionalIndent }
    let childrenLimit := { childrenLimit with oneAdditionalIndentation := newOneAdditionalIndent }
    let headIsEndOfLine :=
      Substring.contains ⟨limit.src, head.getPos?.get!, contentHead.getPos?.get!⟩ '\n'
    let addition := if headIsEndOfLine then newOneAdditionalIndent else 0
    for child in children[: headIdx + 1] do
      ensure child headLimit
    for child in children[headIdx + 1 : tailIdx] do
      ensure child { childrenLimit with additionalIndentation := addition }
    let tailAtMost : Option Nat :=
      if let .some indent := head.getIndentation? limit.src then
        .some indent
      else
        -- the minimum indentation in content
        children[contentHead.parentInfo?.get!.idxInChildren : tailIdx].foldl
          (fun m ↦ (·.getIndentation? limit.src |>.map fun i ↦ min i <| m.getD i))
          .none
    let tailAdditionalIndentation :=
      if head.getIndentation? limit.src |>.isSome then limit.additionalIndentation
      else 0
    for child in children[tailIdx : ] do
      ensure child
        { childrenLimit with
          additionalIndentation := tailAdditionalIndentation, atMost := tailAtMost }
    return .finished
  | _ => return .nextLinter limit

initialize addIndentationLinters {
  nodeLinters := nodeLinters,
  atomLinters := atomLinters,
  linters := #[(1, bracketPairLinter)]
}

end Mathlib.Linter.Indentation
