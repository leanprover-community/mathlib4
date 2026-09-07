/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import ProofWidgets.Component.MakeEditLink
public import ProofWidgets.Component.RefreshComponent
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Tactic.DepRewrite
public import Batteries.Tactic.PermuteGoals
public meta import Mathlib.Data.String.Defs
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-!
# Various utilities used in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx Server

section

open Widget PrettyPrinter.Delaborator

/-- Turn an `Expr` into an HTML with hover info. -/
def exprToHtml (e : Expr) : MetaM Html :=
  return <InteractiveCode fmt={← Widget.ppExprTagged e}/>

/-- Turn a constant into an HTML with hover info.
This avoids the `@` that may appear when using `exprToHtml`. -/
def constToHtml (n : Name) : MetaM Html := do
  let delab := withOptionAtCurrPos `pp.tagAppFns true <| delabConst
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos (delab := delab) (← mkConstWithLevelParams n)
  let tt := TaggedText.prettyTagged fmt
  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt}/>

/-- Display `fmt` with a docstring as if it is the constant `n`. -/
def formatToHtmlWithDoc (fmt : Format) (n : Name) : MetaM Html := do
  let tag := 0
  -- Hack: use `.ofCommandInfo` instead of `.ofTacticInfo` to avoid printing `n` and its type.
  -- Unfortunately, there is still a loose dangling ` : `.
  let infos := .insert ∅ tag <| .ofCommandInfo
    { elaborator := `ClickSuggestions, stx := .node .none n #[] }
  let tt := TaggedText.prettyTagged <| .tag tag fmt
  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  -- TODO: I would love to print this using the same keyword colour used by the editor,
  -- but I don't think this is possible. Additionally, `InteractiveCode` already overwrites the
  -- colour and style of the text (namely the expression style)
  return <InteractiveCode fmt={← tagCodeInfos ctx infos tt} />


/-- Pretty print a tactic with its docstring as hover info.

I would love to print `tac` with another colour, e.g. the keyword highlighting used by the editor,
but I have no idea how to do this.
-/
def tacticToHtml (tac : TSyntax `tactic) : MetaM Html := do
  formatToHtmlWithDoc (← PrettyPrinter.ppTactic tac) tac.1.getKind

end

/-- Let `#click_suggestions` show the candidate lemmas that failed to apply. -/
register_option click_suggestions.debug : Bool := {
  defValue := false
  descr := "let `#click_suggestions` show the candidate lemmas that failed to apply"
}

/-- A global constant or a free variable. Library search can return either. -/
inductive Premise where
  /-- A global constant. -/
  | const (declName : Name)
  /-- A free variable. -/
  | fvar (fvarId : FVarId)
  deriving Inhabited

namespace Premise

/-- Print a premise as a string. -/
def toString : Premise → String
  | .const name | .fvar ⟨name⟩ => name.toString

/-- The name length of a premise. -/
def length (premise : Premise) : Nat :=
  premise.toString.length

/-- Get the type of a premise. -/
def getType : Premise → MetaM Expr
  | .const name => (·.type) <$> getConstInfo name
  | .fvar fvarId => fvarId.getType

/-- Fill the premise in with fresh universe and expression metavariables. -/
def forallMetaTelescopeReducing : Premise → MetaM (Expr × Array Expr × Array BinderInfo × Expr)
  | .const name => do
    let thm ← mkConstWithFreshMVarLevels name
    let result ← Meta.forallMetaTelescopeReducing (← inferType thm)
    return (mkAppN thm result.1, result)
  | .fvar fvarId => do
    let decl ← fvarId.getDecl
    let result ← Meta.forallMetaTelescopeReducing (← instantiateMVars decl.type)
    return (mkAppN decl.toExpr result.1, result)

/-- Return the user-facing name of the premise, relative to the current namespace. -/
def unresolveName : Premise → MetaM Name
  | .const name => do
    unresolveNameGlobalAvoidingLocals name (fullNames := getPPFullNames (← getOptions))
  | .fvar fvarId => fvarId.getUserName

/-- Print a premise using message data. -/
def toMessageData : Premise → MessageData
  | .const name => .ofConstName name
  | .fvar fvarId => .ofExpr (.fvar fvarId)

/-- Print a premise using HTML. -/
def toHtml : Premise → MetaM Html
  | .const name => constToHtml name
  | .fvar fvarId => exprToHtml (.fvar fvarId)

end Premise

/-- The global state that is shared between all threads. -/
structure State where
  /-- The ongoing computations. -/
  status : Std.HashMap String Nat := {}
  /-- Whether any progress has been made at all. If all computations have been finished
  and no progress has been made, then inform the user. -/
  progress : Bool := false
  /-- The suggestions that close the goal. -/
  solvedSuggestions : Array Html := #[]

/-- The information required for pasting a suggestion into the editor. -/
structure Context where
  /-- The current document -/
  «meta» : DocumentMeta
  /-- The range that should be replaced.
  In tactic mode, this should be the range of the suggestion tactic.
  In infoview mode, the start and end of the range should both be the cursor position. -/
  cursorPos : Lsp.Position
  /-- Whether to use the `on_goal n =>` combinator. -/
  onGoal : Option Nat
  /-- The preceding piece of syntax, if available. It is not available if the cursor is
  at the start of the next tactic. This is used for merging consecutive `rw` tactics. -/
  stx : Option (TSyntax `tactic)
  /-- The token for updating the main HTML body of suggestions.
  This is used for displaying a message that no progress has happened. -/
  masterToken : RefreshToken
  /-- The token for the `⏳️` HTML that represents the state of the ongoing computations. -/
  statusToken : RefreshToken
  /-- The token for the solved goals. -/
  solvedToken : RefreshToken
  /-- The main goal. -/
  goal : MVarId
  /-- The selected hypothesis, if any. -/
  hyp? : Option FVarId
  /-- The position of the selected subexpression. -/
  pos : SubExpr.Pos

/-- The monad used in `#click_suggestions`. -/
abbrev ClickSuggestionsM := ReaderT Context <| ReaderT (IO.Ref State) MetaM

instance : MonadStateOf State ClickSuggestionsM where
  get := do (← readThe (IO.Ref State)).get
  modifyGet s := do (← readThe (IO.Ref State)).modifyGet s
  set s := do (← readThe (IO.Ref State)).set s

/-- Signify that at least one suggestion has been made. -/
def markProgress : ClickSuggestionsM Unit := do
  if !(← get).progress then
    modify ({ · with progress := true })

/-- Check whether any suggestion has been made. -/
private def checkProgress : ClickSuggestionsM Unit := do
  if !(← get).progress then
    if ((← get).status).isEmpty then
      (← read).masterToken.update <| .text "No suggestions were found."

/-- Get the syntax of the variable whose type the user selected. -/
def getHypIdent? : ClickSuggestionsM (Option Ident) := do
  let some fvarId := (← read).hyp? | return none
  return mkIdent (← fvarId.getUserName)

/-- Get the variable whose type the user selected. -/
def getHypIdent! : ClickSuggestionsM Ident := do
  let some fvarId := (← read).hyp? | throwError "no hypothesis was selected"
  return mkIdent (← fvarId.getUserName)

/-- Run a computation in such a way that we can keep track of it. -/
def trackingComputation {α} (name : String) (k : ClickSuggestionsM α) : ClickSuggestionsM α := do
  modify (fun s ↦ { s with status := s.status.alter name fun
    | none => some 0
    | some n => some (n + 1) })
  renderStatus
  try k
  finally
    modify (fun s ↦ { s with status := s.status.alter name fun
      | some (n + 1) => some n
      | _ => none })
    renderStatus
    checkProgress
where
  /-- If the set of computations is non-empty, display a `⏳️` symbol with hover information that
  shows all of the ongoing computations. -/
  renderStatus : ClickSuggestionsM Unit := do
    let { status, .. } ← get
    let { statusToken, .. } ← read
    statusToken.update <|
      if status.isEmpty then
        .text ""
      else
        -- TODO: use a fancier throbber instead of `⏳️`?
        let title := "ongoing computations: " ++ String.intercalate ", " status.keys;
        <span title={title}> {.text "⏳️"} </span>

section Meta

/-- Determine whether the explicit parts of two expressions are equal,
and the implicit parts are definitionally equal, up to `reducible_and_instances` transparency.
This says whether two expressions are 'morally equal', and is used for deduplicating suggestions. -/
partial def isExplicitEq (t s : Expr) : MetaM Bool := do
  let t := t.cleanupAnnotations; let s := s.cleanupAnnotations
  if t == s then
    return true
  unless t.getAppNumArgs == s.getAppNumArgs && t.getAppFn == s.getAppFn do
    return false
  let tArgs := t.getAppArgs
  let sArgs := s.getAppArgs
  -- TODO: let's just use `getFunInfo`.
  let bis ← getBinderInfos t.getAppFn tArgs
  t.getAppNumArgs.allM fun i _ =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
      withNewMCtxDepth <| withReducibleAndInstances <| isDefEq tArgs[i]! sArgs[i]!
where
  /-- Get the `BinderInfo`s for the arguments of `mkAppN fn args`. -/
  getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
    let mut fnType ← inferType fn
    let mut result := Array.mkEmpty args.size
    let mut j := 0
    for i in [:args.size] do
      unless fnType.isForall do
        fnType ← whnfD (fnType.instantiateRevRange j i args)
        j := i
      let .forallE _ _ b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
      fnType := b
      result := result.push bi
    return result

end Meta

section Syntax
open Syntax Parser.Tactic

/-- Information about the rewrite position. This is used to determine whether to suggest
`rw`, `rw!`, `nth_rw`, or `simp_rw`. -/
inductive RwKind where
  /-- `rw` cannot rewrite here, because the subexpression contains bound variables.
  So, we suggest `simp_rw`. -/
  | hasBVars
  /-- If `motiveTypeCorrect := true`, we suggest `rw!` instead of `rw`.
  If `occ := some n`, we suggest `nth_rw n` instead of `rw`. -/
  | valid (motiveTypeCorrect : Bool) (occ : Option Nat)

/-- Construct the syntax for a rewrite tactic. -/
def mkRewrite (kind : RwKind) (symm : Bool) (e : Term) (loc : Option Ident)
    (grw := false) : CoreM (TSyntax `tactic) := do
  let rule ← if symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)
  if grw then
    match kind with
    | .valid _ none => `(tactic| grw [$rule] $[at $loc:term]?)
    | .valid _ (some n) => `(tactic| nth_grw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| grw [$rule] $[at $loc:term]?)
  else
    match kind with
    | .valid true none => `(tactic| rw [$rule] $[at $loc:term]?)
    | .valid true (some n) => `(tactic| nth_rw $(mkNatLit n):num [$rule] $[at $loc:term]?)
    | .valid false none => `(tactic| rw! [$rule] $[at $loc:term]?)
    | .valid false (some n) =>
      let occs ← `(optConfig| ($(mkIdent `occs):ident := .$(mkIdent `pos) [$(mkNatLit n)]))
      `(tactic| rw! $occs [$rule] $[at $loc:term]?)
    | .hasBVars => `(tactic| simp_rw [$rule] $[at $loc:term]?)

/-- Try to combine the suggested tactic with the preceding tactic in the tactic sequence.
In particular, we merge sequences of `rw`, `simp_rw` and `grw`. -/
partial def mergeTactics? {m} [Monad m] [MonadQuotation m] (stx₁ stx₂ : TSyntax `tactic) :
    m (Option (TSyntax `tactic)) := do
  match stx₁, stx₂ with
  | `(tactic| on_goal $n₁ => $tac₁:tactic), `(tactic| on_goal $n₂ => $tac₂:tactic) =>
    if n₁.getNat == n₂.getNat then
      if let some tac ← mergeTactics? tac₁ tac₂ then
        return ← `(tactic| on_goal $n₁ => $tac:tactic)
  | `(tactic| rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| simp_rw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| simp_rw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| simp_rw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | `(tactic| grw [$[$rules₁],*] $[at $h₁:ident]?),
    `(tactic| grw [$[$rules₂],*] $[at $h₂:ident]?) =>
    if h₁.map (·.getId) == h₂.map (·.getId) then
      return ← `(tactic| grw [$[$(rules₁ ++ rules₂)],*] $[at $h₁:ident]?)
  | _, _ => pure ()
  return none

/-- Given tactic syntax `tac` that we want to paste into the editor, return it as a string.
This function respects the 100 character limit for long lines. -/
def tacticPasteString (tac : TSyntax `tactic) : ClickSuggestionsM String := do
  let column := (← read).cursorPos.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column

/-- Given tactic syntax `tac`, compute the text edit that will paste it into the editor.
We return the range that should be replaced, and the new text that will replace it. -/
def mkInsertion (tac : TSyntax `tactic) : ClickSuggestionsM (Lsp.Range × String) := do
  if let some stx := (← read).stx then
    if let some tac ← mergeTactics? stx tac then
      if let some range := stx.raw.getRange? then
        let text := (← read).meta.text
        let endPos := max (text.lspPosToUtf8Pos (← read).cursorPos) range.stop
        let extraWhitespace := range.stop.extract text.source endPos
        let tactic ← tacticPasteString tac
        return (text.utf8RangeToLspRange ⟨range.start, endPos⟩, tactic ++ extraWhitespace)
  return (⟨(← read).cursorPos, (← read).cursorPos⟩,
    s!"{← tacticPasteString tac}\n{String.replicate (← read).cursorPos.character ' '}")

end Syntax

section Widget

open Widget

/-- Generate a suggestion for inserting `tac`, with message `html`.
The button is `[apply]` if the tactic does not close the goal, and `[done]` if it is closing. -/
def mkSuggestion (tac : TSyntax `tactic) (html : Html) (isClosing := false) :
    ClickSuggestionsM Html := do
  let tac ← match (← read).onGoal with
    | some n => `(tactic| on_goal $(Syntax.mkNatLit (n + 1)) => $tac:tactic)
    | none => pure tac
  let (range, newText) ← mkInsertion tac (← read)
  let buttonText := if isClosing then "[done] " else "[apply] "
  let button :=
    -- TODO: The hover on this button should be a `CodeWithInfos`, instead of a string.
    <span style={json% { "white-space" : "pre"}} className="font-code">
    { .ofComponent MakeEditLink (.ofReplaceRange (← read).meta range newText) #[.text buttonText] }
    </span>;
  return <div display="flex"
    style={json% { "display" : "flex", "align-items" : "flex-start", "margin-bottom" : "1em" }}>
    {button} {html}
    </div>

/-- Add suggestion `tac` to the list of tactics that solve the goal. -/
def addSolvedSuggestion (tac : TSyntax `tactic) : ClickSuggestionsM Unit := do
  let html ← mkSuggestion tac (.text (← PrettyPrinter.ppTactic tac).pretty) (isClosing := true)
  modify fun s ↦ { s with solvedSuggestions := s.solvedSuggestions.push html }
  (← read).solvedToken.update <details «open»={true}>
    <summary className="mv2 pointer">
    These tactics solve the goal: 🎉️
    </summary>
    {.element "div" #[] (← get).solvedSuggestions}
    </details>

end Widget

/-- Return whether `kabstract` uniquely finds pattern `p` in `e` at position `targetPos`. -/
def kabstractFindsPositions (e p : Expr) (targetPos : SubExpr.Pos) : MetaM Bool := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let foundRef ← IO.mkRef false
  let rec visit (e : Expr) (pos : SubExpr.Pos) : MetaM Unit := do
    let visitChildren : MetaM Unit := do
      match e with
      | .app f a         => visit f pos.pushAppFn; visit a pos.pushAppArg
      | .mdata _ e       => visit e pos
      | .proj _ _ e      => visit e pos.pushProj
      | .letE _ t v b _  =>
        visit t pos.pushLetVarType; visit v pos.pushLetValue; visit b pos.pushLetBody
      | .lam _ d b _     => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain; visit b pos.pushBindingBody
      | _                => pure ()
    if e.hasLooseBVars then
      visitChildren
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren
    else
      if ← isDefEq e p then
        if pos == targetPos then
          foundRef.set true
        else
          throwError "{p} unified with {e}"
      else
        if pos == targetPos then
          throwError "{p} did not unify with {e}"
        else
          visitChildren
  try
    visit e .root
    foundRef.get
  catch _ =>
    return false

end Mathlib.Tactic.ClickSuggestions
