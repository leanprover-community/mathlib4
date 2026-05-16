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

inductive Premise where
  | const (declName : Name)
  | fvar (fvarId : FVarId)
  deriving Inhabited

namespace Premise

def toString : Premise → String
  | .const name | .fvar ⟨name⟩ => name.toString

def length (premise : Premise) : Nat :=
  premise.toString.length

def getType : Premise → MetaM Expr
  | .const name => (·.type) <$> getConstInfo name
  | .fvar fvarId => fvarId.getType

def forallMetaTelescopeReducing : Premise → MetaM (Expr × Array Expr × Array BinderInfo × Expr)
  | .const name => do
    let thm ← mkConstWithFreshMVarLevels name
    let result ← Meta.forallMetaTelescopeReducing (← inferType thm)
    return (mkAppN thm result.1, result)
  | .fvar fvarId => do
    let decl ← fvarId.getDecl
    let result ← Meta.forallMetaTelescopeReducing (← instantiateMVars decl.type)
    return (mkAppN decl.toExpr result.1, result)

def unresolveName : Premise → MetaM Name
  | .const name => do
    unresolveNameGlobalAvoidingLocals name (fullNames := getPPFullNames (← getOptions))
  | .fvar fvarId => fvarId.getUserName

def toMessageData : Premise → MessageData
  | .const name => .ofConstName name
  | .fvar fvarId => .ofExpr (.fvar fvarId)

def toHtml : Premise → MetaM Html
  | .const name => constToHtml name
  | .fvar fvarId => exprToHtml (.fvar fvarId)

end Premise

/-- The information required for pasting a suggestion into the editor -/
structure State where
  /-- The ongoing computations. -/
  status : Std.HashMap String Nat := {}

/-- The information required for pasting a suggestion into the editor -/
structure Context where
  /-- The current document -/
  «meta» : DocumentMeta
  /-- The range that should be replaced.
  In tactic mode, this should be the range of the suggestion tactic.
  In infoview mode, the start and end of the range should both be the cursor position. -/
  cursorPos : Lsp.Position
  /-- Whether to use the `on_goal n =>` combinator. -/
  onGoal : Option Nat
  /-- The preceding piece of syntax. This is used for merging consecutive `rw` tactics. -/
  stx : TSyntax `tactic
  /-- Whether any progress has been made at all. If all computations have been finished
  and no progress has been made, then inform the user. -/
  progress? : IO.Ref Bool
  /-- The token for updating the main HTML body of suggestions.
  This is used for displaying a message that no progress has happened. -/
  masterToken : RefreshToken
  /-- The token for the HTML that represents the state of the ongoing computations. -/
  statusToken : RefreshToken
  /-- The main goal. -/
  goal : MVarId
  /-- The selected hypothesis, if any. -/
  hyp? : Option FVarId
  /-- The position of the selected subexpression. -/
  pos : SubExpr.Pos

abbrev clickSuggestionsM := ReaderT Context StateRefT State MetaM

def markProgress : clickSuggestionsM Unit := do
  if !(← (← read).progress?.get) then
    (← read).progress?.set true

def checkProgress : clickSuggestionsM Unit := do
  if !(← (← read).progress?.get) then
    if ((← get).status).isEmpty then
      (← read).masterToken.update <| .text "No suggestions were found."

def getHypIdent? : clickSuggestionsM (Option Ident) := do
  let some fvarId := (← read).hyp? | return none
  return mkIdent (← fvarId.getUserName)

def getHypIdent! : clickSuggestionsM Ident := do
  let some fvarId := (← read).hyp? | throwError "no hypothesis was selected"
  return mkIdent (← fvarId.getUserName)

def trackingComputation {α} (name : String) (k : clickSuggestionsM α) : clickSuggestionsM α := do
  modify (fun s ↦ { s with status := s.status.alter name fun
    | none => some 0
    | some n => some (n + 1) })
  try k
  finally
    modify (fun s ↦ { s with status := s.status.alter name fun
      | some (n + 1) => some n
      | _ => none })
    checkProgress

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
def mergeTactics? {m} [Monad m] [MonadRef m] [MonadQuotation m] (stx₁ stx₂ : TSyntax `tactic) :
    m (Option (TSyntax `tactic)) := do
  match stx₁, stx₂ with
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
def tacticPasteString (tac : TSyntax `tactic) : clickSuggestionsM String := do
  let tac ← if let some n := (← read).onGoal then
      `(tactic| on_goal $(mkNatLit (n + 1)) => $(tac):tactic)
    else
      pure tac
  let column := (← read).cursorPos.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column

/-- Given tactic syntax `tac`, compute the text edit that will paste it into the editor.
We return the range that should be replaced, and the new text that will replace it. -/
def mkInsertion (tac : TSyntax `tactic) : clickSuggestionsM (Lsp.Range × String) := do
  if let some tac ← mergeTactics? (← read).stx tac then
    if let some range := (← read).stx.raw.getRange? then
      let text := (← read).meta.text
      let endPos := max (text.lspPosToUtf8Pos (← read).cursorPos) range.stop
      let extraWhitespace := range.stop.extract text.source endPos
      let tactic ← tacticPasteString tac (← read)
      return (text.utf8RangeToLspRange ⟨range.start, endPos⟩, tactic ++ extraWhitespace)
  return (⟨(← read).cursorPos, (← read).cursorPos⟩,
    s!"{← tacticPasteString tac (← read)}\n{String.replicate (← read).cursorPos.character ' '}")

end Syntax

section Widget

open Widget

def mkSuggestion (tac : TSyntax `tactic) (html : Html) (isText := false) :
    clickSuggestionsM Html := do
  let (range, newText) ← mkInsertion tac (← read)
  let button :=
    -- TODO: The hover on this button should be a `CodeWithInfos`, instead of a string.
    <span className="font-code"> {
      Html.ofComponent MakeEditLink
        (.ofReplaceRange (← read).meta range newText)
        #[<a
          className={"mh2 codicon codicon-insert"}
          style={json% { "position" : "relative", "top" : "0.15em"}}
          title={(← PrettyPrinter.ppTactic tac).pretty} />] }
    </span>;
  let html := if isText then <span style={json% { "margin-top" : "0.15em" }}> {html} </span>
    else html
  return <div display="flex"
    style={json% { "display" : "flex", "align-items" : "flex-start", "margin-bottom" : "1em" }}>
    {button} {html}
    </div>

/-- Create a suggestion for inserting `stx` and tactic name `tac`. -/
def mkTacticSuggestion (stx tac : TSyntax `tactic) (html : Html) (isText := false) :
    clickSuggestionsM Html := do
  mkSuggestion stx (isText := isText)
    <div> <div>{html}</div> <div>{← tacticToHtml tac}</div> </div>

@[inline]
def mkIncrementalSuggestions (name : String)
    (k : (Html → clickSuggestionsM Unit) → clickSuggestionsM Unit) : clickSuggestionsM Html :=
  mkRefreshComponentM (.text "") fun token ↦ trackingComputation name do
    let htmls ← IO.mkRef #[]
    k fun html ↦ do
      markProgress
      htmls.modify (·.push html)
      token.update (.element "div" #[] (← htmls.get))

end Widget

def kabstractFindsPositions (e p : Expr) (targetPos : SubExpr.Pos) : MetaM Bool := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec
  /-- The main loop that loops through all subexpressions -/
  visit (e : Expr) (pos : SubExpr.Pos) :
      ExceptT Bool MetaM Unit := do
    let visitChildren (found := false) : ExceptT Bool MetaM Unit := do
      if pos == targetPos then
        throwThe _ found
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
        visitChildren true
      else
        visitChildren
  match ← ExceptT.run <| visit e .root with
  | .ok () => throwError "invalid position {targetPos} in {e}"
  | .error found => return found

end Mathlib.Tactic.ClickSuggestions
