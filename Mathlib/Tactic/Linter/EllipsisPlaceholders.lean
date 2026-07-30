/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Mathlib.Lean.ContextInfo
public meta import Mathlib.Lean.Elab.InfoTree
public meta import Mathlib.Lean.Linter
public meta import Lean.Meta.Tactic.TryThis
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Lean.Parser.Term

/-!
# Linter for trailing `_` placeholders in function applications

When a function application ends with at least `linter.style.ellipsisPlaceholders.minTrailingHoles`
consecutive `_` placeholders (default: `4`, i.e. `≥ 4`), the linter suggests replacing them with `..`.

For example, `foo 1 _ _ _ _` becomes `foo 1 ..`.

Only anonymous `_` holes count toward the trailing run. Synthetic holes `?_` are ignored for
counting, and any application whose suffix (after the last concrete argument) contains `?_` is
skipped entirely, since `..` does not reliably substitute for them in patterns such as
`@f _ _ _ _ ?_ ?_` or `f _ _ _ ?_ _ _`.

Before suggesting a replacement, the linter re-elaborates the proposed syntax in the original
local context and requires definitional equality with the original expression. If that check fails
or throws (for example due to loose bound variables in a simproc pattern), the site is skipped.

Sites are also skipped when partial application must be preserved: the context `expectedType` is
a function, the head-normal form is a lambda, or the function's codomain after all syntax
arguments (including trailing holes) is still a `Π`-type. `@`-explicit applications are skipped
as well. WHNF is not run on expressions with loose bound variables (info-tree replay), since
that panics; those sites are skipped conservatively. The unsafe `manualReplacementIsSafe`
fallback was removed.

Re-elaboration is skipped inside declaration bodies when the expression still contains unresolved
metavariables, since validating there can assign those metavariables and break the surrounding
elaboration.

It also rejects non-suffix runs of holes, since `..` fills every remaining argument greedily.
For example, `apply f _ _ x` is not flagged.

Typed holes `(_ : T)` are never rewritten: `..` cannot preserve the type annotation, which
breaks typeclass inference and proof scripts. Pipe projection (`e |>.f`) is out of scope
because it uses a distinct parser node, not `Parser.Term.app`.

Syntax inside match patterns, `let`/`if let` binding patterns, and attribute templates is skipped.
Simproc and other exotic sites are validated by re-elaboration; failures are skipped silently.

Set `linter.style.ellipsisPlaceholders.trace` to log skipped sites during validation.
-/

meta section

open Lean Elab Command Linter Meta Term

namespace Mathlib.Linter

/-- Enable the trailing-ellipsis linter. -/
public register_option linter.style.ellipsisPlaceholders : Bool := {
  defValue := false
  descr := "enable the ellipsisPlaceholders linter"
}

/-- Minimum trailing `_` count before suggesting `..` (inclusive lower bound; `4` means `≥ 4`). -/
public register_option linter.style.ellipsisPlaceholders.minTrailingHoles : Nat := {
  defValue := 4
  descr := "minimum trailing `_` count (≥) before suggesting `..` in function applications"
}

/-- Log when a candidate is skipped after validation fails or throws. -/
register_option linter.style.ellipsisPlaceholders.trace : Bool := {
  defValue := false
  descr := "trace ellipsisPlaceholders validation skips"
}

namespace Style.ellipsisPlaceholders

/-!
### Syntax analysis
-/

/-- Parsed application meeting the configured trailing-hole threshold. -/
structure AppCandidate where
  stx : Syntax
  fn : Syntax
  args : Array Syntax
  trailingHoles : Nat

def isNamedArg (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Term.namedArgument

def isSyntheticHole (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Term.syntheticHole

/-- Whether syntax is an `_` placeholder, optionally through parentheses. -/
partial def isHoleLike (stx : Syntax) (allowParen : Bool := true) : Bool :=
  if isNamedArg stx then
    false
  else if stx.isOfKind ``Lean.Parser.Term.hole then
    true
  else if stx.isOfKind ``Lean.Parser.Term.typeAscription then
    stx.getNumArgs > 1 && isHoleLike stx[1] allowParen
  else if allowParen && stx.isOfKind ``Lean.Parser.Term.paren then
    stx.getNumArgs > 1 && isHoleLike stx[1] allowParen
  else
    false

abbrev isHoleArg (stx : Syntax) : Bool :=
  isHoleLike stx true

/-- Whether syntax is a typed hole `(_ : T)` (possibly parenthesized). -/
partial def isTypedHoleArg (stx : Syntax) : Bool :=
  if stx.isOfKind ``Lean.Parser.Term.typeAscription then
    stx.getNumArgs > 1 && (stx[1].isOfKind ``Lean.Parser.Term.hole ||
      (stx[1].isOfKind ``Lean.Parser.Term.paren && stx[1].getNumArgs > 1 &&
        stx[1][1].isOfKind ``Lean.Parser.Term.hole))
  else if stx.isOfKind ``Lean.Parser.Term.paren && stx.getNumArgs > 1 then
    isTypedHoleArg stx[1]
  else
    false

structure AppArgAnalysis where
  trailingHoles : Nat
  hasSyntheticInSuffix : Bool
  hasTypedHoleInSuffix : Bool

/-- Count trailing plain `_` holes and detect `?_` anywhere in the hole suffix. -/
def analyzeAppArgs (args : Array Syntax) : AppArgAnalysis :=
  let trailingHoles :=
    let rec count (i acc : Nat) : Nat :=
      if i > 0 then
        let j := i - 1
        if h : j < args.size then
          if isHoleArg args[j] then count j (acc + 1) else acc
        else acc
      else acc
    count args.size 0
  let suffixStart :=
    let rec walkSuffix (i : Nat) : Nat :=
      if i > 0 then
        let j := i - 1
        if h : j < args.size then
          if isHoleArg args[j] || isSyntheticHole args[j] then walkSuffix j else i
        else 0
      else 0
    walkSuffix args.size
  let hasSyntheticInSuffix :=
    let rec anySynthetic (i : Nat) : Bool :=
      if h : i < args.size then
        isSyntheticHole args[i] || anySynthetic (i + 1)
      else
        false
    anySynthetic suffixStart
  let hasTypedHoleInSuffix :=
    let rec anyTyped (i : Nat) : Bool :=
      if i > 0 then
        let j := i - 1
        if h : j < args.size then
          if isHoleArg args[j] then
            isTypedHoleArg args[j] || anyTyped j
          else
            false
        else
          false
      else
        false
    anyTyped args.size
  { trailingHoles, hasSyntheticInSuffix, hasTypedHoleInSuffix }

def splitAppArgs (rawArgs : Array Syntax) : Array Syntax × Bool :=
  if rawArgs.isEmpty then
    (rawArgs, false)
  else if rawArgs.back!.isOfKind ``Lean.Parser.Term.ellipsis then
    (rawArgs.pop, true)
  else
    (rawArgs, false)

def analyzeApp? (stx : Syntax) (minTrailingHoles : Nat) : Option AppCandidate :=
  if !stx.isOfKind ``Lean.Parser.Term.app then
    none
  else if stx.getNumArgs < 2 then
    none
  else
    let rawArgs := stx[1].getArgs
    let (args, hasEllipsis) := splitAppArgs rawArgs
    if hasEllipsis then
      none
    else
      let analysis := analyzeAppArgs args
      if analysis.hasSyntheticInSuffix || analysis.hasTypedHoleInSuffix ||
          analysis.trailingHoles < minTrailingHoles then
        none
      else
        some { stx, fn := stx[0], args, trailingHoles := analysis.trailingHoles }

private def skippedContextKinds : Array SyntaxNodeKind := #[
  ``Lean.Parser.Term.namedPattern,
  ``Lean.Parser.Term.attributes]

private def markerBeforeTermKind (k : SyntaxNodeKind) : Option String :=
  if k == ``Lean.Parser.Term.matchAlt || k == ``Lean.Parser.Term.matchAltExpr then
    some "=>"
  else if k == ``Lean.Parser.Term.letDecl || k == ``Lean.Parser.Term.letIdDecl ||
      k == ``Lean.Parser.Term.letPatDecl then
    some ":="
  else if k == ``Lean.Parser.Term.fun then
    some "=>"
  else
    none

/-- Traverse command syntax, skipping patterns and other non-term regions. -/
partial def collectApps (stx : Syntax) (minTrailingHoles : Nat) : Array AppCandidate :=
  go stx #[] true
where
  go (stx : Syntax) (acc : Array AppCandidate) (inTerm : Bool) : Array AppCandidate :=
    let acc :=
      if inTerm then
        match analyzeApp? stx minTrailingHoles with
        | some c => acc.push c
        | none => acc
      else
        acc
    match stx with
    | .node _ k args =>
      if skippedContextKinds.contains k then
        args.foldl (fun a s => go s a false) acc
      else if let some marker := markerBeforeTermKind k then
        goUntilMarker args acc marker
      else
        args.foldl (fun a s => go s a inTerm) acc
    | _ => acc

  goUntilMarker (args : Array Syntax) (acc : Array AppCandidate) (marker : String) :
      Array AppCandidate :=
    let rec loop (i : Nat) (acc : Array AppCandidate) (inTerm : Bool) : Array AppCandidate :=
      if h : i < args.size then
        let arg := args[i]
        if arg.isAtom && arg.getAtomVal == marker then
          loop (i + 1) acc true
        else
          loop (i + 1) (go arg acc inTerm) inTerm
      else
        acc
    loop 0 acc false

def candidateRangeKey (stx : Syntax) : Option (Nat × Nat) :=
  stx.getRange?.map fun r => (r.start.byteIdx, r.stop.byteIdx)

def syntaxRangesMatch (a b : Syntax) : Bool :=
  match a.getRange?, b.getRange? with
  | some ra, some rb => ra == rb
  | _, _ => false

def termInfoMatchesCandidate (ti : TermInfo) (c : AppCandidate) (minTrailingHoles : Nat) : Bool :=
  let target := c.stx
  ti.stx == target ||
    (match analyzeApp? ti.stx minTrailingHoles with
      | some analyzed => syntaxRangesMatch target analyzed.stx
      | none => false) ||
    syntaxRangesMatch target ti.stx

/-!
### Validation
-/

def domainHasDefault (domain : Expr) : Bool :=
  domain.isOptParam || domain.isAutoParam || domain.getOptParamDefault?.isSome ||
    domain.getAutoParamTactic?.isSome

partial def skipImplicitBinders (ty : Expr) (explicit : Bool) : MetaM Expr := do
  if explicit then
    return ty
  else
    match ty with
    | .forallE _ _ body bi =>
      if bi.isExplicit then
        return ty
      else
        skipImplicitBinders body explicit
    | _ => return ty

/-- `@`-prefixed function in an application. -/
partial def isExplicitApp (stx : Syntax) : Bool :=
  match stx[0] with
  | `(@$_) => true
  | _ =>
    stx[0].isOfKind ``Lean.Parser.Term.explicitUniv ||
      (stx[0].isOfKind ``Lean.Parser.Term.app && isExplicitApp stx[0])

/-- Walk the function type, collecting domain types of positional arguments. -/
partial def explicitPositionalParamTypes (fn : Expr) (explicit : Bool) (args : Array Syntax) :
    MetaM (Array Expr) := do
  let mut ty ← inferType fn
  let mut result := #[]
  for arg in args do
    if isNamedArg arg then
      let name := arg[1].getId.eraseMacroScopes
      let mut found := false
      while !found do
        ty ← skipImplicitBinders ty explicit
        match ty with
        | .forallE binderName _ body _ =>
          if binderName == name then
            ty := body
            found := true
          else
            ty := body
        | _ => break
      continue
    ty ← skipImplicitBinders ty explicit
    match ty with
    | .forallE _ dom body _ =>
      result := result.push dom
      ty := body
    | _ => break
  return result

/-- Fallback when re-elaboration fails: reject if trailing parameters have defaults. -/
def manualReplacementIsSafe (fn : Expr) (explicit : Bool) (args : Array Syntax)
    (trailingHoles : Nat) : MetaM Bool := do
  let types ← explicitPositionalParamTypes fn explicit args
  if types.size < trailingHoles then
    return false
  let start := types.size - trailingHoles
  for i in [start:types.size] do
    if domainHasDefault types[i]! then
      return false
  return true

/-- WHNF only on well-scoped expressions; ill-scoped info-tree replay must not panic. -/
def whnfIfScoped (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.hasLooseBVars then
    return e
  try whnf e catch _ => return e

/-- True when `ty` is a `Π`-type (including implications). -/
partial def isFunctionType (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  match ty with
  | .forallE _ _ _ _ => return true
  | _ =>
    if ty.hasLooseBVars then
      return true
    match (← whnfIfScoped ty) with
    | .forallE _ _ _ _ => return true
    | _ => return false

/-- True when `e` reduces to a lambda (eta-expanded partial application). -/
def exprIsLambda (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  match e with
  | .lam _ _ _ _ => return true
  | _ =>
    if e.hasLooseBVars then
      return true
    match (← whnfIfScoped e) with
    | .lam _ _ _ _ => return true
    | _ => return false

/-- Walk `fn`'s type along `args`; return the codomain after all arguments are consumed. -/
partial def codomainAfterAppArgs (fn : Expr) (explicit : Bool) (args : Array Syntax) :
    MetaM Expr := do
  let mut ty ← inferType fn
  for arg in args do
    if isNamedArg arg then
      let name := arg[1].getId.eraseMacroScopes
      let mut found := false
      while !found do
        ty ← skipImplicitBinders ty explicit
        match ty with
        | .forallE binderName _ body _ =>
          ty := body
          if binderName == name then found := true
        | _ => return ty
      continue
    ty ← skipImplicitBinders ty explicit
    match ty with
    | .forallE _ _ body _ => ty := body
    | _ => break
  return ty

/-- True when consuming all syntax arguments still leaves a function codomain on the head. -/
def appArgsLeaveFunctionCodomain (fn : Expr) (explicit : Bool) (args : Array Syntax) : MetaM Bool := do
  isFunctionType (← codomainAfterAppArgs fn explicit args)

def traceSkip (msg : MessageData) : CommandElabM Unit := do
  if linter.style.ellipsisPlaceholders.trace.get (← getOptions) then
    logInfo msg

/-- Reject `..` when partial application must be preserved at this site. -/
def rejectsPartialApplication (ti : TermInfo) (c : AppCandidate) : MetaM Bool := do
  try
    if isExplicitApp c.stx then
      return true
    if let some expected := ti.expectedType? then
      if ← isFunctionType expected then
        return true
    let e ← instantiateMVars ti.expr
    if ← exprIsLambda e then
      return true
    let fn := e.getAppFn
    if ← appArgsLeaveFunctionCodomain fn (isExplicitApp c.stx) c.args then
      return true
    return false
  catch _ =>
    return true

/-- Re-elaborate the proposed replacement and require definitional equality with the original. -/
def replacementIsSafe (ctx : ContextInfo) (lctx : LocalContext) (info : TermInfo)
    (replacement : Syntax) : CommandElabM Bool := do
  try
    ctx.runMetaMWithMessages lctx do
      let target ← instantiateMVars info.expr
      let replacementExpr ← TermElabM.run' do
        withoutErrToSorry do
          withSynthesize do
            let expected ← match info.expectedType? with
              | some ty => instantiateMVars ty
              | none => inferType target
            elabTermEnsuringType replacement expected
      let target ← instantiateMVars target
      let replacementExpr ← instantiateMVars replacementExpr
      if !(← isDefEq replacementExpr target) then
        return false
      match info.expectedType? with
      | none => return true
      | some expected =>
        let expected ← instantiateMVars expected
        let expectedIsFn ← isFunctionType expected
        let replacementIsFn ← isFunctionType (← inferType replacementExpr)
        return expectedIsFn == replacementIsFn
  catch _ =>
    return false

def isInteractiveCommandDecl (decl : Name) : Bool :=
  decl == `_check || decl == `_reduce || decl == `_synth_cmd

/-- Conservative skip to avoid assigning still-live metavariables during validation.

Top-level commands such as `#check foo 1 _ _` are still linted. Inside a declaration body,
if the subterm still contains metavariables (typical for `_` holes in a proof), skip validation
entirely rather than re-elaborating in the shared metavariable context. -/
def shouldSkipValidation (ctx : ContextInfo) (lctx : LocalContext) (ti : TermInfo) :
    CommandElabM Bool := do
  match ctx.parentDecl? with
  | none => return false
  | some decl =>
    if isInteractiveCommandDecl decl then
      return false
    ctx.runMetaMWithMessages lctx do
      return (← instantiateMVars ti.expr).hasExprMVar

def replacementAllowed (ctx : ContextInfo) (lctx : LocalContext) (ti : TermInfo)
    (c : AppCandidate) (suggested : Syntax) : CommandElabM Bool := do
  if ← shouldSkipValidation ctx lctx ti then
    return false
  let rejectPartial ← ctx.runMetaMWithMessages ti.lctx do
    rejectsPartialApplication ti c
  if rejectPartial then
    traceSkip "ellipsisPlaceholders: skipped application (partial application / function type)"
    return false
  replacementIsSafe ctx lctx ti suggested

def mkEllipsis (info : SourceInfo) : Syntax :=
  mkNode ``Lean.Parser.Term.ellipsis #[Syntax.atom info ".."]

def rewriteApp (c : AppCandidate) : Syntax :=
  let info := c.stx.getHeadInfo
  let newArgs := c.args.take (c.args.size - c.trailingHoles) |>.push (mkEllipsis info)
  mkNode ``Lean.Parser.Term.app #[c.fn, mkNullNode newArgs]

/-- Replace `old` with `new` in a syntax tree, keyed by range when nodes differ. -/
partial def replaceSyntax (root old new : Syntax) : Syntax :=
  if root == old || syntaxRangesMatch root old then
    new
  else
    match root with
    | .node info k args => .node info k (args.map fun arg => replaceSyntax arg old new)
    | _ => root

def rewriteStopPos (stx : Syntax) : Nat :=
  stx.getRange?.map (·.stop.byteIdx) |>.getD 0

/-- Apply validated rewrites from right to left so ranges stay stable. -/
def applyAllRewrites (stx : Syntax) (rewrites : Array (Syntax × Syntax)) : Syntax :=
  let rewrites := rewrites.qsort fun a b => rewriteStopPos a.1 > rewriteStopPos b.1
  rewrites.foldl (fun acc (old, new) => replaceSyntax acc old new) stx

def foldInfoM {α m} [Monad m] (f : ContextInfo → Info → α → m α) (init : α) (t : InfoTree) : m α :=
  InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init) t

/-- Collect `(old, new)` rewrites that pass validation for a command. Requires info trees. -/
def collectValidatedRewrites (cmdStx : Syntax) (minTrailingHoles : Nat) :
    CommandElabM (Array (Syntax × Syntax)) := do
  let candidates := collectApps cmdStx minTrailingHoles
  if candidates.isEmpty then
    return #[]
  let mut acc : Array (Syntax × Syntax) × Std.HashSet (Nat × Nat) := (#[], {})
  for tree in ← getInfoTrees do
    acc ← foldInfoM (fun ctx info acc => do
      let (rewrites, seen) := acc
      let .ofTermInfo ti := info | return acc
      let mut rewrites := rewrites
      let mut seen := seen
      for c in candidates do
        unless termInfoMatchesCandidate ti c minTrailingHoles do
          continue
        match candidateRangeKey c.stx with
        | none => continue
        | some key =>
          if seen.contains key then
            continue
          let some (lctx, _) := Info.getLCtx? info | continue
          let suggested := rewriteApp c
          unless ← replacementAllowed ctx lctx ti c suggested do
            continue
          rewrites := rewrites.push (c.stx, suggested)
          seen := seen.insert key
      return (rewrites, seen)) acc tree
  return acc.1

/-- Re-elaborate a command after applying all validated rewrites; return an error if it fails. -/
def validateCommandWithAllRewrites (cmdStx : Syntax) (minTrailingHoles : Nat) :
    CommandElabM (Option MessageData) := do
  let rewrites ← collectValidatedRewrites cmdStx minTrailingHoles
  if rewrites.isEmpty then
    return none
  let modified := applyAllRewrites cmdStx rewrites
  try
    elabCommand modified
    return none
  catch e =>
    return some e.toMessageData

/-!
### Linter driver
-/

def tryLintCandidate (ctx : ContextInfo) (lctx : LocalContext) (ti : TermInfo)
    (c : AppCandidate) : CommandElabM Bool := do
  try
    if ← shouldSkipValidation ctx lctx ti then
      traceSkip "ellipsisPlaceholders: skipped application (unresolved metavariables in declaration body)"
      return false
    let suggested := rewriteApp c
    unless ← replacementAllowed ctx lctx ti c suggested do
      traceSkip "ellipsisPlaceholders: skipped application (validation failed)"
      return false
    Linter.logLint linter.style.ellipsisPlaceholders c.stx <|
      m!"Replace {c.trailingHoles} trailing `_` placeholders with `..`."
    liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion c.stx
      { suggestion := .tsyntax (kind := `term) ⟨suggested⟩ } (origSpan? := c.stx)
    return true
  catch e =>
    traceSkip m!"ellipsisPlaceholders: skipped application ({e.toMessageData})"
    return false

def lintCandidatesFromTree (tree : InfoTree) (candidates : Array AppCandidate)
    (minTrailingHoles : Nat) (seen : Std.HashSet (Nat × Nat)) : CommandElabM (Std.HashSet (Nat × Nat)) :=
  foldInfoM (fun ctx info seen => do
    let .ofTermInfo ti := info | return seen
    let mut seen := seen
    for c in candidates do
      unless termInfoMatchesCandidate ti c minTrailingHoles do
        continue
      match candidateRangeKey c.stx with
      | none => continue
      | some key =>
        if seen.contains key then
          continue
        let some (lctx, _) := Info.getLCtx? info | continue
        if ← tryLintCandidate ctx lctx ti c then
          seen := seen.insert key
    return seen) seen tree

@[inherit_doc linter.style.ellipsisPlaceholders]
def ellipsisPlaceholdersLinter : Linter where
  run := whenLinterActivated linter.style.ellipsisPlaceholders fun stx => do
    unless (← getInfoState).enabled do
      return
    let minTrailingHoles := linter.style.ellipsisPlaceholders.minTrailingHoles.get (← getOptions)
    if minTrailingHoles == 0 then
      return
    let candidates := collectApps stx minTrailingHoles
    if candidates.isEmpty then
      return
    let mut seen : Std.HashSet (Nat × Nat) := {}
    for tree in ← getInfoTrees do
      seen ← lintCandidatesFromTree tree candidates minTrailingHoles seen

initialize addLinter ellipsisPlaceholdersLinter

/-- Test-only: elaborate `cmd`, apply every validated ellipsis rewrite, and re-elaborate. -/
elab "#guard_ellipsis_rewrites " cmd:command : command => do
  elabCommand cmd
  let minTrailingHoles := linter.style.ellipsisPlaceholders.minTrailingHoles.get (← getOptions)
  match ← validateCommandWithAllRewrites cmd.raw minTrailingHoles with
  | none => pure ()
  | some err =>
    throwError "batch ellipsis rewrite failed to re-elaborate:{indentD err}"

end Style.ellipsisPlaceholders

end Mathlib.Linter
