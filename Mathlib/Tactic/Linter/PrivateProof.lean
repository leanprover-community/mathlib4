/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Meta.Tactic.TryThis
-- for the syntax kind of the `private` term elaborator, which the linter suggests and must not
-- fire inside of
public meta import Mathlib.Util.PrivateProof
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# The `privateProof` linter

This linter finds uses of `set_option backward.privateInPublic true` which are (at least partly)
caused by a *proof term* appearing in a public position, and suggests wrapping that proof term in
the `private` term elaborator from `Mathlib.Util.PrivateProof` instead.

This is a throwaway linter, intended only to drive a one-off sweep over Mathlib; it is not meant to
be enabled permanently.

## How it works

Declaration types, and declaration values which would be exposed (`abbrev`s, data instances,
`@[expose]` definitions, definitions in an `expose` section; see `Lean.Elab.MutualDef.finishElab`),
are elaborated in an exporting environment, in which private declarations do not resolve. Proofs
written as `by ...` blocks with a `Prop` goal leave the exporting scope and are abstracted into
auxiliary theorems (see `Lean.Elab.Term.runTactic`), so they may freely mention private
declarations. *Bare term* proofs do not: they are elaborated in the exporting environment, and hence
require either `backward.privateInPublic` or an explicit `private` wrapper, which abstracts them
into a public auxiliary theorem in the same way `by` does.

The linter therefore proceeds as follows, for each command elaborated with
`backward.privateInPublic` set to `true`:

1. It reads the declarations of the current module from the stateful linter `moduleDecls`; the
   private ones are exactly those a reference to which the option permits.
2. It walks the infotrees of the command looking for references to those private declarations
   which were elaborated in an exporting environment (the same condition that
   `Lean.checkPrivateInPublic` warns about), keeping track of the enclosing terms and `by` blocks.
   References enclosed in a `by` block with a `Prop` goal are discarded: the infotree contexts
   inside such a block still claim to be exporting, since `runTactic` does not save a new one.
3. For each remaining reference, it finds the innermost enclosing term which is a proof whose *type*
   does not itself mention private declarations, i.e. the innermost term that `private` could
   successfully abstract into a public auxiliary theorem, and suggests wrapping it.

Note that the environment *after* the command is not a usable criterion here: nested proofs in
definition values are abstracted into auxiliary theorems whether or not they came from a `by` block
(see `Lean.Meta.abstractNestedProofs`), and the values of those theorems are not exported. So a
declaration can require the option during elaboration and still mention no private declaration
publicly once added. See `publicPrivateNames`, which is used only to annotate the references that
cannot be fixed by `private` at all.

## Implementation notes

We never re-print the terms we suggest wrapping: the infotrees are not guaranteed to contain
original syntax, but the syntax they do contain is canonical, so we use its positions to read the
original text back out of the `FileMap`.

Inserting `private ` in front of a term `t` at position `p` makes the elaborator parse the *longest*
term starting at `p`, and the resulting term must be accepted where a term of arbitrary precedence
is not necessarily allowed. So we parenthesize unless
* no enclosing term in the infotree starts at `p` as well (i.e. `t` really is the longest term
  starting at `p`), and
* the token preceding `p` opens a position in which a term of precedence 0 is accepted.
-/

meta section

open Lean Elab Command Linter Meta Meta.Tactic.TryThis

namespace Mathlib.Linter

/-- The `privateProof` linter flags proof terms which force the use of
`set_option backward.privateInPublic true`, and suggests wrapping them in the `private` term
elaborator instead. -/
public register_option linter.privateProof : Bool := {
  defValue := true
  descr := "enable the `privateProof` linter"
}

/-- Whether to warn when something does not appear in a proof. -/
public register_option linter.privateProof.notInProof : Bool := {
  defValue := false
  descr := "enable warning when not in proof `privateProof` linter"
}

namespace PrivateProof

/-- Debugging output for the `privateProof` linter. -/
public register_option debugPrivateProof : Bool := {
  defValue := false
  descr := "enable debugging output for the `privateProof` linter"
}

/-- A stateful linter which records the declarations of the current module.

Its persistent state is the set of declarations of the current module as of the end of the previous
command; its pre-phase state is the array of declarations added by the current command. -/
public initialize moduleDecls : StatefulLinter NameSet (Array Name) ←
  registerStatefulLinter (σ := NameSet) (τ := Array Name) (∅ : NameSet)
    (pre := fun _ prev _ => do
      let mut new := #[]
      for (n, _) in (← getEnv).constants.map₂ do
        unless prev.contains n do
          new := new.push n
      return some new)
    (post := fun _ _ _ _ _ => do
      let mut decls : NameSet := ∅
      for (n, _) in (← getEnv).constants.map₂ do
        decls := decls.insert n
      return decls)

/-- An occurrence of a private constant in an exporting environment, together with the terms
enclosing it, outermost first. The last entry of `path` is the reference itself. -/
private structure Occurrence where
  /-- The enclosing terms, outermost first, paired with the context they were elaborated in. -/
  path : Array (ContextInfo × TermInfo)
  /-- The enclosing `by` blocks, outermost first. -/
  byBlocks : Array (ContextInfo × TacticInfo)
  /-- The private constant that was referenced. -/
  privateName : Name

/-- Whether this term is already wrapped in something that elaborates it in a non-exporting
environment: either the `private` term elaborator, or `private_decl%`, which is what
`field := private ..` in a structure instance expands to (see
`Lean.Elab.Term.StructInst.mkStructInstField`). -/
private def isPrivateWrapper (ti : TermInfo) : Bool :=
  ti.stx.isOfKind ``Mathlib.Tactic.PrivateProof.privateElab ||
    ti.stx.isOfKind ``Parser.Term.privateDecl

/-- Collects the references to constants in `privateNames` which were elaborated in an exporting
environment, together with their enclosing terms and `by` blocks. -/
private partial def collect (privateNames : NameSet) (ctx? : Option ContextInfo)
    (path : Array (ContextInfo × TermInfo)) (byBlocks : Array (ContextInfo × TacticInfo))
    (acc : Array Occurrence) : InfoTree → Array Occurrence
  | .context i t => collect privateNames (i.mergeIntoOuter? ctx?) path byBlocks acc t
  | .node i children =>
    let (path, byBlocks, acc) :=
      match ctx?, i with
      | some ctx, .ofTermInfo ti =>
        let path := path.push (ctx, ti)
        let acc := match ti.expr with
          -- Note the `isIdent` check: wrapper nodes such as `(..)` also carry the constant as
          -- their `expr`, and are not references to it.
          | .const n _ =>
            if ti.stx.isIdent && !ti.isBinder && ctx.env.isExporting && privateNames.contains n
                && !path.any (isPrivateWrapper ·.2) then
              acc.push ⟨path, byBlocks, n⟩
            else
              acc
          | _ => acc
        (path, byBlocks, acc)
      | some ctx, .ofTacticInfo ti =>
        -- `by` blocks appear as tactic nodes; there is no term info for them.
        if ti.stx.isOfKind ``Parser.Term.byTactic then
          (path, byBlocks.push (ctx, ti), acc)
        else
          (path, byBlocks, acc)
      | _, _ => (path, byBlocks, acc)
    let ctx? := i.updateContext? ctx?
    children.foldl (init := acc) fun acc t => collect privateNames ctx? path byBlocks acc t
  | .hole _ => acc

/-- Whether `private` could abstract this term into a public auxiliary theorem: it must be a proof,
and its type must not itself mention private declarations.

The metavariable context we have here is the one saved at the nearest enclosing context node, not
the one in force when this term was elaborated, so `instantiateMVars` can produce an expression
mentioning free variables which are not in `ti.lctx` (giving "unknown free variable"), or leave
metavariables which `inferType` then cannot handle. There is nothing useful to say about such a
term, so we treat a failure as "not wrappable"; if no enclosing term is wrappable, the reference is
reported for manual inspection anyway. -/
private def isWrappableProof (ctx : ContextInfo) (ti : TermInfo) : CommandElabM Bool := do
  try
    ctx.runMetaM ti.lctx do
      let e ← instantiateMVars ti.expr
      if e.hasSorry || e.isFVar then return false
      unless ← isProof e do return false
      let ty ← instantiateMVars (← inferType e)
      return !ty.getUsedConstants.any isPrivateName
  catch _ =>
    return false

/-- Whether this `by` block proves a proposition: such a block is elaborated in a non-exporting
environment and abstracted into an auxiliary theorem, so nothing inside it needs `private`. (This is
not visible in the infotree contexts, which are saved further out.)

As in `isWrappableProof`, the check can fail on ill-scoped expressions; we assume a proof in that
case, since `by` blocks proving propositions are the overwhelming majority and a spurious
suggestion inside one would be worse than a missed one. -/
private def isProofByBlock (ctx : ContextInfo) (ti : TacticInfo) : CommandElabM Bool := do
  let some goal := ti.goalsBefore.head? | return false
  let some decl := ti.mctxBefore.decls.find? goal | return false
  let ctx := { ctx with mctx := ti.mctxBefore }
  try
    -- Note that the goal's own local context is required here: its type generally mentions the
    -- local hypotheses of the declaration being elaborated.
    ctx.runMetaM decl.lctx do isProp (← instantiateMVars decl.type)
  catch _ =>
    return true

/-- Tokens after which a term of precedence 0 may appear, so that `private t` need not be
parenthesized. -/
private def precZeroOpeners : Array String :=
  #["(", "⟨", "[", "{", ",", ":=", "=>", "↦", "|", ";", "then", "else", "do", "from", "exact",
    "refine", "<|", "$", "·"]

/-- Whether the token preceding `pos` in `source` opens a position accepting a term of
precedence 0. -/
private def precedingTokenIsOpener (source : String) (pos : String.Pos.Raw) : Bool :=
  let before := (String.Pos.Raw.extract source ⟨0⟩ pos).toSlice.trimAsciiEnd
  let tk := before.takeEndWhile (!·.isWhitespace)
  tk.isEmpty || precZeroOpeners.any (tk.endsWith ·)

/-- The suggestion for a single occurrence: the term to wrap, and whether it needs parenthesizing.
-/
private structure Wrap where
  /-- The term `private` should be attached to. -/
  ti : TermInfo
  /-- The range of `ti` in the source. -/
  range : Lean.Syntax.Range
  /-- Whether the result must be parenthesized. -/
  parens : Bool

/-- Finds the term that `private` should be attached to for the given occurrence, if any. -/
private def findWrap (source : String) (occ : Occurrence) : CommandElabM (Option Wrap) := do
  -- Find the innermost wrappable enclosing term.
  let mut inner? := none
  for i in [0 : occ.path.size] do
    let idx := occ.path.size - 1 - i
    let some (ctx, ti) := occ.path[idx]? | continue
    let some range := ti.stx.getRange? | continue
    unless range.start < range.stop do continue
    if ← isWrappableProof ctx ti then
      inner? := some (idx, ti, range)
      break
  let some (idx, innerTi, innerRange) := inner? | return none
  let opener := precedingTokenIsOpener source innerRange.start
  -- Find the outermost enclosing term starting at the same position: inserting `private ` at that
  -- position would wrap that term, not the inner one.
  let mut outer := idx
  for i in [0 : idx] do
    let j := idx - 1 - i
    let some (_, ti) := occ.path[j]? | break
    let some range := ti.stx.getRange? | break
    unless range.start == innerRange.start do break
    outer := j
  if outer == idx then
    return some ⟨innerTi, innerRange, !opener⟩
  let some (outerCtx, outerTi) := occ.path[outer]? | return some ⟨innerTi, innerRange, true⟩
  let some outerRange := outerTi.stx.getRange? | return some ⟨innerTi, innerRange, true⟩
  if opener && (← isWrappableProof outerCtx outerTi) then
    return some ⟨outerTi, outerRange, false⟩
  else
    return some ⟨innerTi, innerRange, true⟩

/-- Whether `stx` is the `optionValue` `val`. The value of a `set_option` is an atom, but we also
look through a single wrapping node in case that changes. -/
private def isOptionValue (stx : Syntax) (val : String) : Bool :=
  let atom := if stx.isAtom then stx else if stx.getNumArgs == 1 then stx[0] else .missing
  match atom with
  | .atom _ v => v == val
  | _ => false

/-- The ranges, in the chain of `set_option .. in`s wrapping the current command, of those which
set `backward.privateInPublic` to `true` or `backward.privateInPublic.warn` to `false`, each
running from the `set_option` keyword through the whitespace following the `in`, so that deleting
one removes its whole line. -/
public partial def redundantOptionRanges (stx : Syntax) : Array Lean.Syntax.Range := Id.run do
  let mut deleteRefs := #[]
  for stx in stx.topDown do
    if stx.isOfKind ``Parser.Command.in && stx[0].isOfKind ``Parser.Command.set_option then
      -- `Command.in` is a trailing parser: the `set_option` command, the `in` token, the command it
      -- applies to (which is the rest of the chain).
      let rest := redundantOptionRanges stx[2]
      let redundant :=
        (stx[0][1].getId == `backward.privateInPublic && isOptionValue stx[0][3] "true") ||
        (stx[0][1].getId == `backward.privateInPublic.warn && isOptionValue stx[0][3] "false")
      if redundant then
        match stx[0].getPos?, stx[1].getTrailingTailPos? with
        | some start, some stop => deleteRefs := deleteRefs.push ⟨start, stop⟩
        | _, _ => continue
  return deleteRefs

/-- The private declarations of the current module which appear in public positions of the
declarations added by the current command.

Note that this is *not* the criterion the linter uses: nested proofs are abstracted into auxiliary
theorems after elaboration (see `Lean.Meta.abstractNestedProofs`), whose values are not exported, so
a declaration can require `backward.privateInPublic` during elaboration and still not mention any
private declaration publicly once it is added. This is only used to report the (rarer) cases in
which the option is needed for something that is *not* a proof, and hence cannot be fixed by
`private`. -/
private def publicPrivateNames (newDecls : Array Name) (moduleNames : NameSet) :
    CommandElabM NameSet := do
  let publicEnv := (← getEnv).setExporting true
  let mut offenders : NameSet := ∅
  for decl in newDecls do
    if isPrivateName decl then continue
    let some ci := publicEnv.find? decl | continue
    let mut consts := ci.type.getUsedConstants
    if let some value := ci.value? then
      consts := consts ++ value.getUsedConstants
    for c in consts do
      if isPrivateName c && moduleNames.contains c then
        offenders := offenders.insert c
  return offenders

/-- The main entry point of the `privateProof` linter. It is run with the options of the command
with any leading `set_option ... in`s peeled off, but `stx` is the whole command, so that we can
also suggest deleting those `set_option`s. -/
private def check (stx : Syntax) (newDecls : Array Name) (moduleNames : NameSet) :
    CommandElabM Unit := do
  let debug := debugPrivateProof.get (← getOptions)
  unless ← ResolveName.backward.privateInPublic.getM do return
  -- The private declarations of the current module: a reference to one of these in an exporting
  -- environment is exactly what `backward.privateInPublic` permits.
  let privateNames := moduleNames.filter isPrivateName
  if privateNames.isEmpty then return
  let source := (← getFileMap).source
  let mut occurrences : Array Occurrence := #[]
  for tree in (← getInfoState).trees do
    occurrences := collect privateNames none #[] #[] occurrences tree
  if occurrences.isEmpty then return
  if debug then
    logInfo m!"new decls: {newDecls.toList}\nstill public: \
      {(← publicPrivateNames newDecls moduleNames).toList}\noccurrences: {occurrences.size}"
    for occ in occurrences do
      let descrs := occ.path.map fun (p : ContextInfo × TermInfo) =>
        let r? : Option Nat := p.2.stx.getRange?.map fun (r : Lean.Syntax.Range) => r.start.byteIdx
        m!"({p.2.stx.getKind}, {repr r?}, exporting := {p.1.env.isExporting})"
      logInfo m!"occurrence of {occ.privateName} in {occ.byBlocks.size} `by` blocks: {descrs.toList}"
  let mut wraps : Array Wrap := #[]
  let mut unfixable : Array (Syntax × Name) := #[]
  for occ in occurrences do
    -- References inside a `by` block proving a proposition are already abstracted away.
    if ← occ.byBlocks.anyM fun (ctx, ti) => isProofByBlock ctx ti then continue
    match ← findWrap source occ with
    | some wrap =>
      unless wraps.any (·.range == wrap.range) do
        wraps := wraps.push wrap
    | none =>
      if let some (_, ti) := occ.path.back? then
        unless unfixable.any (·.1 == ti.stx) do
          unfixable := unfixable.push (ti.stx, occ.privateName)
  -- Drop wraps nested inside other wraps: the outer `private` already covers them.
  let outermostWraps := wraps.filter fun w =>
    !wraps.any fun w' => w'.range != w.range && w'.range.includes w.range
  for wrap in outermostWraps do
    let text := String.Pos.Raw.extract source wrap.range.start wrap.range.stop
    let suggestion := if wrap.parens then s!"(private {text})" else s!"private {text}"
    liftCoreM <| addSuggestion wrap.ti.stx { suggestion := .string suggestion }
      (origSpan? := wrap.ti.stx)
      (header := "This proof term requires `backward.privateInPublic`; wrap it instead:")
  if unfixable.isEmpty then
    -- Every reference in this command can be wrapped, so the `set_option`s enabling the option for
    -- it should no longer be needed. One suggestion per `set_option`, not per wrap.
    for range in redundantOptionRanges stx do
      liftCoreM <| addSuggestion (Syntax.ofRange range)
        { suggestion := .string "", messageData? := m!"(delete)" }
        (origSpan? := Syntax.ofRange range)
        (header := "With the proof terms of this command wrapped in `private`, this \
          `set_option` should be unnecessary; delete it:")
  else
    if ← linter.privateProof.notInProof.getM then
      let stillPublic ← publicPrivateNames newDecls moduleNames
      for (refStx, name) in unfixable do
        let note := if stillPublic.contains name then
            " (and it is still referenced publicly after elaboration)"
          else
            ""
        logLint linter.privateProof refStx m!"The private declaration `{name}` is referenced in an \
          exporting environment here{note}, but no enclosing proof term could be wrapped in \
          `private`."

/-- The `privateProof` linter proper: see the module docstring. -/
public initialize privateProofLinter : StatefulLinter Unit Unit ←
  registerStatefulLinter (σ := Unit) (τ := Unit) ()
    (post := fun stx _ _ readPrev readPre => do
      unless getLinterValue linter.privateProof (← getLinterOptions) do return
      if ← MonadLog.hasErrors then return
      unless (← getEnv).header.isModule do return
      let some newDecls := readPre moduleDecls | return
      if newDecls.isEmpty then return
      let moduleNames := (readPrev moduleDecls).insertMany newDecls
      -- Note that the options are those of the innermost command, but `check` is given the whole
      -- command syntax, `set_option .. in`s and all.
      withSetOptionIn (fun _ => check stx newDecls moduleNames) stx)

end PrivateProof

end Mathlib.Linter
