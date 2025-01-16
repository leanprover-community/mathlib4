/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Batteries.Data.NameSet
import Mathlib.Tactic.DeclarationNames

/-!
#  The "unusedVariableCommand" linter

The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/

open Lean Parser Elab Command

namespace Lean.Syntax
/-!
# `Syntax` filters
-/

/--
`filterMapM stx f` takes as input
* `stx : Syntax` and
* a monadic function `f : Syntax → m (Option α)`.

It returns the array of all "`some`" values of `f` on all syntax sub-terms of `stx`.
-/
partial
def filterMapM {α} {m : Type → Type} [Monad m] (stx : Syntax) (f : Syntax → m (Option α)) :
    m (Array α) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

/--
`filterMap stx f` takes as input
* `stx : Syntax` and
* a function `f : Syntax → Option α`.

It returns the array of all "`some`" values of `f` on all syntax sub-terms of `stx`.
-/
def filterMap {α} (stx : Syntax) (f : Syntax → Option α) : Array α :=
  stx.filterMapM (m := Id) f

/--
`filter stx f` takes as input
* `stx : Syntax` and
* a predicate `f : Syntax → Bool`.

It returns the array of all syntax sub-terms of `stx` satisfying `f`.
-/
def filter (stx : Syntax) (f : Syntax → Bool) : Array Syntax :=
  stx.filterMap (fun s => if f s then some s else none)

end Lean.Syntax

namespace Mathlib.Linter

/--
The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/
register_option linter.unusedVariableCommand : Bool := {
  defValue := true
  descr := "enable the unusedVariableCommand linter"
}

/--
Toggles whether or not the linter prints the variables that it considers "used" in `def`initions.
-/
register_option showDefs : Bool := {
  defValue := false
  descr := "shows which variables are introduced in a definition"
}

/-- `varsTracker` is the main tool to keep track of used variables.
* `seen` are the unique names of the variables that have been used by some declaration.
* `dict` is the mapping from unique names to the `Syntax` node of the corresponding variable.
  There is an exception: for variables introduced with `variable ... in`, the `Syntax`
  node is the whole `variable` command.
-/
structure varsTracker where
  /-- The unique names of the variables that have been used. -/
  seen : NameSet := {}
  /-- The map from unique names of variables to the corresponding syntax node. -/
  dict : NameMap Syntax := {}
  /-- The map from unique names of variables to the corresponding pretty-printed expression. -/
  defDict : NameMap Format := {}
  deriving Inhabited

/-- A `varsTracker` is empty if its constituents are empty. -/
def varsTracker.isEmpty (v : varsTracker) : Bool :=
  v.seen.isEmpty && v.dict.isEmpty

namespace UnusedVariableCommand

/--
`usedVarsRef` stores a `varsTracker`.

The intended updates to `varsTracker` should go via
* `usedVarsRef.addUsedVarName` to add a used variable;
* `usedVarsRef.addDict` to add a correspondence `unique name <--> syntax`;
* `usedVarsRef.addTemp` to extend the temporary storage of information from `variable ... in`.
-/
initialize usedVarsRef : IO.Ref varsTracker ← IO.mkRef {}

/--
`#show_used` is a convenience function that prints a summary of the variables that have been
defined so far and whether or not they have been used at the point where `#show_used` is called.
-/
elab "#show_used" : command => do
  let varRef ← Mathlib.Linter.UnusedVariableCommand.usedVarsRef.get
  if varRef.dict.isEmpty then logInfo "No variables present." else
  let mut msg := #[m!"Dictionary\n"]
  let sorted := varRef.dict.toList.toArray.qsort (·.2.prettyPrint.pretty < ·.2.prettyPrint.pretty)
  let (used, unused) := sorted.partition (varRef.seen.contains ·.1)
  for (a, b) in used do
    msg := msg.push (checkEmoji ++ m!" {b.prettyPrint.pretty} ↔ {a}")
  for (a, b) in unused do
    msg := msg.push (crossEmoji ++ m!" {b.prettyPrint.pretty} ↔ {a}")
  msg := msg.push "" |>.push m!"{checkEmoji}: used" |>.push m!"{crossEmoji}: unused"
  logInfo <| .joinSep msg.toList "\n"

/-- Add the (unique) name `a` to `varsTracker.seen`: these are the variable names that some
declaration used. -/
def usedVarsRef.addUsedVarName (a : Name) : IO Unit := do
  usedVarsRef.modify fun varTrack => {varTrack with seen := varTrack.seen.insert a}

/-- Add the assignment `a → ref` to `varsTracker.dict`, where
* `a` is the *unique name* (not the username) of a variable and
* `ref` is the syntax node that introduces the variable with unique name `a`.
-/
def usedVarsRef.addDict (a : Name) (ref : Syntax) : IO Unit := do
  usedVarsRef.modify fun varTrack =>
    if varTrack.dict.contains a then varTrack
    else {varTrack with dict := varTrack.dict.insert a ref}

def usedVarsRef.addDefDict (a : Name) (ref : Format) : IO Unit := do
  usedVarsRef.modify fun varTrack =>
    if varTrack.defDict.contains a then varTrack
    else {varTrack with defDict := varTrack.defDict.insert a ref}

/--
`includedVariables plumb` returns the unique `Name`, the user `Name` and the `Expr` of
each `variable` that is present in the current context.
While doing this, it also updates the "unique-var-name-to-Syntax" dictionary with the variables
from the local context.

Finally, the `Bool`ean `plumb` decides whether or not `includedVariables` also extends the
`NameSet` of variables that have been used in some declaration.
-/
def includedVariables (def? : Bool) (plumb : Bool) : TermElabM (Array (Name × Name × Expr)) := do
  let c ← read
  let fvs := c.sectionFVars
  let mut varIds := #[]
  let lctx ← getLCtx
  for (a, b) in fvs do
    let ref ← getRef
    if (lctx.findFVar? b).isNone then
      if def? then
        usedVarsRef.addDefDict a (← Meta.ppExpr (← Meta.inferType b))
      else
        usedVarsRef.addDict a ref
    if (lctx.findFVar? b).isSome then
      let mut fd := .anonymous
      for (x, y) in c.sectionVars do
        if y == a then fd := x
      varIds := varIds.push (a, fd, b)
      if plumb then
        usedVarsRef.addUsedVarName a
  return varIds

/--
The tactic `included_variables` reports which variables are included in the current declaration.

The variant `included_variables plumb` is intended only for the internal use of the
unused variable command linter: besides printing the message, `plumb` also adds records that
the variables included in the current declaration really are included.
-/
elab "included_variables" dd:(ppSpace "!")? plumb:(ppSpace &"plumb")? : tactic => do
    let (_plb, usedUserIds) := (← includedVariables dd.isSome plumb.isSome).unzip
    let msgs ← usedUserIds.mapM fun (userName, expr) =>
      return m!"'{userName}' of type '{← Meta.inferType expr}'"
    if ! msgs.isEmpty then
      logInfo m!"{msgs.foldl (m!"{·}\n" ++ m!"* {·}") "Included variables:"}"

/-- The `NameSet` of all the `SyntaxNodeKinds` of all the binders. -/
abbrev binders : NameSet := .ofList [
  ``Lean.Parser.Term.explicitBinder,
  ``Lean.Parser.Term.strictImplicitBinder,
  ``Lean.Parser.Term.implicitBinder,
  ``Lean.Parser.Term.instBinder,
]

/--
`findBinders stx` extracts all syntax nodes in `stx` representing binders.

*Note*. This is a crude function and more structured solutions, such as `mkThm`
should be preferred, if possible.
-/
partial
def findBinders (stx : Syntax) : Array Syntax :=
  stx.filter (binders.contains ·.getKind)

/--
`getExtendBinders stx` finds the first `extends` node in `stx` and, from there,
extracts all binders, returning them as an array of instance-implicit syntax nodes.
-/
def getExtendBinders {m} [Monad m] [MonadRef m] [MonadQuotation m] (stx : Syntax) :
    m (Array Syntax) := do
  if let some exts := stx.find? (·.isOfKind ``Lean.Parser.Command.extends) then
    let exts := exts[1].getArgs.filter (·.getAtomVal != ",")
    let exts ← exts.mapM (`(Lean.Parser.Term.instBinder| [$(⟨·⟩)]))
    return exts
  else return #[]

variable (nm : Ident) (binders : TSyntaxArray [`ident, ``Term.hole, ``Term.bracketedBinder])
  (typ : Syntax) in
/--
`mkThmCore nm binders typ` returns the `Syntax` for
`theorem nm binders* : type := by included_variables plumb; sorry`.
-/
def mkThmCore {m} [Monad m] [MonadRef m] [MonadQuotation m] : m Syntax :=
  `(command| theorem $nm $binders* : $(⟨typ⟩) := by included_variables plumb; sorry)

/-- `mkThm stx` inspects `stx` and, if it is a declaration, it extracts, where available,
the binders and the expected type, to produce a new `theorem` using `mkThmCore`.

This is the more "structured" sibling of `mkThm'`, that tries to handle the cases that slip through
the cracks of the matching in `mkThm`.
-/
def mkThm {m} [Monad m] [MonadQuotation m] [MonadRef m] (stx : Syntax) : m Syntax := do
  let fls := mkIdent `False
  let (id, hyps, typ) := ← match stx with
    | `($_:declModifiers abbrev $did:declId $as* : $t $_:declVal) =>
      return (did, as, (← `($(mkIdent `toFalse) $t)))
    | `($_:declModifiers def $did:declId $as* : $t $_:declVal) =>
      return (did, as, (← `($(mkIdent `toFalse) $t)))
    | `($_:declModifiers def $did:declId $as* $_:declVal) =>
      return (did, as, fls)
    | `($_:declModifiers instance $(_optNamedPrio)? $(did)? $as* : $t $_:declVal) =>
      return (did.getD default, as, (← `($(mkIdent `toFalse) $t)))
    | `($_:declModifiers theorem $did:declId $as* : $t $_:declVal) =>
      return (did, as, (← `($(mkIdent `toFalse) $t)))
    | `($_:declModifiers structure $did:declId $as* extends $es,* :=
        $(_optCtor)? $_t:structFields) => do
      let exts ← es.getElems.mapM fun d => `(Term.instBinder| [$d])
      return (did, as.map (⟨·⟩) ++ exts.map (⟨·⟩), fls)
    | _ => return (default, #[], fls)
  let newNm := id.raw[0].getId ++ `sfx
  mkThmCore (mkIdent newNm) hyps typ

/-- `getPropValue stx` assumes that `stx` is the syntax of some declaration and returns a
`Prop`-valued `Syntax` term.
It also assumes that there is a function `toFalse : _ → Prop`.
(Such a function is internally generated by the rest of the linter and its value is always `False`.)

If `stx` is a non-`structure` that contains a `typeSpec` node `ts` (e.g. all `theorem`s) , then
`getPropValue` returns `toFalse ts`, otherwise it returns `False`.
-/
def getPropValue {m} [Monad m] [MonadRef m] [MonadQuotation m] (stx : Syntax) : m Syntax := do
  let flse ← `($(mkIdent `False))
  if (stx.find? (·.isOfKind ``Command.structure)).isSome then
    return flse
  if let some ts := stx.find? (·.isOfKind ``Term.typeSpec) then
    `($(mkIdent `toFalse) $(⟨ts[1]⟩))
  else
    return flse

open Lean.Parser.Term in
/--
Like `Lean.Elab.Command.getBracketedBinderIds`, but returns the identifier `Syntax`,
rather than the `Name`, in the given bracketed binder.
-/
def getBracketedBinderIds : Syntax → Array Syntax
  | `(bracketedBinderF|($ids* $[: $ty?]? $(_annot?)?)) => ids
  | `(bracketedBinderF|{$ids* $[: $ty?]?})             => ids
  | `(bracketedBinderF|⦃$ids* : $_⦄)                   => ids
  | `(bracketedBinderF|[$id : $_])                     => #[id]
  | `(bracketedBinderF|[$f])                           => #[f]
  | _                                                  => #[]

/--
`getNamelessVars exp` takes as input an expression, assumes that it is an iterated
`forallE`/`lam` and reports whether or not each such constructor has macro-scoped name or not.
This information is used by `getForallStrings`.
-/
def getNamelessVars : Expr → Array Bool
  | .forallE na _x bod _bi | .lam na _x bod _bi => #[na.hasMacroScopes] ++ getNamelessVars bod
  | _ => #[]

/-- `getForallStrings expr` takes as input an `Expr`ession `expr`, and recursively extracts a
string from `expr`, for every `.forallE` constructor with which `expr` starts, returning them
as an array.

If the name associated to a `.forallE` constructor has macro-scopes (e.g. it is nameless),
then the string is the pretty-printed name of the type of the variable, stripped out of any
possible universe annotations.
If the `.forallE` has an associated name that is not macro-scoped, then the string is the name of
the binder.

These strings are used to find used variables in the case of `def`-based declarations.

This is not perfect, but works well in practice.
-/
def getForallStrings (e : Expr) : MetaM (Array String) :=
  try
    if e == default then return #[] else
    let infers? := getNamelessVars e
    Meta.forallTelescopeReducing e fun xs _ =>
      (xs.zip infers?).mapM fun (exp, infer?) => do
        let typ := ← if infer? then Meta.inferType exp else return exp
        -- strip out universe annotations
        return (← Meta.ppExpr (typ.setPPUniverses false)).pretty
  catch _ => return #[]

/--
`getUsedVariableFromName declName` takes as input the name `declName` of a declaration.

It retrieves its `type` and returns the binder names of `type`, using `getForallStrings`.

This is used on `def`-like declaration to try to determine the section `variable`s that the
declaration uses.
-/
def getUsedVariableFromName (declName : Name) : CommandElabM (Array String) := do
  let env ← getEnv
  let decl := (env.find? declName).getD default
  let (d, _) ← liftCoreM do Meta.MetaM.run do getForallStrings decl.type
  if Linter.getLinterValue showDefs (← getOptions) then
    dbg_trace "getForallStrings: {d}"
  return d

/--
`getUsedVariableNames pos` takes as input a position `pos`.

Assuming that `pos` is the beginning of a declaration identifiers, `getUsedVariableNames` finds
which declaration starts at `pos`, retrieves its `type` and returns the binder names of `type`.

This is used on `def`-like declaration to try to determine the section `variable`s that the
declaration uses.
-/
def getUsedVariableNames (pos : String.Pos) : CommandElabM (Array String) := do
  let declNames ← getNamesFrom pos
  let vars ← declNames.mapM (getUsedVariableFromName ∘ Syntax.getId)
  return vars.flatten

/-- `lemmaToThm stx` assumes that `stx` is of kind `lemma` and converts it into `theorem`. -/
def lemmaToThm (stx : Syntax) : Syntax :=
  let toDecl := stx.replaceM (m := Id) fun d =>
    match d with
      | .node kind `group args => return some (.node kind ``Command.theorem args)
      | _ => return none
  let toDecl := toDecl.replaceM (m := Id) fun d =>
    match d with
      | atm@(.atom _ "lemma") => return (mkAtomFrom atm "theorem")
      | _ => return none
  let toDecl := toDecl.replaceM (m := Id) fun d =>
    match d with
      | .node kind `lemma args => return some (.node kind ``declaration args)
      | _ => return none
  toDecl

/--
`exampleToDef stx` assumes that `stx` is of kind `example` and converts it into `def`.

We go to `def` from `example`, since the inclusion mechanism for variables is the same in the two
commands (and different from `theorem`).
-/
def exampleToDef (stx : Syntax) (nm : Name) : Syntax :=
  let toDecl := stx.replaceM (m := Id) fun d =>
    match d with
      | .node kind ``Command.example args => do
        let did := .node default ``Lean.Parser.Command.declId #[mkIdent nm, mkNullNode #[]]
        return some (.node kind ``definition ((args.insertIdx! 1 did).push (mkNullNode #[])))
      | _ => return none
  let toDecl := toDecl.replaceM (m := Id) fun d =>
    match d with
      | atm@(.atom _ "example") => return (mkAtomFrom atm "def")
      | _ => return none
  toDecl

/-- `cleanUpExplicitUniverses stx` takes as input a syntax node `stx` and removes explicit
universe annotations from it.

It may not work well if there are several universe annotations present.
-/
def cleanUpExplicitUniverses (stx : Syntax) : Syntax :=
  stx.replaceM (m := Id) fun s =>
    if s.isOfKind ``Lean.Parser.Term.explicitUniv then
      let firstPos := s[0].getPos?.getD default
      let lastPos := (s.getArgs.back?.getD default).getHeadInfo.getTailPos?.getD default
      some (mkIdentFrom (.ofRange ⟨firstPos, lastPos⟩) s[0].getId)
    else none

@[inherit_doc Mathlib.Linter.linter.unusedVariableCommand]
def unusedVariableCommandLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.unusedVariableCommand (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- rather than just reporting on a `Parser.isTerminalCommand`,
  -- we look inside `stx` to find a terminal command.
  -- This simplifies testing: writing `open Nat in #exit` prints the current linter output
  if (stx.find? (Parser.isTerminalCommand ·)).isSome then
    let varTrack ← usedVarsRef.get
    let sorted := varTrack.seen.toArray.qsort (·.toString < ·.toString)
    let unused := varTrack.dict.toList.filter (!sorted.contains ·.1)
    let fm ← getFileMap
    for (uniq, user) in unused do
      let rg := user.getRange?.getD default
      let var : Substring := {
          str := fm.source
          startPos := rg.start
          stopPos := rg.stop
        }
      let toPrint := match uniq.eraseMacroScopes with
        | .anonymous => user.prettyPrint.pretty
        | x          => x.toString
      if rg == default || var.toString != toPrint then
        logInfoAt user "Rebuild the file to get accurate variable information."
      Linter.logLint linter.unusedVariableCommand user
        m!"'{toPrint}' is unused {user.getRange?.map fun r => (r.start, r.stop)}"
  -- if there is a `variable` command in `stx`, then we update `usedVarsRef` with all the
  -- information that is available
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.variable)).isSome then
    let scope ← getScope
    let pairs := scope.varUIds.zip (scope.varDecls.map getBracketedBinderIds).flatten
    for (uniq, user) in pairs do
      if Linter.getLinterValue showDefs (← getOptions) then
        logInfo m!"Variable syntax found: '{user}'\n\
                   Variable syntax saved: '{cleanUpExplicitUniverses user}'"
      usedVarsRef.addDict uniq (cleanUpExplicitUniverses user)
  -- On all declarations that are not examples, we "rename" them, so that we can elaborate
  -- their syntax again, and we replace `:= proof-term` by `:= by included_variables plumb: sorry`
  -- in order to update the `usedVarsRef` counter.
  -- TODO: find a way to deal with proofs that use the equation compiler directly.
  if let some decl := stx.find? (#[``declaration, `lemma].contains <|·.getKind) then
    if decl.isOfKind `lemma || decl[1].isOfKind ``Command.theorem
    then
      let s ← get
      let toFalse := mkIdent `toFalse
      let toThm : Syntax := if decl.isOfKind `lemma then lemmaToThm decl else decl
      let renStx ← mkThm toThm
      let newRStx : Syntax := stx.replaceM (m := Id)
        (if · == decl then return some renStx else return none)
      elabCommand (← `(def $toFalse (S : Sort _) := False))
      try elabCommand newRStx
      catch _ => dbg_trace "caught something"
      set s
      return
    let usedVarNames := ← do
      if #[``Command.instance, ``definition, ``Command.structure, ``Command.abbrev].contains
        decl[1].getKind
      then getUsedVariableNames (decl.getPos?.getD default)
      else if decl[1].getKind == ``Command.example then
        let toDef := exampleToDef decl `newName
        let newRStx : Syntax := stx.replaceM (m := Id)
          (if · == decl then return some toDef else return none)
        elabCommand newRStx
        let cinfo := ((← getEnv).find? ((← getCurrNamespace) ++ `newName)).getD default
        let (d, _) ← liftCoreM do Meta.MetaM.run do getForallStrings cinfo.type
        if Linter.getLinterValue showDefs (← getOptions) then
          dbg_trace "getForallStrings: {d}"
        return d
      else return #[]
    -- Replace the declaration in the initial `stx` with the "revised" one.
    -- This handles `include h in` and other "`in`"s.
    let left2 := (← usedVarsRef.get).dict.toList
    let left := left2.map Prod.fst
    let _leftPretty := (left2.map Prod.snd).map fun l => l.prettyPrint.pretty
    let mut filt := []
    let mut filt2 := []
    -- used to test when the `for` loop below can be simplified
    --let cond := ← match stx with | `(variable $_* in $_) => return false | _ => return true
    for s in usedVarNames do
      filt2 := filt2 ++ left2.filter fun (_a, b) =>
        let new :=
          if _a.eraseMacroScopes.isAnonymous then
            s == b.prettyPrint.pretty.trim
          else
            s == _a.eraseMacroScopes.toString
        --if cond && new != (s == b.prettyPrint.pretty) then dbg_trace "error (variable in)!"; new else
        --if (!cond) && new == (s == b.prettyPrint.pretty) then dbg_trace "error (not variable in)!"; new else
        new

      filt := filt ++ left.filter (s.isPrefixOf ·.toString)
    for (s, _) in filt2 do
      usedVarsRef.addUsedVarName s

initialize addLinter unusedVariableCommandLinter

end UnusedVariableCommand

end Mathlib.Linter
