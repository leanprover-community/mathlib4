/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command

/-!
--import Mathlib.adomaniLeanUtils.inspect
#  The "unusedVariableCommand" linter

The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/

open Lean Parser Elab Command

namespace Lean.Syntax
/-!
# `Syntax` filters
-/

partial
def filterMapM {m : Type → Type} [Monad m] (stx : Syntax) (f : Syntax → m (Option Syntax)) :
    m (Array Syntax) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

def filterMap (stx : Syntax) (f : Syntax → Option Syntax) : Array Syntax :=
  stx.filterMapM (m := Id) f

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

namespace UnusedVariableCommand

/--
`usedVarsRef` collects the unique names of the variables that have been used somewhere
in its `NameSet` factor and the mapping from unique names to the `Syntax` node of the
corresponding variable in its second factor.

There is an exception, though: for variables introduced with `variable ... in`, the `Syntax`
node is the whole `variable` command.
-/
initialize usedVarsRef : IO.Ref (NameSet × NameMap Syntax) ← IO.mkRef ({}, {})

/-- returns the unique `Name`, the user `Name` and the `Expr` of each `variable` that is
present in the current context. -/
def includedVariables (plumb : Bool) : TermElabM (Array (Name × Name × Expr)) := do
  let c ← read
  let fvs := c.sectionFVars
  let mut varIds := #[]
  let lctx ← getLCtx
  for (a, b) in fvs do
    let ref ← getRef
    if (lctx.findFVar? b).isNone then
      usedVarsRef.modify fun (used, varsDict) =>
        (used, if varsDict.contains a then
          varsDict
        else
          varsDict.insert a (.ofRange (ref.getRange?.getD default)))
    if (lctx.findFVar? b).isSome then
      let mut fd := .anonymous
      for (x, y) in c.sectionVars do
        if y == a then fd := x
      varIds := varIds.push (a, fd, b)
      if plumb then
        usedVarsRef.modify fun (used, varsDict) => (used.insert a, varsDict)
  return varIds

/--
The tactic `included_variables` reports which variables are included in the current declaration.

The variant `included_variables plumb` is intended only for the internal use of the
unused variable command linter: besides printing the message, `plumb` also adds records that
the variables included in the current declaration really are included.
-/
elab "included_variables" plumb:(ppSpace &"plumb")? : tactic => do
    let (_plb, usedUserIds) := (← includedVariables plumb.isSome).unzip
    let msgs ← usedUserIds.mapM fun (userName, expr) =>
      return m!"'{userName}' of type '{← Meta.inferType expr}'"
    if ! msgs.isEmpty then
      logInfo m!"{msgs.foldl (m!"{·}\n" ++ m!"* {·}") "Included variables:"}"

abbrev binders : NameSet := NameSet.empty
  |>.insert ``Lean.Parser.Term.explicitBinder
  |>.insert ``Lean.Parser.Term.strictImplicitBinder
  |>.insert ``Lean.Parser.Term.implicitBinder
  |>.insert ``Lean.Parser.Term.instBinder

partial
def findBinders (stx : Syntax) : Array Syntax :=
  stx.filter (binders.contains ·.getKind)

def getExtendBinders {m} [Monad m] [MonadRef m] [MonadQuotation m] (stx : Syntax) : m (Array Syntax) := do
  if let some exts := stx.find? (·.isOfKind ``Lean.Parser.Command.extends) then
    let exts := exts[1].getArgs.filter (·.getAtomVal != ",")
    let exts ← exts.mapM (`(Lean.Parser.Term.instBinder| [$(⟨·⟩)]))
    return exts
  else return #[]

variable
  (nm : Ident)
  (binders : TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder])
  (typ : Syntax)
def mkThmCore : CommandElabM Syntax :=
  `(command| theorem $nm $binders* : $(⟨typ⟩) := by included_variables plumb; sorry)

def getPropValue {m} [Monad m] [MonadRef m] [MonadQuotation m] (stx : Syntax) : m Syntax := do
  let flse ← `($(mkIdent `False))
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.structure)).isSome then
    return flse
  --if (stx.find? (·.isOfKind ``Lean.Parser.Command.definition)).isSome then
  --  return ((stx.find? (·.isOfKind ``Lean.Parser.Term.typeSpec)).getD default)[1]
  if let some ts := stx.find? (·.isOfKind ``Parser.Term.typeSpec) then
    `($(mkIdent `toFalse) $(⟨ts[1]⟩))
  else
    return flse

def mkThmWithHyps (cmd : Syntax) (nm : Ident) : CommandElabM Syntax := do
  mkThmCore nm ((findBinders cmd).map (⟨·⟩)) (← getPropValue cmd)

def mkNewThm (cmd : Syntax) (typeSorry : Bool := False) : CommandElabM Syntax := do
  let exts ← getExtendBinders cmd
  let typ ← if typeSorry then do return (← `($(mkIdent `toFalse) sorry)).raw else getPropValue cmd
  mkThmCore (mkIdent `helr) ((findBinders cmd ++ exts).map (⟨·⟩)) typ

/-
  if let some stx := stx.raw.find? (·.isOfKind ``Lean.Parser.Command.declaration) then
    match stx with
      | `(structure $id $as* where $(_optStructCtor)? $_fds:structFields) =>
        -- the `fds` should be extracted and the target of the `structure.mk` should be used
        let new ←
          `(command| theorem $(mkIdent (id.raw[0].getId ++ `hi)) $as* : toFalse sorry := sorry)
        logInfo m!"{new}"
      --| `(structure $id $as* extends $es where $(opt)? $fds:structFields) => logInfo "found!"
      | `(structure $id $as* extends $es,* where $(_optStructCtor)? $_fds:structFields) =>
        dbg_trace "es.getElems: {es.getElems}\n"
        let bes ← es.getElems.mapM (`(Parser.Term.instBinder| [·]))
        let bes ← bes.mapM fun d => `(bracketedBinder| $(⟨d⟩))
        let cs := (as : Array _) ++ bes.map (·.raw)
        --let cs ← cs.mapM (`(⟨·⟩))
        let cs : TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder] :=
          cs.map (⟨·⟩)
        --let mut first : Array (TSyntax _):= as.getD 0 default
        --for b in bes do
          --first ← `(Term.App| $first $(⟨b.raw⟩))
        logInfo m!"bes: {bes}\n"
        --let bes1 : Syntax.TSepArray [bracketedBinder] "," := ⟨bes.map (·)⟩
        --logInfo m!"{bes1.getElems}"
        let new ←
          `(command| theorem $(mkIdent (id.raw[0].getId ++ `hi)) $cs* : toFalse sorry := sorry)
        logInfo m!"{new}"
      | _ => logInfo "here"

-/

open Lean.Parser.Term in
/--
Like `Lean.Elab.Command.getBracketedBinderIds`, but returns the identifier `Syntax`,
rather than the `Name`, in the given bracketed binder.
-/
def getBracketedBinderIds : Syntax → CommandElabM (Array Syntax)
  | `(bracketedBinderF|($ids* $[: $ty?]? $(_annot?)?)) => return ids
  | `(bracketedBinderF|{$ids* $[: $ty?]?})             => return ids
  | `(bracketedBinderF|⦃$ids* : $_⦄)                   => return ids
  | `(bracketedBinderF|[$id : $_])                     => return #[id]
  | `(bracketedBinderF|[$f])                           => return #[f]
  | _                                                  => throwUnsupportedSyntax

open Lean.Parser.Term in
/--
similar to `getBracketedBinderIds`, but replaces syntax representing a binder update with
`.missing` instead of the corresponding variable: a binder update does not count as a repetition.
-/
def getBracketedBinderIds' : Syntax → CommandElabM (Array Syntax)
  | `(bracketedBinderF|($ids* $[: $ty?]? $(_annot?)?)) =>
    return if ty?.isSome then ids else ids.map fun _ => .missing
  | `(bracketedBinderF|{$ids* $[: $ty?]?})             =>
    return if ty?.isSome then ids else ids.map fun _ => .missing
  | `(bracketedBinderF|⦃$ids* : $_⦄) => return ids
  | `(bracketedBinderF|[$id : $_]) => return #[id]
  | `(bracketedBinderF|[$_]) => return #[.missing]
  | _ => throwUnsupportedSyntax

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
      let (used, all) ← usedVarsRef.get
      let sorted := used.toArray.qsort (·.toString < ·.toString)
      let unused := all.toList.filter (!sorted.contains ·.1)
      for (uniq, user) in unused do
        match uniq.eraseMacroScopes with
          | .anonymous => Linter.logLint linter.unusedVariableCommand user m!"'{user}' is unused"
          | x          => Linter.logLint linter.unusedVariableCommand user m!"'{x}' is unused"
  -- if there is a `variable` command in `stx`, then we update `usedVarsRef` with all the
  -- information that is available
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.variable)).isSome then
    let scope ← getScope
    let pairs := scope.varUIds.zip (← scope.varDecls.mapM getBracketedBinderIds).flatten
    usedVarsRef.modify fun (used, varsDict) => Id.run do
      let mut newVarsDict := varsDict
      for (uniq, user) in pairs do
        newVarsDict := newVarsDict.insert uniq user
      (used, newVarsDict)
  -- on all declarations that are not examples, we "rename" them, so that we can elaborate
  -- their syntax again, and we replace `:= proof-term` by `:= by included_variables plumb: sorry`
  -- in order to update the `usedVarsRef` counter.
  -- TODO: find a way to deal with proofs that use the equation compiler directly.
  if let some decl := stx.find? (#[``declaration, `lemma].contains <|·.getKind) then
    -- skip examples, since they have access to all the variables
    if decl[1].isOfKind ``Lean.Parser.Command.example then
      return
    let _renStx ← stx.replaceM fun s => match s.getKind with
        | ``declId        => return some (← `(declId| $(mkIdentFrom s[0] (s[0].getId ++ `_hello))))
        | ``declValSimple | ``declValEqns | ``whereStructInst =>
          return some (← `(declValSimple| := by included_variables plumb; sorry))
        | _               => return none
    let toFalse := mkIdent `toFalse
    --let renStx ← renStx.replaceM fun s => match s with
    --    | `(def $d $vs* : $t := $pf) => return some (← `(theorem $d $vs* : $toFalse $t := $pf))
    --    | _               => return none
    let renStx ← mkNewThm decl
    let s ← get
    elabCommand (← `(def $toFalse (S : Sort _) := False))
    try
      elabCommand renStx
    catch _ =>
      elabCommand (← mkNewThm decl true)
    set s
    --logInfo renStx

initialize addLinter unusedVariableCommandLinter

end UnusedVariableCommand

/-- The "shadow" linter emits a warning when there are assumptions with repeated names. -/
register_option linter.shadow : Bool := {
  defValue := true
  descr := "enable the shadow linter"
}

--initialize allVarsRef : IO.Ref (Array Syntax) ← IO.mkRef #[]

/-- extracts the binder names of nested `forallE`s.  Should deal better with instances. -/
def getForAllBinderNames : Expr → Array Name
  | .forallE name _ rest _ => #[name] ++ getForAllBinderNames rest
  | _ => #[]

namespace Shadow

@[inherit_doc Mathlib.Linter.linter.shadow]
def shadowLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.shadow (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- on each variable command, we check if there are new, non-updated, binders that have the
  -- same name as binders that are already present and we flag them.
  if stx.isOfKind ``Command.variable then
    match stx with
      | `(variable $s*) =>
        let newVs := (← s.mapM UnusedVariableCommand.getBracketedBinderIds').flatten
        let sc := (← getScope).varDecls
        let sc := (← sc.mapM (getBracketedBinderIds ·.raw)).flatten
        let sc := sc.shrink (sc.size - newVs.size)
        for v in newVs do
          if (!v.getId.isAnonymous) && sc.contains v.getId then logInfoAt v m!"repeated variable '{v}'"
      | _ => return

  unless (stx.find? (#[``declaration, `lemma].contains <|·.getKind)).isSome do
    return
  let decl? := (stx.find? (·.isOfKind ``Lean.Parser.Command.declId)).getD default
  let decl := ((← getEnv).find? decl?[0].getId).getD default
  let type := decl.type
  --type.inspect
  let bindNames := getForAllBinderNames type
  let mut reps := #[]
  let mut seen : NameSet := {}
  for nm in bindNames do
    if seen.contains nm then reps := reps.push nm else seen := seen.insert nm
  if ! reps.isEmpty then
    Linter.logLint linter.shadow stx m!"Repeated binder names: {reps}"

initialize addLinter shadowLinter

end Shadow

end Mathlib.Linter
