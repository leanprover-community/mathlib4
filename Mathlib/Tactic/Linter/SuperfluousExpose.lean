/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import Lean.Elab.Command
public import Lean.Environment
public import Lean.Class
public import Lean.Structure
public import Lean.Meta.Instances
public import Lean.ReducibilityAttrs
public import Lean.ProjFns
public import Lean.Meta.Match.MatcherInfo
public import Lean.Meta.Match.MatchPatternAttr
public import Batteries.Tactic.Lint.Basic
-- Import `Mathlib.Init`, not the header linter directly, to ensure that this
-- file has a valid copyright header and module docstring. The import-linter
-- requires that a module outside the closure of `Mathlib.Init` imports
-- `Mathlib.Init`.
public import Mathlib.Init  -- shake: keep

/-!
# Superfluous-expose linter

This linter is the dual of `privateModule`. It reports a module that has an
`@[expose] public section` but no declaration whose body must be visible
downstream. It suggests that you remove the `@[expose]` modifier. The removal
changes the file default from exposed bodies to hidden bodies, and it does
not change downstream typechecking.

A declaration benefits from exposure when its body matters to downstream
proofs or elaboration. These benefit: plain `def`, plain `inductive`,
`@[match_pattern]` def, `@[irreducible]` def (downstream `rw` and `unfold`
still need the body), and `@[to_additive]` def. These do not benefit:
theorems, abbrevs, classes, structures, instances, `unsafe` and `partial`
defs, projections, matchers, and parser entries that come from notation. The
linter uses `Batteries.Tactic.Lint.isAutoDecl` to identify compiler-generated
declarations, such as recursors, no-confusion lemmas, and equation lemmas,
and skips them.

## Implementation notes

The linter is a stateful linter (`Lean.Elab.Command.registerStatefulLinter`),
so it keeps state across the commands of a module. After each command, the
linter inspects the current `Scope`. Nested scopes inherit `Scope.isPublic`
and `Scope.attrs`. Thus a command is under an explicit or inherited
`@[expose] public section` exactly when its scope is public and carries the
`expose` attribute. The linter records this fact in its state. The terminal
command (`Parser.Command.eoi` or `#exit`) has access to the full elaborated
environment, but every section scope is already closed there. Thus, at the
terminal command, the linter reads the recorded flag, walks
`env.constants.map₂` to enumerate the locally-defined constants, and fires
unless some declaration benefits from exposure.

The scope inspection is semantic, not syntactic. The linter detects an
`@[expose] section` nested inside a `public section` in the same way as a
literal `@[expose] public section` header, because exposure applies to the
declarations of the inner section. The linter does not detect a non-public
`@[expose] section`: `@[expose]` only affects downstream visibility, and only
a `public section` has downstream visibility.

The linter is conservative. Each known limitation causes a false negative:
the linter stays silent on a file where the warning applies. No limitation
causes a false positive. The known cases are:

* File-level granularity. Suppose a file has several `@[expose] public
  section`s and only some of them are needed. If any declaration in the file
  benefits from exposure, the linter stays silent, and it does not find the
  superfluous `@[expose]` on the other sections.
* Tactic-implementation defs. Declarations that come from `simproc_decl`,
  `elab`, `macro_rules`, or `scoped macro` count as ordinary defs that
  benefit from exposure. Thus a file with only such declarations gets no
  warning.
* Scoped and local instances. `Lean.Meta.isInstanceCore` catches global
  instances but misses `scoped instance` and `local instance`. In the
  environment, these look identical to `@[implicit_reducible] def` shortcuts
  that are not instances and whose bodies do need exposure. The linter does
  not try to tell them apart. Thus a file with only scoped or local
  instances gets no warning.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The `superfluousExpose` linter detects a module with `@[expose] public
section` where no declaration needs its body visible downstream. It suggests
that you remove the `@[expose]` modifier. -/
public register_option linter.superfluousExpose : Bool := {
  defValue := false
  descr := "Enable the `superfluousExpose` linter, which detects modules \
    where `@[expose] public section` is superfluous."
}

/-- Returns `true` when the return type of `info` has the head constant
`name`. The return type is the codomain after removal of all `∀` and `→`
binders. -/
private def returnTypeHeadIs (info : ConstantInfo) (name : Name) : Bool :=
  match info.type.getForallBody.getAppFn with
  | .const n _ => n == name
  | _ => false

/-- Returns `true` when the def looks like a parser entry that `notation`,
`infix`, `syntax`, or `macro` generates. Two conditions must both hold: the
leaf name starts with `term`, `binder`, `stx`, or `tactic`, and the return
type is one of the parser and macro descriptor types of Lean. The conjunction
avoids false positives on user defs that share the prefix.

The prefix check is permissive: it tests for `term`, not `term_`, because the
shape of the leaf name depends on the syntax of the notation. The infix
`notation:65 a " ⋄ " b` generates `«term_⋄_»`, with an underscore for the
leading argument. The function-like `notation "F(" a ")"` generates
`«termF(_)»`, without an underscore separator. The return-type check does the
real classification. The prefix is only a cheap filter. -/
private def looksLikeNotationDecl (info : ConstantInfo) (name : Name) : Bool :=
  let nameMatches := match name with
    | .str _ s => s.startsWith "term" || s.startsWith "binder" ||
                  s.startsWith "stx" || s.startsWith "tactic"
    | _ => false
  let typeMatches :=
    returnTypeHeadIs info ``Lean.ParserDescr ||
    returnTypeHeadIs info ``Lean.TrailingParserDescr ||
    returnTypeHeadIs info ``Lean.Macro
  nameMatches && typeMatches

/-- Returns `true` when the body of the constant is relevant to downstream
typechecking. Callers must filter out `Batteries.Tactic.Lint.isAutoDecl`
names first. -/
private def benefitsFromExposure (env : Environment) (name : Name)
    (info : ConstantInfo) : Bool :=
  if isPrivateName name then false else
  if looksLikeNotationDecl info name then false else
  if (env.getProjectionFnInfo? name).isSome then false else
  if Lean.Meta.isMatcherCore env name then false else
  match info with
  | .defnInfo dv =>
      if Lean.Meta.isInstanceCore env name then false
      else if dv.safety != .safe then false   -- `unsafe def` or `partial def`
      -- `@[match_pattern]` needs the body for pattern-match elaboration,
      -- even when the def is `@[reducible]`. Example:
      --   @[match_pattern, reducible] def myPat : α ⊕ β := Sum.inl _
      --   -- Downstream, `match x with | myPat a => …` needs the body of `myPat`.
      else if Lean.hasMatchPatternAttribute env name then true
      else
        match Lean.getReducibilityStatusCore env name with
        -- Modules expose `abbrev` bodies by default, with or without `@[expose]`.
        | .reducible => false
        -- Plain `def`, `@[irreducible] def`, `irreducible_def`, and
        -- `@[implicit_reducible]` all need the body downstream. `@[irreducible]`
        -- does not help: downstream code can still apply `rw` or `unfold`
        -- explicitly. Example:
        --   irreducible_def myConst : Nat := 42
        --   -- Downstream, `theorem … := by rw [myConst]` needs the body of `myConst`.
        | _ => true
  | .inductInfo _ =>
      -- A plain inductive benefits: it serves pattern matching and recursor
      -- calls. Structures and classes go through auto-generated projections.
      !Lean.isStructure env name
  | _ => false

/-- Returns `true` when the attribute instance is `expose`. `elabSection`
builds scope attributes by quotation, so the ident carries macro scopes. The
comparison must first erase the macro scopes. -/
private def isExposeAttrInstance (ai : TSyntax ``Parser.Term.attrInstance) : Bool :=
  let attr := ai.raw[1]
  attr.isOfKind ``Parser.Attr.simple && attr[0].getId.eraseMacroScopes == `expose

/-- The persistent state of the `superfluousExpose` linter. It records whether
some command of the current module was inside an `@[expose] public section`
scope. -/
public structure ExposeSectionState where
  /-- `true` when some previous command was in a public scope that carries
  `@[expose]`. -/
  hasExposeSection : Bool := false
deriving Inhabited

/-- The end-of-module check of the `superfluousExpose` linter. It walks the
elaborated environment and logs the lint warning, unless some declaration
benefits from body exposure. Callers must check the `linter.superfluousExpose`
option. Callers must also check that the module has an `@[expose] public
section`. -/
def superfluousExposeCheck : CommandElabM Unit := do
  let env ← getEnv
  if !env.header.isModule then return
  if env.constants.map₂.isEmpty then return
  for (decl, info) in env.constants.map₂ do
    if ← liftCoreM (Batteries.Tactic.Lint.isAutoDecl decl) then continue
    if benefitsFromExposure env decl info then return
  let topOfFileRef := Syntax.atom (.synthetic ⟨0⟩ ⟨0⟩) ""
  logLint linter.superfluousExpose topOfFileRef
    "This module has `@[expose] public section` but no declaration that \
    would benefit from body exposure. The `@[expose]` modifier can be \
    safely removed: it would only affect `def`/`inductive` bodies, and \
    there are none here that need exposure (only theorems, instances, \
    classes/structures, abbrevs, notation, or auto-generated decls)."

/--
The `superfluousExpose` linter detects a module with `@[expose] public
section` where no declaration needs its body exposed downstream. It suggests
that you remove the `@[expose]` modifier.

After each command, the linter records in its state whether the scope of the
command is public and carries `@[expose]`. At the terminal command, it reads
the flag and runs `superfluousExposeCheck`. It logs its message at the top of
the file.
-/
public initialize superfluousExpose : StatefulLinter ExposeSectionState Unit ←
  registerStatefulLinter {}
    (post := fun stx self _ _ _ => do
      if Parser.isTerminalCommand stx then
        if self.hasExposeSection then
          if getLinterValue linter.superfluousExpose (← getLinterOptions) then
            superfluousExposeCheck
        return self
      else if self.hasExposeSection then
        return self
      else
        let sc ← getScope
        return { hasExposeSection := sc.isPublic && sc.attrs.any isExposeAttrInstance })

end Mathlib.Linter
