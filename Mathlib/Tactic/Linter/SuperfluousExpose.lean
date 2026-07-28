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

This linter is the dual of `privateModule`. It reports each `@[expose] public
section` that contains no declaration whose body must be visible downstream.
It suggests that you remove the `@[expose]` modifier. The removal changes the
section default from exposed bodies to hidden bodies, and it does not change
downstream typechecking.

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
so it keeps state across the commands of a module. It tracks regions: a
region is a maximal run of commands whose scope is public and carries the
`expose` attribute. Nested scopes inherit `Scope.isPublic` and `Scope.attrs`,
so one check of the top scope after each command finds these regions. A
region opens when the predicate becomes true, and the linter records the
position of the command that opened it (the section header). A region closes
when the predicate becomes false (an `end` command), or at the terminal
command for a section that the end of the file closes.

After each command inside a region, the linter classifies the declarations
that appeared in the environment since the previous command, and it folds the
verdicts into one flag: does some declaration of the region benefit from
exposure? The classification runs while the scopes of the command are still
active. Thus `Lean.Meta.isInstanceCore` also identifies `scoped instance` and
`local instance` declarations, which an end-of-file check would misclassify
as plain defs.

When a region closes and no declaration in it benefits from exposure, the
linter logs its warning at the recorded position of the section header. A
file with several expose sections gets one verdict per section.

The linter tracks regions and classifies declarations unconditionally; the
`linter.superfluousExpose` option gates only the report. The tracking cost is
one pass over the local constants per command inside a region, and the
classification of each constant runs once.

The scope inspection is semantic, not syntactic. The linter detects an
`@[expose] section` nested inside a `public section` in the same way as a
literal `@[expose] public section` header, because exposure applies to the
declarations of the inner section. The linter does not detect a non-public
`@[expose] section`: `@[expose]` only affects downstream visibility, and only
a `public section` has downstream visibility.

The linter is conservative. Each known limitation causes a false negative:
the linter stays silent on a section where the warning applies. No limitation
causes a false positive. The known cases are:

* Tactic-implementation defs. Declarations that come from `simproc_decl`,
  `elab`, `macro_rules`, or `scoped macro` count as ordinary defs that
  benefit from exposure. Thus a section with only such declarations gets no
  warning.
* Nested expose sections. An `@[expose] public section` inside another one
  extends the same region. The linter gives one verdict for the combined
  region and cannot report the inner, redundant modifier separately.
* Late attribute changes. The linter classifies a declaration at the command
  that creates it. A later `attribute` command, for example
  `attribute [reducible] foo`, does not change the recorded verdict. The
  early verdict errs toward "benefits from exposure", so the linter stays
  silent.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The `superfluousExpose` linter detects each `@[expose] public section`
where no declaration needs its body visible downstream. It suggests that you
remove the `@[expose]` modifier. -/
public register_option linter.superfluousExpose : Bool := {
  defValue := false
  descr := "Enable the `superfluousExpose` linter, which detects sections \
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
names first.

Callers must apply this check while the scopes of the declaring command are
still active: `Lean.Meta.isInstanceCore` sees a `scoped instance` or a
`local instance` only while its scope is active. -/
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

/-- An open exposed region: a run of commands whose scope is public and
carries `@[expose]`. -/
public structure ExposeRegion where
  /-- Position of the command that opened the region (the section header).
  The warning ref points here. -/
  pos : String.Pos.Raw
  /-- `true` when some declaration created inside the region benefits from
  exposure. -/
  someDeclBenefits : Bool := false

/-- The persistent state of the `superfluousExpose` linter: the constants
classified so far, and the open region, if any. -/
public structure ExposeSectionState where
  /-- Constants of the module that the linter has classified, or that existed
  when the current region opened. -/
  seen : NameSet := {}
  /-- The open exposed region, if any. Regions cannot nest: an expose section
  inside an active region extends the same region. -/
  region? : Option ExposeRegion := none

instance : Inhabited ExposeSectionState := ⟨{}⟩

/-- Reports a closed region: logs the lint warning at the position of the
section header, unless some declaration of the region benefits from exposure
or the `linter.superfluousExpose` option is off. -/
private def reportRegion (r : ExposeRegion) : CommandElabM Unit := do
  if r.someDeclBenefits then return
  unless getLinterValue linter.superfluousExpose (← getLinterOptions) do return
  let ref := Syntax.atom (.synthetic r.pos r.pos) ""
  logLint linter.superfluousExpose ref
    "This `@[expose] public section` contains no declaration that benefits \
    from body exposure. You can safely remove the `@[expose]` modifier: it \
    only affects `def` and `inductive` bodies, and no declaration here needs \
    exposure (only theorems, instances, classes, structures, abbrevs, \
    notation, or auto-generated declarations)."

/--
The `superfluousExpose` linter detects each `@[expose] public section` where
no declaration needs its body exposed downstream. It suggests that you remove
the `@[expose]` modifier.

After each command, the linter tracks the current exposed region and
classifies the declarations that the command created. When a region closes —
at its `end` command, or at the terminal command for a section that the end
of the file closes — the linter reports the region if no declaration in it
benefits from exposure. The warning points at the section header.
-/
public initialize superfluousExpose : StatefulLinter ExposeSectionState Unit ←
  registerStatefulLinter {}
    (post := fun stx self _ _ _ => do
      let env ← getEnv
      if !env.header.isModule then return self
      -- Classify the declarations that appeared since the previous command.
      let mut st := self
      if let some r := st.region? then
        let mut seen := st.seen
        let mut benefits := r.someDeclBenefits
        for (n, info) in env.constants.map₂ do
          unless seen.contains n do
            seen := seen.insert n
            unless benefits do
              unless ← liftCoreM (Batteries.Tactic.Lint.isAutoDecl n) do
                benefits := benefitsFromExposure env n info
        st := { seen, region? := some { r with someDeclBenefits := benefits } }
      if Parser.isTerminalCommand stx then
        -- The end of the file closes an open section.
        if let some r := st.region? then reportRegion r
        return { st with region? := none }
      let sc ← getScope
      let exposedNow := sc.isPublic && sc.attrs.any isExposeAttrInstance
      match st.region?, exposedNow with
      | none, true =>
        -- The region opens at this command. Snapshot the current constants:
        -- declarations from before the region do not count.
        let mut seen : NameSet := {}
        for (n, _) in env.constants.map₂ do
          seen := seen.insert n
        return { seen, region? := some { pos := stx.getPos?.getD ⟨0⟩ } }
      | some r, false =>
        reportRegion r
        return { st with region? := none }
      | _, _ => return st)

end Mathlib.Linter
