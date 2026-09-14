/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import Lean.Elab.Command
public import Lean.Environment
public import Lean.Meta.Instances
public import Lean.ReducibilityAttrs
public import Lean.ProjFns
public import Lean.Meta.Match.MatcherInfo
public import Lean.Meta.Match.MatchPatternAttr
public import Batteries.Tactic.Lint.Basic
-- Import `Mathlib.Init`, not the header linter directly, to ensure that this
-- file has a valid copyright header and module docstring.
public import Mathlib.Init  -- shake: keep

/-!
# Superfluous-expose linter

This linter is the dual of `privateModule`. It reports each `@[expose] public
section` where no declaration benefits from exposure. It suggests that you
remove the `@[expose]` modifier. The removal hides the bodies of the section
and leaves downstream typechecking unchanged.

## What the section modifier controls

The `@[expose]` modifier of a section reaches the bodies of `def`
declarations only. Lean decides the rest:

* Lean exposes the body of an `abbrev` and the body of an `instance` of
  non-propositional type in every public section.
* Lean keeps the body of a theorem, of an `opaque` declaration, of a `partial
  def`, and of an `instance` of propositional type out of the public
  interface of every public section.
* An inductive type, a structure, a class, and the constructors,
  projections, recursors, matchers and other declarations that Lean
  generates for them, all follow the visibility of their declaration.

## Which defs need their body downstream

A `def` benefits from exposure when downstream typechecking or elaboration
reads its body. These benefit: a plain `def`, an `unsafe def` (downstream
`unsafe` code proves `rfl` facts that read it), an `@[irreducible]` def
(downstream code applies `rw` and `unfold`, which read the body), a
`@[reducible]` def (a hidden body breaks even the public `rfl` proofs of the
same file), and a `@[match_pattern]` def (pattern elaboration reads the
body).

A parser entry that `notation`, `infix`, `syntax`, or `macro` generates does
not benefit. Lean reads such a descriptor through its compiled code, which
stays outside the exposed part of the module.

The linter uses `Lean.Environment.isAutoDecl` to identify the declarations
that Lean generates, such as recursors, no-confusion lemmas and equation
lemmas, and skips them.

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
that the environment gained since the previous command. One declaration that
benefits from exposure settles the verdict of the region, and the scan stops
there.

The classification runs while the scopes of the command are still active.
`Lean.Meta.isInstanceCore` identifies a `scoped instance` or a `local
instance` only while its scope is active, so the classification must run here
rather than at the end of the file.

When a region closes and no declaration in it benefits from exposure, the
linter logs its warning at the recorded position of the section header. A
file with several expose sections gets one verdict per section.

The linter tracks regions and classifies declarations unconditionally. The
`linter.superfluousExpose` option gates only the report. Once a region holds
a def that benefits, it costs one scan of the local constants. A region
without such a def scans them once per command, until it closes.

The scope inspection is semantic, not syntactic. An `@[expose] section`
nested inside a `public section` reads the same as a literal
`@[expose] public section` header, because exposure reaches the declarations
of the inner section. A non-public `@[expose] section` reads as no region at
all: `@[expose]` acts on downstream visibility, and only a `public section`
has downstream visibility.

The linter is conservative. Every case below classifies a declaration as
one that benefits from exposure. Each therefore causes a false negative: the
linter stays silent on a section where the warning applies. That one
direction holds the guarantee that a reported section is safe to change. The
known cases are:

* Tactic-implementation defs. Declarations that come from `simproc_decl`,
  `elab`, `macro_rules`, or `scoped macro` count as ordinary defs that
  benefit from exposure. Thus a section with only such declarations gets no
  warning.
* Nested expose sections. An `@[expose] public section` inside another one
  extends the same region. The linter gives one verdict for the combined
  region and cannot report the inner, redundant modifier separately.
* `@[no_expose]` defs and `meta` defs. Lean keeps the body of either out of
  the public interface, but the linter still counts them as defs that
  benefit.
* Late attribute changes. The linter classifies a declaration at the command
  that creates it. A later `attribute` command, for example
  `attribute [instance] foo`, does not change the recorded verdict. The early
  verdict errs toward "benefits from exposure", so the linter stays silent.
* Macro-generated abbrevs. The abbrev exemption requires a visible `abbrev`
  command. An `abbrev` that a macro produces counts as a reducible def that
  benefits from exposure, so its section gets no warning.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The `superfluousExpose` linter detects each `@[expose] public section`
where no declaration benefits from exposure, that is, where no body must be
visible downstream. It suggests that you remove the `@[expose]` modifier. -/
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
`infix`, `syntax`, or `macro` generates. Two conditions hold together: the
leaf name starts with `term`, `binder`, `stx`, or `tactic`, and the return
type is one of the parser and macro descriptor types of Lean. A user def
that shares the prefix fails the second condition.

The prefix check is permissive: it tests for `term`, not `term_`, because the
shape of the leaf name depends on the syntax of the notation. The infix
`notation:65 a " ⋄ " b` generates `«term_⋄_»`, with an underscore for the
leading argument. The function-like `notation "F(" a ")"` generates
`«termF(_)»`, without an underscore separator. The return-type check does
the classification, and the prefix is only a cheap filter. -/
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

/-- The kind of the declaration that the command `stx` writes, for example
``Parser.Command.definition`` or ``Parser.Command.abbrev``. Returns
`Name.anonymous` for a command that writes no declaration, and for a
declaration that a macro produces. -/
private def declarationKind (stx : Syntax) : Name :=
  if stx.isOfKind ``Parser.Command.declaration then stx[1].getKind else .anonymous

/-- Returns `true` when the body of the constant is relevant to downstream
typechecking or to same-file public proofs. `declKind` is the kind that
`declarationKind` reports for the command that created the constant. Callers
must filter out `Lean.Environment.isAutoDecl` names first.

Callers must apply this check while the scopes of the declaring command are
still active: `Lean.Meta.isInstanceCore` sees a `scoped instance` or a
`local instance` only while its scope is active. -/
private def benefitsFromExposure (env : Environment) (name : Name)
    (info : ConstantInfo) (declKind : Name) : Bool :=
  if isPrivateName name then false else
  if looksLikeNotationDecl info name then false else
  if (env.getProjectionFnInfo? name).isSome then false else
  if Lean.Meta.isMatcherCore env name then false else
  match info with
  | .defnInfo _ =>
      -- Lean settles the exposure of an `instance` declaration in every
      -- public section: it exposes the body of one of non-propositional type
      -- and hides the body of one of propositional type. A `def` that carries
      -- `@[instance]` keeps the exposure rules of a `def`, so the command
      -- kind guards this exemption.
      if declKind != ``Parser.Command.definition && Lean.Meta.isInstanceCore env name then
        false
      -- Pattern-match elaboration reads the body of a `@[match_pattern]`
      -- def, even when the def is also `@[reducible]`. Example:
      --   @[match_pattern, reducible] def myPat : α ⊕ β := Sum.inl _
      --   -- Downstream, `match x with | myPat a => …` needs the body of `myPat`.
      else if Lean.hasMatchPatternAttribute env name then true
      else
        match Lean.getReducibilityStatusCore env name with
        -- Lean exposes the body of an `abbrev` in every public section. The
        -- section modifier does control the body of a hand-written
        -- `@[reducible] def`: hiding it breaks even same-file public `rfl`
        -- proofs.
        | .reducible => declKind != ``Parser.Command.abbrev
        -- A plain `def`, an `unsafe def`, an `@[irreducible] def`, an
        -- `irreducible_def`, and an `@[implicit_reducible]` def all need the
        -- body downstream. Even for `@[irreducible]`, downstream code applies
        -- `rw` or `unfold` to it.
        | _ => true
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
  when the current region opened. The linter state is shared between
  commands, so this must be a persistent set: an insert into a hash set
  would copy the whole table. -/
  seen : NameSet := {}
  /-- The open exposed region, if any. Regions cannot nest: an expose section
  inside an active region extends the same region. -/
  region? : Option ExposeRegion := none

instance : Inhabited ExposeSectionState := ⟨{}⟩

/-- Logs the warning for a closed region, at the position of its section
header. Stays silent when a declaration of the region benefits from
exposure, or when the `linter.superfluousExpose` option is off. -/
private def reportRegion (r : ExposeRegion) : CommandElabM Unit := do
  if r.someDeclBenefits then return
  unless getLinterValue linter.superfluousExpose (← getLinterOptions) do return
  let ref := Syntax.atom (.synthetic r.pos r.pos) ""
  logLint linter.superfluousExpose ref
    "This `@[expose] public section` contains no declaration that benefits \
    from exposure. You can safely remove the `@[expose]` modifier: it \
    only changes the bodies of `def` declarations, and no `def` here needs \
    its body downstream."

/--
The `superfluousExpose` linter detects each `@[expose] public section` where
no declaration benefits from exposure.

After each command, the linter tracks the current exposed region and
classifies the declarations that the command created. A region closes at its
`end` command, or at the terminal command for a section that the end of the
file closes. The linter then reports the region if no declaration in it
benefits from exposure, and points the warning at the section header.
-/
public initialize superfluousExpose : StatefulLinter ExposeSectionState Unit ←
  registerStatefulLinter {}
    (post := fun stx self _ _ _ => do
      let env ← getEnv
      -- Only module files can contain `public section`s.
      if !env.header.isModule then return self
      -- Classify the declarations that appeared since the previous command.
      -- The verdict of a region cannot change once one declaration benefits,
      -- so the scan stops there.
      let mut st := self
      if let some r := st.region? then
        unless r.someDeclBenefits do
          let declKind := declarationKind stx
          let mut seen := st.seen
          let mut benefits := false
          for (n, info) in env.constants.map₂ do
            unless seen.contains n do
              seen := seen.insert n
              unless benefits || env.isAutoDecl n do
                benefits := benefitsFromExposure env n info declKind
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
        -- The region closes at this command.
        reportRegion r
        return { st with region? := none }
      -- No region and none opens, or the open region continues.
      | _, _ => return st)

end Mathlib.Linter
