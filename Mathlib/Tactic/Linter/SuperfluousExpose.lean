/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import Lean.Elab.Command
public import Lean.Environment
public import Lean.Meta.Instances
public import Lean.ProjFns
public import Batteries.Tactic.Lint.Basic
-- Import `Mathlib.Init`, not the header linter directly, to ensure that this
-- file has a valid copyright header and module docstring.
public import Mathlib.Init  -- shake: keep

/-!
# Superfluous-expose linter

This linter is the dual of `privateModule`. It reports each `@[expose] public section` where no
declaration benefits from exposure, and it suggests that you remove the `@[expose]` modifier.
Downstream code typechecks the same after the removal. When the section holds an `@[no_expose]`
def, Lean reports that attribute as redundant after the removal, so remove it as well.

## What the section modifier controls

The `@[expose]` modifier of a section exposes the bodies of the `def` declarations of the section.
Lean settles the exposure of every other body without the modifier:

* Lean exposes the body of an `abbrev`, of an `instance` of non-propositional type, and of a
  structure projection in every public section.
* Lean hides the body of a theorem, of an `opaque` or `partial def`, of a private declaration, and
  of an `instance` of propositional type in every public section.
* Lean also hides the body of an `@[no_expose] def`, of a `meta def` outside a `meta` section, and
  of the parser descriptor that `notation` or `syntax` generates.
* An inductive type, its constructors and its recursors have no body.

A `def` that carries the `@[instance]` attribute is a `def`: the modifier controls its body.

## Classification

A declaration benefits from exposure when two conditions hold: its body is exposed when the
linter sees it (`Lean.Environment.hasExposedBody`), and Lean would hide that body without the
section modifier. The second condition fails for an `abbrev`, for an `instance`, and for a
structure projection. The linter also skips the declarations that Lean generates
(`Lean.Environment.isAutoDecl`), such as recursors, matchers and equation lemmas.

Every other exposed `def` counts as one that benefits. The linter stays silent when in doubt, so
a reported section is safe to change. A wrong report means that one exemption in
`benefitsFromExposure`, or the auto-declaration filter, is too broad.

## Implementation notes

The linter is a stateful linter (`Lean.Elab.Command.registerStatefulLinter`) and keeps state
across the commands of a module. It tracks regions: a region is a maximal run of commands whose
scope is public and carries the `expose` attribute. Nested scopes inherit `Scope.isPublic` and
`Scope.attrs`, so one check of the top scope after each command finds these regions, including
an `@[expose] section` nested inside a `public section`. A region opens at the command that makes
the predicate true, which is the section header. It closes at the command that makes the
predicate false, which is an `end`, or at the terminal command when the end of the file closes
the section.

After each command inside a region, the linter classifies the constants that the command added to
the environment. The classification runs while the scopes of the command are active, because
`Lean.Meta.isInstanceCore` sees a `scoped instance` or a `local instance` only then. It also reads
the kind of the command, for the `abbrev` and `instance` exemptions. One constant that benefits
settles the verdict of the region, and the scan stops.

When a region closes and no constant in it benefits, the linter reports the region at its section
header. A file with several expose sections gets one verdict per section. The
`linter.superfluousExpose` option gates the report only.

## Known false negatives

Each case below makes the linter count a declaration as one that benefits, so the linter stays
silent on a section where the warning applies:

* Meta-code defs, for example a hand-written `def` of type `Simproc` or `TacticM Unit`. Lean runs
  such a def through its compiled code, but the modifier does expose its body.
* Nested expose sections. An `@[expose] public section` inside another one extends the same
  region, so the linter cannot report the inner, redundant modifier separately.
* Late attribute changes. The linter classifies a constant at the command that creates it. A later
  `attribute [instance] foo` does not change the recorded verdict.
* Declarations behind a macro or in a `mutual` block. The kind of such a command is not that of an
  `abbrev` or `instance` command, so neither exemption applies to the constants it creates.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The `superfluousExpose` linter detects each `@[expose] public section` where no declaration
benefits from exposure, that is, where no body must be visible downstream. It suggests that you
remove the `@[expose]` modifier. -/
public register_option linter.superfluousExpose : Bool := {
  defValue := false
  descr := "Enable the `superfluousExpose` linter, which detects sections \
    where `@[expose] public section` is superfluous."
}

/-- The kind of the command `stx`, seen through `set_option … in`, `open … in` and similar
wrappers. For a declaration, this is the kind of the declaration itself, for example
``Parser.Command.abbrev`` or ``Parser.Command.instance``. -/
private partial def commandKind (stx : Syntax) : Name :=
  if stx.isOfKind ``Parser.Command.in then commandKind stx[2]
  else if stx.isOfKind ``Parser.Command.declaration then stx[1].getKind
  else stx.getKind

/-- The commands that declare instances through the `instance` elaborator: the `instance` command,
the `deriving instance` command, and the `inductive`, `class inductive` and `structure`
declarations, whose `deriving` clauses produce instances. Lean exposes the body of such an
instance in every public section. -/
private def instanceCommandKinds : List Name :=
  [``Parser.Command.instance, ``Parser.Command.deriving, ``Parser.Command.inductive,
    ``Parser.Command.classInductive, ``Parser.Command.structure]

/-- Returns `true` when the body of the constant `name` is exposed and Lean would hide it without
the section modifier. `cmdKind` is the kind that `commandKind` reports for the command that created
the constant. Callers filter out `Lean.Environment.isAutoDecl` names first, and apply this while
the scopes of the creating command are active.

The conjuncts after the first two each cover one case in which Lean exposes a body in every
public section, with or without the modifier. -/
private def benefitsFromExposure (env : Environment) (name : Name) (info : ConstantInfo)
    (cmdKind : Name) : Bool :=
  -- Only a `def` has a body that the modifier can expose.
  info matches .defnInfo _
  -- A body that is hidden now stays hidden without the modifier.
  && env.hasExposedBody name
  -- An `abbrev`.
  && cmdKind != ``Parser.Command.abbrev
  -- An `instance`. `Lean.Meta.isInstanceCore` also accepts a `def` that carries `@[instance]`,
  -- whose body the modifier controls, so the command kind must confirm an `instance` declaration.
  && !(cmdKind ∈ instanceCommandKinds && Lean.Meta.isInstanceCore env name)
  -- A structure projection.
  && (env.getProjectionFnInfo? name).isNone

/-- An open exposed region: a maximal run of commands whose scope is public and carries
`@[expose]`. -/
public structure ExposeRegion where
  /-- The command that opened the region, that is, the section header. The warning points at it. -/
  ref : Syntax
  /-- The constants that existed when the region opened, plus the constants classified since. The
  constants outside this set are the ones that the current command added. This is a persistent
  set because the linter framework keeps the previous state alive, so every insert must share
  structure with it. -/
  seen : NameSet
  /-- `true` once a constant of the region benefits from exposure. The verdict is then settled,
  and the linter stops classifying. -/
  someDeclBenefits : Bool := false

/-- Opens a region at the command `stx`. The constants that exist at this point lie outside the
region. -/
private def ExposeRegion.open (env : Environment) (stx : Syntax) : ExposeRegion :=
  { ref := stx, seen := env.constants.map₂.foldl (fun seen n _ => seen.insert n) {} }

/-- Classifies the constants that the command `stx` added to the environment, and settles the
verdict at the first one that benefits from exposure. -/
private def ExposeRegion.classifyNew (r : ExposeRegion) (env : Environment) (stx : Syntax) :
    ExposeRegion := Id.run do
  if r.someDeclBenefits then return r
  let cmdKind := commandKind stx
  let mut seen := r.seen
  for (n, info) in env.constants.map₂ do
    unless seen.contains n do
      if !env.isAutoDecl n && benefitsFromExposure env n info cmdKind then
        return { r with someDeclBenefits := true }
      seen := seen.insert n
  return { r with seen }

/-- Logs the warning for a closed region at its section header. Stays silent when a constant of
the region benefits from exposure, or when the `linter.superfluousExpose` option is off. -/
private def ExposeRegion.report (r : ExposeRegion) : CommandElabM Unit := do
  if r.someDeclBenefits then return
  unless getLinterValue linter.superfluousExpose (← getLinterOptions) do return
  logLint linter.superfluousExpose r.ref
    "This `@[expose] public section` contains no declaration that benefits \
    from exposure. You can safely remove the `@[expose]` modifier: it \
    only changes the bodies of `def` declarations, and no `def` here needs \
    its body downstream."

/--
The `superfluousExpose` linter detects each `@[expose] public section` where no declaration
benefits from exposure. It tracks the open exposed region across commands and reports it at its
section header when the region closes. The module docstring describes the classification.
-/
public initialize superfluousExpose : StatefulLinter (Option ExposeRegion) Unit ←
  registerStatefulLinter none
    (post := fun stx region? _ _ _ => do
      let env ← getEnv
      -- Only a module file has `public section`s.
      unless env.header.isModule do return none
      let region? := region?.map (·.classifyNew env stx)
      if Parser.isTerminalCommand stx then
        -- The end of the file closes an open section.
        if let some r := region? then r.report
        return none
      let sc ← getScope
      let exposedNow := sc.isPublic && sc.attrs.any (· matches `(Parser.Term.attrInstance| expose))
      match region?, exposedNow with
      | none, true => return some (.open env stx)
      | some r, false => r.report; return none
      | _, _ => return region?)

end Mathlib.Linter
