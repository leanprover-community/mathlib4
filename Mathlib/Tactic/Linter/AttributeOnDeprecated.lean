/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# The `attributeOnDeprecated` linter

The `attributeOnDeprecated` linter flags `attribute [...] foo` commands whose target `foo` is
deprecated.

Unlike uses of `foo` in terms, the `attribute` command does not trigger a deprecation warning.
However, once `foo` is removed, for instance by the `remove_deprecated_decls` automation,
the `attribute` command referring to it stops working.

`attribute [deprecated ...] foo` commands are ignored, since they are what makes `foo` deprecated.

## Implementation notes

The linter first inspects the syntax kind of the command (and of the commands chained with `in`),
so that it exits essentially immediately on commands that are not `attribute` commands.

The identifiers are resolved by looking up the constants that the `attribute` command recorded in
the info trees, so that `open ... in` and the current namespaces are taken into account.
When traversing the info trees, the linter skips the subtrees whose syntax lies outside of the
`attribute` command: in `attribute [...] foo in theorem bar ...`, this avoids inspecting the info
trees of `bar`.

## TODO

The `attribute` command is not the only place where a deprecated declaration can be referenced
without triggering a deprecation warning.
The following references also do not warn, and break once the deprecated declaration is removed.
* `open A (foo)`, `open A hiding foo`, `open A renaming foo → bar` and `export A (foo)`.
  These are commands and the info trees record the resolved names, so the linter could handle them
  with the same early exit and the same info tree traversal.
* `alias bar := foo`, where `foo` is deprecated and `bar` is not: the `alias` command does not
  check its target.
  As for `open`, the linter could handle this with the same early exit and info tree traversal.
* Declarations named in attribute arguments, such as `@[inherit_doc foo]`, and possibly
  `to_additive existing` and `to_dual existing` (untested).
  Handling these requires inspecting the attributes of every declaration, so the early exit would
  not be as quick.
* Name literals ``` ``foo ``` in meta code.
  Finding these requires traversing the syntax of every command, so they are probably better
  handled upstream, by having the name literal elaborator check for deprecations.
* The `delta foo` tactic, which is rare in Mathlib.

Ideally, all of these would be fixed upstream, by checking for deprecations when resolving the
names.
-/

meta section

open Lean Elab Linter

namespace Mathlib.Linter

/-- The `attributeOnDeprecated` linter flags `attribute [...] foo` commands whose target `foo` is
deprecated. -/
public register_option linter.attributeOnDeprecated : Bool := {
  defValue := false
  descr := "enable the `attributeOnDeprecated` linter"
}

namespace AttributeOnDeprecated

/--
`attributeCmds stx` returns the `attribute [...] ids` commands in `stx`, looking through the
commands chained with `in`, but no further.

It only inspects syntax kinds, so it returns `#[]` essentially immediately on most commands.
-/
partial def attributeCmds (stx : Syntax) : Array Syntax :=
  if stx.isOfKind ``Lean.Parser.Command.attribute then #[stx]
  else if stx.isOfKind ``Lean.Parser.Command.in then attributeCmds stx[0] ++ attributeCmds stx[2]
  else #[]

/--
`deprecatedTargets env rg targets t acc` pushes to `acc` the pairs `(id, n)`, where `id` is
one of the identifiers in `targets`, and `n` is a deprecated declaration that the info tree `t`
records at `id`.

The identifiers in `targets` lie in the range `rg`, and the subtrees of `t` whose syntax lies
outside of `rg` are skipped.
-/
partial def deprecatedTargets (env : Environment) (rg : Syntax.Range) (targets : Array Syntax) :
    InfoTree → Array (Syntax × Name) → Array (Syntax × Name)
  | .context _ t, acc => deprecatedTargets env rg targets t acc
  | .hole _, acc => acc
  | .node i cs, acc => Id.run do
    if let some r := i.stx.getRange? then
      if r.stop ≤ rg.start || rg.stop ≤ r.start then return acc
    let mut acc := acc
    if let .ofTermInfo { expr := .const n _, stx, .. } := i then
      if let some id := targets.find? (·.getRange? == stx.getRange?) then
        if Linter.isDeprecated env n then
          acc := acc.push (id, n)
    return cs.foldl (init := acc) fun acc t => deprecatedTargets env rg targets t acc

@[inherit_doc Mathlib.Linter.linter.attributeOnDeprecated]
def attributeOnDeprecatedLinter : Linter where run stx := do
  let attrs := attributeCmds stx
  if attrs.isEmpty then
    return
  withSetOptionIn (fun _ => do
    unless getLinterValue linter.attributeOnDeprecated (← getLinterOptions) do
      return
    let env ← getEnv
    let trees ← getInfoTrees
    for attr in attrs do
      -- `attribute [deprecated ...] foo` is what makes `foo` deprecated.
      if attr[2].getSepArgs.any (·[1].isOfKind ``Lean.deprecated) then
        continue
      let some rg := attr.getRange? | continue
      let targets := attr[4].getArgs
      let found := trees.foldl (init := #[]) fun acc t => deprecatedTargets env rg targets t acc
      for (id, n) in found do
        let breaks := m!"this `attribute` command will break when `{.ofConstName n}` is removed."
        let consider :=
          m!"Consider adding the attribute directly to the declaration of `{.ofConstName n}`"
        let msg ← match Linter.deprecatedAttr.getParam? env n with
          | some { newName? := some new, .. } => do
            -- If the deprecated name is fully qualified, then so is the suggested replacement.
            let fullNames := id.getId.eraseMacroScopes == privateToUserName n
            let hint ← Command.liftCoreM do
              MessageData.hint "Replace the deprecated name:"
                #[(← unresolveNameGlobal new (fullNames := fullNames)).toString] (ref? := id)
            pure <| m!"`{.ofConstName n}` has been deprecated in favor of \
              `{.ofConstName new}`: {breaks}\n\
              {consider}, applying it to `{.ofConstName new}` instead, or removing it." ++ hint
          | _ =>
            pure m!"`{.ofConstName n}` has been deprecated: {breaks}\n{consider} or removing it."
        logLint linter.attributeOnDeprecated id msg) stx

initialize addLinter attributeOnDeprecatedLinter

end AttributeOnDeprecated

end Mathlib.Linter
