/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jeremy Tan, Adomas Baliuka
-/

import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# Linter against deprecated syntax

`refine'` and `cases'` provide backward-compatible implementations of their unprimed equivalents
in Lean 3, `refine` and `cases`. They have been superseded by Lean 4 tactics:

* `refine` and `apply` replace `refine'`. While they are similar, they handle metavariables
  slightly differently; this means that they are not completely interchangeable, nor can one
  completely replace another. However, `refine` and `apply` are more readable and (heuristically)
  tend to be more efficient on average.
* `obtain`, `rcases` and `cases` replace `cases'`. Unlike the replacement tactics, `cases'`
  does not require the variables it introduces to be separated by case, which hinders readability.

The `admit` tactic is a synonym for the much more common `sorry`, so the latter should be preferred.

The `native_decide` tactic is not allowed in mathlib, as it trusts the entire Lean compiler
(and not just the Lean kernel). Because the latter is large and complicated, at present it is
probably possible to prove `False` using `native_decide`.

This linter is an incentive to discourage uses of such deprecated syntax, without being a ban.
It is not inherently limited to tactics.
-/

open Lean Elab Linter

namespace Mathlib.Linter.Style

/-- The option `linter.style.refine` of the deprecated syntax linter flags usages of
the `refine'` tactic.

The tactics `refine`, `apply` and `refine'` are similar, but they handle metavariables slightly
differently. This means that they are not completely interchangeable, nor can one completely
replace another. However, `refine` and `apply` are more readable and (heuristically) tend to be
more efficient on average.
-/
register_option linter.style.refine : Bool := {
  defValue := false
  descr := "enable the refine linter"
}

/-- The option `linter.style.cases` of the deprecated syntax linter flags usages of
the `cases'` tactic, which is a backward-compatible version of Lean 3's `cases` tactic.
Unlike `obtain`, `rcases` and Lean 4's `cases`, variables introduced by `cases'` are not
required to be separated by case, which hinders readability.
-/
register_option linter.style.cases : Bool := {
  defValue := false
  descr := "enable the cases linter"
}

/-- The option `linter.style.admit` of the deprecated syntax linter flags usages of
the `admit` tactic, which is a synonym for the much more common `sorry`. -/
register_option linter.style.admit : Bool := {
  defValue := false
  descr := "enable the admit linter"
}

/-- The option `linter.style.nativeDecide` of the deprecated syntax linter flags usages of
the `native_decide` tactic, which is disallowed in mathlib. -/
-- Note: this linter is purely for user information. Running `lean4checker` in CI catches *any*
-- additional axioms that are introduced (not just `ofReduceBool`): the point of this check is to
-- alert the user quickly, not to be airtight.
register_option linter.style.nativeDecide : Bool := {
  defValue := false
  descr := "enable the nativeDecide linter"
}

/-- The option `linter.style.maxHeartbeats` of the deprecated syntax linter flags usages of
`set_option <name-containing-maxHeartbeats> n in cmd` that do not add a comment explaining
the reason for the modification of the `maxHeartbeats`.

This includes `set_option maxHeartbeats n in` and `set_option synthInstance.maxHeartbeats n in`.
-/
register_option linter.style.maxHeartbeats : Bool := {
  defValue := false
  descr := "enable the maxHeartbeats linter"
}

/-- If the input syntax is of the form `set_option <option> num in <string> cmd`,
where `<option>` contains `maxHeartbeats`, then it returns
* the `<option>`, as a name (typically, `maxHeartbeats` or `synthInstance.maxHeartbeats`);
* the number `num` and
* whatever is in `<string>`. Note that `<string>` can only consist of whitespace and comments.

Otherwise, it returns `none`.
-/
def getSetOptionMaxHeartbeatsComment : Syntax → Option (Name × Nat × Substring)
  | stx@`(command|set_option $mh $n:num in $_) =>
    let opt := mh.getId
    if !opt.components.contains `maxHeartbeats then
      none
    else
      if let some inAtom := stx.find? (·.getAtomVal == "in") then
        inAtom.getTrailing?.map (opt, n.getNat, ·)
      else
        -- This branch should be unreachable.
        some default
  | _ => none

/-- Whether a given piece of syntax represents a `decide` tactic call with the `native` option
enabled. This may have false negatives for `decide (config := {<options>})` syntax). -/
def isDecideNative (stx : Syntax ) : Bool :=
  match stx with
  | .node _ ``Lean.Parser.Tactic.decide args =>
    -- The configuration passed to the tactic call.
    let config := args[1]![0]
    -- Check all configuration arguments in order to determine the final
    -- toggling of the native decide option.
    if let (.node _ _ config_args) := config then
      let natives := config_args.filterMap (match ·[0] with
        | `(Parser.Tactic.posConfigItem| +native) => some true
        | `(Parser.Tactic.negConfigItem| -native) => some false
        | `(Parser.Tactic.valConfigItem| (config := {native := true})) => some true
        | `(Parser.Tactic.valConfigItem| (config := {native := false})) => some false
        | _ => none)
      natives.back? == some true
    else
      false
  | _ => false

/-- `getDeprecatedSyntax t` returns all usages of deprecated syntax in the input syntax `t`. -/
partial
def getDeprecatedSyntax : Syntax → Array (SyntaxNodeKind × Syntax × MessageData)
  | stx@(.node _ kind args) =>
    let rargs := args.flatMap getDeprecatedSyntax
    match kind with
    | ``Lean.Parser.Tactic.refine' =>
      rargs.push (kind, stx,
        "The `refine'` tactic is discouraged: \
         please strongly consider using `refine` or `apply` instead.")
    | `Mathlib.Tactic.cases' =>
      rargs.push (kind, stx,
        "The `cases'` tactic is discouraged: \
         please strongly consider using `obtain`, `rcases` or `cases` instead.")
    | ``Lean.Parser.Tactic.tacticAdmit =>
      rargs.push (kind, stx,
        "The `admit` tactic is discouraged: \
         please strongly consider using the synonymous `sorry` instead.")
    | ``Lean.Parser.Tactic.decide =>
      if isDecideNative stx then
        rargs.push (kind, stx, "Using `decide +native` is not allowed in mathlib: \
        because it trusts the entire Lean compiler (not just the Lean kernel), \
        it could quite possibly be used to prove false.")
      else
        rargs
    | ``Lean.Parser.Tactic.nativeDecide =>
      rargs.push (kind, stx, "Using `native_decide` is not allowed in mathlib: \
        because it trusts the entire Lean compiler (not just the Lean kernel), \
        it could quite possibly be used to prove false.")
    | ``Lean.Parser.Command.in =>
      match getSetOptionMaxHeartbeatsComment stx with
      | none => rargs
      | some (opt, n, trailing) =>
        -- Since we are now seeing the currently outermost `maxHeartbeats` option,
        -- we remove all subsequent potential flags and only decide whether to lint or not
        -- based on whether the current option has a comment.
        let rargs := rargs.filter (·.1 != `MaxHeartbeats)
        if trailing.toString.trimLeft.isEmpty then
          rargs.push (`MaxHeartbeats, stx,
            s!"Please, add a comment explaining the need for modifying the maxHeartbeat limit, \
              as in\nset_option {opt} {n} in\n-- reason for change\n...\n")
        else
          rargs
    | _ => rargs
  | _ => default

/-- The deprecated syntax linter flags usages of deprecated syntax and suggests
replacement syntax. For each individual case, linting can be turned on or off separately.

* `refine'`, superseded by `refine` and `apply` (controlled by `linter.style.refine`)
* `cases'`, superseded by `obtain`, `rcases` and `cases` (controlled by `linter.style.cases`)
* `admit`, superseded by `sorry` (controlled by `linter.style.admit`)
* `set_option maxHeartbeats`, should contain an explanatory comment
  (controlled by `linter.style.maxHeartbeats`)
-/
def deprecatedSyntaxLinter : Linter where run stx := do
  unless getLinterValue linter.style.refine (← getLinterOptions) ||
      getLinterValue linter.style.cases (← getLinterOptions) ||
      getLinterValue linter.style.admit (← getLinterOptions) ||
      getLinterValue linter.style.maxHeartbeats (← getLinterOptions) ||
      getLinterValue linter.style.nativeDecide (← getLinterOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let deprecations := getDeprecatedSyntax stx
  -- Using `withSetOptionIn` here, allows the linter to parse also the "leading" `set_option`s
  -- but then flagging them only if the corresponding option is still set after elaborating the
  -- leading `set_option`s.
  -- In particular, this means that the linter "sees" `set_option maxHeartbeats 10 in ...`,
  -- records it in `deprecations` and then acts on it, according to the correct options.
  (withSetOptionIn fun _ ↦ do
    for (kind, stx', msg) in deprecations do
      match kind with
      | ``Lean.Parser.Tactic.refine' => Linter.logLintIf linter.style.refine stx' msg
      | `Mathlib.Tactic.cases' => Linter.logLintIf linter.style.cases stx' msg
      | ``Lean.Parser.Tactic.tacticAdmit => Linter.logLintIf linter.style.admit stx' msg
      | ``Lean.Parser.Tactic.nativeDecide | ``Lean.Parser.Tactic.decide =>
        Linter.logLintIf linter.style.nativeDecide stx' msg
      | `MaxHeartbeats => Linter.logLintIf linter.style.maxHeartbeats stx' msg
      | _ => continue) stx

initialize addLinter deprecatedSyntaxLinter

end Mathlib.Linter.Style
