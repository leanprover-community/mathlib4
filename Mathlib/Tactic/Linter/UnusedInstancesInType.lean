/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Mathlib.Lean.Expr.Basic
public meta import Mathlib.Lean.Environment
public meta import Mathlib.Lean.Elab.InfoTree
public meta import Lean.Linter.Basic
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  --shake: keep
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint.Misc

/-!
# Linters for Unused Instances in Types

This file declares linters which detect certain instance hypotheses in declarations that are unused
in the remainder of the type.

Currently, these linters only handle theorems. (This also includes `lemma`s and `instance`s of
`Prop` classes.)

- `unusedDecidableInType` linter (currently off by default): suggests replacing type-unused
  `Decidable*` instance hypotheses, and could therefore be replaced by `classical` in the proof.

TODO: log on type signature instead of whole command
TODO: add more linters!
TODO: create Try This suggestions
-/

meta section

open Lean Meta Elab Command Linter

namespace Mathlib.Linter.UnusedInstancesInType

/--
A structure for storing information about a parameter of some declaration, usually within some
telescope. We use this for recording the expressions and index associated to a parameter which was
unused in the remainder of the type.

`m!"{param}"` displays as `[{param.type?.get}] (#{param.idx + 1})` if `type?` is `some _`, and as
`parameter #{param.idx + 1}` as a failsafe if `type?` is `none`. (We always expect `type?` to be
`some _`, but would like a fallback if there are unexpected issues in telescoping.)
-/
structure Parameter where
  /- TODO: include syntax references to the binders here, and use the "real" fvars created during
  elaboration if possible -/
  /-- The free variable of the parameter created in a telescope for logging.
  We always expect this to be `some _` normally, but allow `none` as a failsafe. -/
  fvar? : Option Expr
  /-- The type of the parameter created in a telescope for logging.
  We always expect this to be `some _` normally, but allow `none` as a failsafe. -/
  type? : Option Expr
  /-- The index of the parameter among the `forall` binders in the type (starting at 0). -/
  idx : Nat

instance : ToMessageData Parameter where
  toMessageData (param : Parameter) :=
    if let some type := param.type? then
      m!"[{type}] (#{param.idx + 1})"
    else
      m!"parameter #{param.idx + 1}"

/--
Given a (full, resolvable) declaration name `foo` and an array of parameters
`#[p₁, p₂, ..., pₙ]`, constructs the message:
```null
`{foo}` has the hypothes(is/es):
  • {p₁}
  • {p₂}
  ⋮
  • {pₙ}
which (is/are) not used in the remainder of the type.
```
-/
def _root_.Lean.Name.unusedInstancesMsg (declName : Name)
    (unusedInstanceBinders : Array Parameter) : MessageData :=
  let unusedInstanceBinders := unusedInstanceBinders.map toMessageData
  m!"`{.ofConstName declName}` has the \
  {if unusedInstanceBinders.size = 1 then "hypothesis" else "hypotheses"}:\
  {(unusedInstanceBinders.map (m!"\n  • {·}") |>.foldl (init := .nil) .compose)}\nwhich \
  {if unusedInstanceBinders.size = 1 then "is" else "are"} not used in the remainder of the type."

/--
Gathers instance hypotheses in the type of `decl` that are unused in the remainder of the type and
whose types satisfy `p`. (Does not consider the body of the declaration.) Collects them into an
`Array Parameter`, and if (and only if) this array is nonempty, feeds it to `logOnUnused`.

Since `logOnUnused` will only be run if its argument is nonempty, it is allowed to be expensive.

Note that `p` is non-monadic, and may encounter loose bvars in its argument. This is a performance
optimization. However, the `Parameter`s are created in a telescope, and their fields will *not*
have loose bound variables.
-/
def _root_.Lean.ConstantVal.onUnusedInstancesWhere (decl : ConstantVal)
    (p : Expr → Bool) (logOnUnused : Array Parameter → TermElabM Unit) : CommandElabM Unit := do
  let unusedInstances := decl.type.getUnusedForallInstanceBinderIdxsWhere p
  if let some maxIdx := unusedInstances.back? then liftTermElabM do
    unless decl.type.hasSorry do -- only check for `sorry` in the "expensive" case
      forallBoundedTelescope decl.type (some <| maxIdx + 1)
        (cleanupAnnotations := true) fun fvars _ => do
          let unusedInstances : Array Parameter ← unusedInstances.mapM fun idx =>
            return {
                fvar? := fvars[idx]?
                type? := ← fvars[idx]?.mapM (inferType ·)
                idx
              }
          logOnUnused unusedInstances

/--
Finds theorems whose bodies were elaborated in the current infotrees and whose (full)
declaration names satisfy `nameFilter`. Checks their type to see if it contains instance hypotheses
that (1) are unused in the remainder of the type (2) have types which satisfy `instanceTypeFilter`.
(Note: `instanceTypeFilter` is non-monadic, and may encounter bound variables in its argument. This
is a performance optimization. `isAppOrForallOfConstP` may be useful in detecting constant
applications and types of the form `∀ (...), bar ..` here.)

If any such parameters are found in the type of a theorem `foo`, we create a telescope in which the
types and free variables of the unused parameters are available as
`unusedParams : Array Parameter := #[p₁, p₂, ..., pₙ]`, as well as the theorem `thm : ConstantVal`
and current infotree `t`, and run `log t thm unusedParams`.

A simple pattern is therefore
```
fun _ thm unusedParams => do
  logLint linter.fooLinter (← getRef) m!"\
    {thm.name.unusedInstancesMsg unusedParams}\n\n\
    <extra caption>"
```
which logs
```null
`{foo}` has the hypothes(is/es):
  • {p₁}
  • {p₂}
  ⋮
  • {pₙ}
which (is/are) not used in the remainder of the type.

<extra caption>

Note: This linter can be disabled with `set_option {linter.fooLinter.name} false`
```
pluralizing as appropriate.
-/
@[nolint unusedArguments] -- TODO: we plan to use `_cmd` in future
def _root_.Lean.Syntax.logUnusedInstancesInTheoremsWhere (_cmd : Syntax)
    (instanceTypeFilter : Expr → Bool)
    (log : InfoTree → ConstantVal → Array Parameter → TermElabM Unit)
    (declFilter : ConstantVal → Bool := fun _ => true) : CommandElabM Unit := do
  for t in ← getInfoTrees do
    let thms := t.getTheorems (← getEnv) |>.filter declFilter
    for thm in thms do
      thm.onUnusedInstancesWhere instanceTypeFilter fun unusedParams =>
        -- TODO: restore in order to log on type signature. See (#31729)[https://github.com/leanprover-community/mathlib4/pull/31729].
        -- t.withDeclSigRef cmd thm.name do
        log t thm unusedParams

section Decidable

/--
Checks if `type` is an application of (or forall with return type which is an application of) a
`Decidable*` constant. Specifically, checks if the constant is one of:
- `Decidable`
- `DecidablePred`
- `DecidableRel`
- `DecidableEq`
- `DecidableLE`
- `DecidableLT`

Ignores metadata and cleans up annotations.
-/
def isDecidableVariant (type : Expr) : Bool :=
  type.isAppOrForallOfConstP fun n =>
    n == ``Decidable     ||
    n == ``DecidablePred ||
    n == ``DecidableRel  ||
    n == ``DecidableEq   ||
    n == ``DecidableLE   ||
    n == ``DecidableLT

/-- `withSetOptionIn` currently breaks infotree searches, so we simply set `Bool` options
until this is fixed in [lean4#11313](https://github.com/leanprover/lean4/pull/11313). -/
partial def withSetBoolOptionIn (x : CommandElab) : CommandElab
  | `(command| set_option $opt:ident $val in $cmd:command) => do
    match val.raw with
    | Syntax.atom _ "true"  =>
      withBoolOption opt.getId true <| withSetBoolOptionIn x cmd
    | Syntax.atom _ "false" =>
      withBoolOption opt.getId false <| withSetBoolOptionIn x cmd
    | _ => withSetBoolOptionIn x cmd
  | `(command| $_:command in $cmd:command) => withSetBoolOptionIn x cmd
  | stx => x stx
where
  /-- Set a `Bool` option in `CommandElabM`. Ideally, `CommandElabM` would have a
  `MonadWithOptions` instance to this effect. -/
  withBoolOption (n : Name) (val : Bool) (k : CommandElabM Unit) : CommandElabM Unit := do
    let opts := (← getOptions).setBool n val
    Command.withScope (fun scope => { scope with opts }) k

/--
The `unusedDecidableInType` linter checks if a theorem's hypotheses include `Decidable*` instances
which are not used in the remainder of the type. If so, it suggests removing the instances and using
`classical` or `open scoped Classical in`, as appropriate, in the theorem's proof instead.

This linter fires only on theorems. (This includes `lemma`s and `instance`s of `Prop` classes.)

Note: `set_option linter.unusedDecidableInType _ in <command>` currently only works at the
outermost level of a command due to working around [lean4#11313](https://github.com/leanprover/lean4/pull/11313).
-/
public register_option linter.unusedDecidableInType : Bool := {
  defValue := false
  descr := "enable the unused `Decidable*` instance linter, which lints against `Decidable*` \
    instances in the hypotheses of theorems which are not used in the type, and can therefore be \
    replaced by a use of `classical` in the proof."
}

/-- Detects `Decidable*` instance hypotheses in the types of theorems which are not used in the
remainder of the type, and suggests replacing them with a use of `classical` in the proof or
`open scoped Classical in` at the term level. -/
def unusedDecidableInType : Linter where
  run := withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.unusedDecidableInType (← getLinterOptions) do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      /- Theorems in the `Decidable` namespace such as `Decidable.eq_or_ne` are allowed to depend
      on decidable instances without using them in the type. -/
      (declFilter := (!(`Decidable).isPrefixOf ·.name))
      isDecidableVariant
      fun _ thm unusedParams => do
        logLint linter.unusedDecidableInType (← getRef) m!"\
          {thm.name.unusedInstancesMsg unusedParams}\n\n\
          Consider removing \
          {if unusedParams.size = 1 then "this hypothesis" else "these hypotheses"} \
          and using `classical` in the proof instead. \
          For terms, consider using `open scoped Classical in` at the term level (not the command \
          level)."

initialize addLinter unusedDecidableInType

end Decidable

section Fintype

/--
The `unusedFintypeInType` linter checks if a theorem's hypotheses include `Fintype` instances
which are not used in the remainder of the type. If so, it suggests modifying the instances to
`Finite _` and using `Fintype.ofFinite` in the proof, or removing them entirely.

This linter fires only on theorems. (This includes `lemma`s and `instance`s of `Prop` classes.)
-/
public register_option linter.unusedFintypeInType : Bool := {
  defValue := false
  descr := "enable the unused `Fintype` instance linter, which lints against `Fintype` \
    instances in the hypotheses of theorems which are not used in the type, and can therefore be \
    replaced by a hypothesis of `Finite` or removed entirely."
}

/-- Detects `Fintype` instance hypotheses in the types of theorems which are not used in the
remainder of the type, and suggests replacing them with the corresponding hypothesis of `Finite`
and the use of `Fintype.ofFinite` in the proof. -/
def unusedFintypeInType : Linter where
  run := withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.unusedFintypeInType (← getLinterOptions) do
      return
    -- Cheap early exit if `Fintype` is not imported.
    unless (← getEnv).isImportedConst `Fintype do
      return
    cmd.logUnusedInstancesInTheoremsWhere
      (·.isAppOrForallOfConst `Fintype)
      fun _ thm unusedParams => do
        let importFintypeOfFiniteNote? :=
          if (← getEnv).isImportedConst `Fintype.ofFinite then none else
            some <| .note "Add `import Mathlib.Data.Fintype.EquivFin` \
              to make `Fintype.ofFinite` available."
        logLint linter.unusedFintypeInType (← getRef) m!"\
          {thm.name.unusedInstancesMsg unusedParams}\n\n\
          Consider replacing \
          {if unusedParams.size = 1 then "this hypothesis" else "these hypotheses"} with the \
          corresponding {if unusedParams.size = 1 then "instance" else "instances"} of \
          `{.ofConstName `Finite}` and using \
          `{.ofConstName `Fintype.ofFinite}` in the proof, or removing \
          {if unusedParams.size = 1 then "it" else "them"} entirely.\
          {importFintypeOfFiniteNote?.getD m!""}"

initialize addLinter unusedFintypeInType

end Fintype

end Mathlib.Linter.UnusedInstancesInType
