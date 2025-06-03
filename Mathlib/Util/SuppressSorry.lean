/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
open Lean Elab Command

/-!
# The `suppressSorry` option

The `suppressSorry` option will cause the `warning: declaration uses 'sorry'` message
to be suppressed on any declaration. It is useful for projects which are incomplete and have
dozens or hundreds of sorries and would like to not see this noise in the build log.

The option can be set anywhere a regular option can: as `set_option` in the file (including
locally in a section, up to declaration granularity), or using the `[leanOptions]` table
in `lakefile.toml`.

To suppress sorries only in `lake build` and not interactively, add
```
weakLeanArgs = ["-Dweak.suppressSorry=true"]
```
to the `lakefile.toml` file.

If you want `lake build` to not suppress sorries in CI, you need to use the `lakefile.lean`
syntax like so:
```
package myPackage where
  weakLeanArgs := if (get_config? CI).isSome then #[] else #["-Dweak.suppressSorry=true"]
```
and then call `lake build` locally and `lake build -KCI` in your CI script.

## Implementation Notes

Lean's commands do not come with a way to do this out of the box. To accomplish it without
adding any additional text to downstream files, we hook each command elaborator. For declaration
kinds which are built in, like `theorem` (or things that macro expand to them, like `lemma`),
this is done by changing the global state for the parser to apply our sorry filter after the
command has done its thing.

Unfortunately this is not good enough because it interacts badly with the `suppress_compilation`
command, which declares a local (non-builtin) command elaborator in the middle of the file.
We can't modify the environment at import time because it is read only, so we also hook the
`attribute` command to perform a one-time environment modification to change the `command_elab`
attribute itself to hook any new command elaborators it declares.

-/

namespace Mathlib.Util.SuppressSorry

/-- Suppresses the warning `declaration uses 'sorry'` that normally appears when using `sorry`. -/
register_option suppressSorry : Bool := {
  defValue := false
  descr := "suppress sorry warnings"
}

/--
This is a list of whitelisted declarations which will be wrapped to suppress sorries.
(We could wrap all elabs but it seems prudent to just wrap the ones that actually get used.)
-/
def wrappedDeclarations := [``Parser.Command.declaration]

/--
This is a list of whitelisted declarations which will install a one-time hook to modify
`@[command_elab]` on first use. All of the ways of applying attributes boil down to using
one of these commands, so we can intercept `command_elab` before it is interpreted.
-/
def hookedDeclarations := [``Parser.Command.attribute, ``Parser.Command.declaration]

initialize
  -- Wraps a `CommandElab` to suppress sorries.
  have wrap m stx := do
    m stx
    if suppressSorry.get (← getOptions) then
      -- We have to resolve asynchronous messages or we might miss some.
      -- This might be a linearization point but `#guard_msgs` does the same thing.
      -- TODO: investigate if this can be done without waiting.
      let msgs := (← get).messages ++
        (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) {}
      modify ({ · with messages := msgs, snapshotTasks := #[] })
      if msgs.hasUnreported then
        modify fun s => { s with
          messages.unreported := s.messages.unreported.filter fun m =>
            !(m.severity matches .warning && m.data.hasTag (· == `hasSorry)) }
  have { defn, ext, .. } := commandElabAttribute
  let hooked ← IO.mkRef false
  -- This function hooks a `CommandElab` to modify the `@[command_elab]` attribute
  -- so that future elaborators will be `wrap`ped.
  have hook m stx := do
    -- This checks whether we have already run the hook so we don't do it multiple times
    if !(← hooked.get) then
      hooked.set true
      -- This is a modification of the `add` function in `Lean.KeyedDeclsAttribute.init`
      -- which implements the `@[command_elab]` attribute, where the only change is to
      -- apply the `wrap` function before installing it.
      let add declName stx attrKind := do
        let key ← defn.evalKey false stx
        let .none := IR.getSorryDep (← getEnv) declName | return
        let val ← unsafe evalConstCheck CommandElab defn.valueTypeName declName
        ext.add { key := key, declName := declName, value := wrap val } attrKind
        defn.onAdded false declName
      modifyEnv fun env => attributeExtension.modifyState env fun s =>
        { s with map := s.map.modify defn.name fun v => { v with add } }
    m stx
  -- Wraps each element of a `List AttributeEntry` with function `f`
  have wrapEntry f := .map fun e => { e with value := f e.value }
  -- Wraps all declarations in `ks` with function `f`
  have wrapTable₁ f ks r :=
    { r with map₁ := ks.foldl (fun map k => map.modify k (wrapEntry f)) r.map₁ }
  -- The actual business: wrap the `wrappedDeclarations` and hook the `hookedDeclarations`
  commandElabAttribute.tableRef.modify <|
    wrapTable₁ hook hookedDeclarations ∘
    wrapTable₁ wrap wrappedDeclarations

end Mathlib.Util.SuppressSorry
