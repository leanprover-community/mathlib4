/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
open Lean Elab Command

/-!
This file adds a backend hook which wraps every command elaborator. Currently this is only used
by `Mathlib.Util.SuppressSorry`. See the module documentation there for more information.
-/

namespace Mathlib.Util.CommandElabHook

/--
This is a list of whitelisted declarations which will install a one-time hook to modify
`@[command_elab]` on first use. All of the ways of applying attributes boil down to using
one of these commands, so we can intercept `command_elab` before it is interpreted.
-/
def hookedDeclarations := [``Parser.Command.attribute, ``Parser.Command.declaration]

/-- Wraps all declarations in `ks` with function `f`. If `ks` is `none`, everything is wrapped. -/
def wrapTable {γ} (f : γ → γ)
    (ks : Option (List Name)) (r : KeyedDeclsAttribute.Table γ) :
    KeyedDeclsAttribute.Table γ :=
  { r with map₁ := match ks with
    | some ks => ks.foldl (fun map k => map.modify k wrapEntry) r.map₁
    | none => r.map₁.fold (fun map k v => map.insert k (wrapEntry v)) {} }
where
  /-- Wraps each element of a `List AttributeEntry` with function `f` -/
  wrapEntry := .map fun e => { e with value := f e.value }

/--
Because the hooking process done here is non-compositional (it replaces rather than appends to
the implementation of `@[command_elab]`), we leave a hook of our own so that you can use
`wrapEveryCommandElab` multiple times.
-/
initialize wrapElabRef : IO.Ref (CommandElab → CommandElab) ← do
  let wrap ← IO.mkRef id
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
        ext.add { key := key, declName := declName, value := (← wrap.get) val } attrKind
        defn.onAdded false declName
      modifyEnv fun env => attributeExtension.modifyState env fun s =>
        { s with map := s.map.modify defn.name fun v => { v with add } }
    m stx
  -- The actual business: hook the `hookedDeclarations`
  commandElabAttribute.tableRef.modify <| wrapTable hook hookedDeclarations
  pure wrap

/-- Wrap every command elab in `ks` (or everything if `ks` is none), and all future declarations
as well if `future` is true. -/
def wrapEveryCommandElab (wrap : CommandElab → CommandElab)
    (ks : Option (List Name) := none) (future := true) : IO Unit := do
  if future then wrapElabRef.modify (wrap ∘ ·)
  commandElabAttribute.tableRef.modify <| wrapTable wrap ks

end Mathlib.Util.CommandElabHook
