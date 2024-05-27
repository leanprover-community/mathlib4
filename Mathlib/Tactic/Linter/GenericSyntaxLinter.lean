/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "generic" linter

The "generic" linter takes as input a function
`unwanted : Syntax → Array Syntax` that returns the syntax nodes of an input syntax that
should be flagged.


Future extensions:
* Add `blackout? : Syntax → Bool` to prevent further inspection by the linter?
* Add `context? : InfoTree → Bool` for further effects combining `unwanted` and `blackout?` and
  possibly doing some further filtering?

See  #11890 for an example of how this may be extended.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "generic" linter emits a warning on all syntax matching a given pattern. -/
register_option linter.generic : Bool := {
  defValue := true
  descr := "enable the generic linter"
}

namespace generic

/-- is the actual symbol `·`? -/
def isCDot? : Syntax → Bool
  | .node _ ``cdotTk #[.node _ `patternIgnore #[.node _ _ #[.atom _ v]]] => v == "·"
  | .node _ ``Lean.Parser.Term.cdot #[.atom _ v] => v == "·"
  | _ => false

/--
`findDot stx` extracts from `stx` the syntax nodes of `kind` `Lean.Parser.Term.cdot` or `cdotTk`. -/
partial
def findDot : Syntax → Array Syntax
  | stx@(.node _ k args) =>
    let dargs := (args.map findDot).flatten
    match k with
      | ``Lean.Parser.Term.cdot => dargs.push stx
      | ``cdotTk => dargs.push stx
      | _ =>  dargs
  |_ => default

/-- the main unwanted syntax: a `cdot` that is not a `·`.
The function return an array of syntax atoms corresponding to `cdot`s that are not the
written with the character `·`. -/
def unwanted.cDot (stx : Syntax) : Array Syntax :=
  (findDot stx).filter (!isCDot? ·)

/-- Whether a syntax element is adding an `instance` attribute without a `local` modifier. -/
def is_attribute_instance_in : Syntax → Array Syntax
  | stx@`(command|attribute [instance] $_decl:ident in $_) => #[stx]
  | stx@`(command|attribute [instance $_priority] $_decl:ident in $_) => #[stx]
  | _ => #[]


/-
inspect: 'set_option linter.unusedVariables false in
example {n : Nat} : n = n :=
  rfl'

node Lean.Parser.Command.in, none
|-node Lean.Parser.Command.set_option, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'set_option'
|   |-ident original: ⟨⟩⟨ ⟩-- (linter.unusedVariables,linter.unusedVariables)
|   |-node null, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'false'
|-atom original: ⟨⟩⟨\n⟩-- 'in'
|-node Lean.Parser.Command.declaration, none
|   |-node Lean.Parser.Command.declModifiers, none
|   |   |-node null, none
|   |   |-node null, none
|   |   |-node null, none
|   |   |-node null, none
|   |   |-node null, none
|   |   |-node null, none
|   |-node Lean.Parser.Command.example, none
|   |   |-atom original: ⟨⟩⟨ ⟩-- 'example'
|   |   |-node Lean.Parser.Command.optDeclSig, none
|   |   |   |-node null, none
|   |   |   |   |-node Lean.Parser.Term.implicitBinder, none
|   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '{'
|   |   |   |   |   |-node null, none
|   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (n,n)
|   |   |   |   |   |-node null, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |   |   |-ident original: ⟨⟩⟨⟩-- (Nat,Nat)
|   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '}'
|   |   |   |-node null, none
|   |   |   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |   |-node «term_=_», none
|   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (n,n)
|   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '='
|   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (n,n)
|   |   |-node Lean.Parser.Command.declValSimple, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':='
|   |   |   |-ident original: ⟨⟩⟨\n\n⟩-- (rfl,rfl)
|   |   |   |-node Lean.Parser.Termination.suffix, none
|   |   |   |   |-node null, none
|   |   |   |   |-node null, none
|   |   |   |-node null, none
-/
#check withSetOptionIn

open Command in
partial def withoutSetOptionIn (cmd : CommandElab) : CommandElab := fun stx => do --withoutModifyingEnv do
  let mut ms := 0
  let s ← get
  if stx.getKind == ``Lean.Parser.Command.in &&
    stx[0].getKind == ``Lean.Parser.Command.set_option then
      dbg_trace "inside"
      --logInfo stx[2];
      --logInfo ""
      --logWarning ""
      cmd stx[2]
      --logWarning m!"{ms}, {(← get).messages.isEmpty}"
--      logInfo m!"messages: {(← MonadState.get).messages.msgs.size}\nempty: {(← MonadState.get).messages.isEmpty}"
--      logInfo m!"messages: {((← MonadState.get).messages.msgs.map (·.data)).toArray}"
      --if (← MonadState.get).messages.isEmpty then logInfoAt stx  m!"no messages {((← MonadState.get).messages.msgs.map (·.data)).toArray}"
      --else logInfo "messages"

      --logInfo m!"{ms}, {(← get).messages.isEmpty}"
      ms := ms + (← get).messages.msgs.size --+ if ! (← get).messages.isEmpty then 1 else 0
--  set s
  if ms == 0 then logWarningAt stx "unused `set_option`"
  dbg_trace ms
elab "ws " cmd:command : command => withoutSetOptionIn Command.elabCommand cmd

ws
set_option linter.unusedVariables false in
example {n : Nat} : n = n := rfl

ws
set_option linter.unusedVariables false in
example {n : Nat} : true := have := 0 ; rfl

#exit
def is_soi : Syntax → Option Syntax
  | s@(.node _ ``Lean.Parser.Command.in _
  --#[
  --    .node _ ``Lean.Parser.Command.set_option _,
  --    _,
  --    cmd
  --  ]
    ) => --dbg_trace s.getKind
         some s
  | _s => --dbg_trace s.getKind
         none


end generic

end Mathlib.Linter

namespace Mathlib.Linter.generic

/-- Gets the value of the `linter.generic` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.generic o
#check StrLit
/-- The main implementation of the generic syntax linter. -/
def genericSyntaxLinter --(contains? : Syntax → Array (Syntax × MessageData))
    (toElab : Syntax → Option Syntax) : Linter where
  run := fun stx => do --withoutSetOptionIn fun stx => do --withoutModifyingEnv do
--    unless getLinterHash (← getOptions) do
--      return
--    if (← MonadState.get).messages.hasErrors then
--      return
--    let _ ← (contains? stx).mapM fun (s, msg) =>
--      Linter.logLint linter.generic s msg
--      dbg_trace "{is_soi stx}"
      if let some stx := toElab stx then
--      dbg_trace stx[0][3]
--      dbg_trace (← `(true))
--      let tr : Syntax ← `(true)
        let options ← getOptions --Elab.elabSetOption stx[0][1] stx[0][3]
        --let st := (← get).scopes
--        dbg_trace options
        let nopt := options.entries.dropLast

        --withoutModifyingEnv do
   --       Command.withScope (fun scope => { scope with opts := {entries := nopt} }) do
        --  dbg_trace "scopes {st.map (·.opts)}"
        --withoutSetOptionIn
        --    let _ ← Command.elabCommand stx
        withoutSetOptionIn Command.elabCommand stx --=> do
            if (← MonadState.get).messages.isEmpty then
              logInfoAt stx "no messages"
  --          else
  --            dbg_trace "messages {((← MonadState.get).messages.msgs.size)}"
  --            logWarning m!"messages {((← MonadState.get).messages.msgs.map (·.data)).toArray}"
initialize addLinter (genericSyntaxLinter /-(fun _ => #[])-/ is_soi)

#exit
initialize addLinter (genericSyntaxLinter fun stx =>
  (unwanted.cDot stx).map (·, "cdots should use `·`"))

initialize addLinter (genericSyntaxLinter fun stx =>
  (is_attribute_instance_in stx).map (·, "careful: \
    `attribute [instance] ... in` declarations are surprising: \
    they are **not** limited to the subsequent declaration, \
    but define global instances \
    please remove the `in` or make this a `local instance` instead"))
