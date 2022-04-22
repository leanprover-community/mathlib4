/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

import Lean
open Lean Elab

private def setOption [Monad m] [MonadError m]
    (name val : Syntax) (opts : Options) : m Options := do
  let val ← match val with
    | Syntax.ident _ _ `true _  => DataValue.ofBool true
    | Syntax.ident _ _ `false _ => DataValue.ofBool false
    | _ => match val.isNatLit? with
      | some num => DataValue.ofNat num
      | none => match val.isStrLit? with
        | some str => DataValue.ofString str
        | none =>
          throwError "unsupported option value {val}"
  opts.insert name.getId val

/-
The command `sudo set_option name val` is similar to `set_option name val`,
but it also allows to set undeclared options.
-/
open Elab.Command in
elab "sudo" "set_option" n:ident val:term : command => do
  let options ← setOption n val (← getOptions)
  modify fun s => { s with maxRecDepth := maxRecDepth.get options }
  modifyScope fun scope => { scope with opts := options }

/-
The command `sudo set_option name val in term` is similar to `set_option name val in term`,
but it also allows to set undeclared options.
-/
open Elab.Term in
elab "sudo" "set_option" n:ident val:term "in" body:term : term <= expectedType => do
  let options ← setOption n val (← getOptions)
  withTheReader Core.Context (fun ctx =>
      { ctx with maxRecDepth := maxRecDepth.get options, options := options }) do
    elabTerm body expectedType

/-
sudo set_option trace.Elab.resuming true in #check 4
#check sudo set_option trace.Elab.resuming true in by exact 4
-/
