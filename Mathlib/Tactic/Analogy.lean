/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Lean

/-!
# Analogies

This file defines a new command `analogy` which allows the user to state an analogy between two pairs of objects.
We store analogies in an environment extension.
-/

open Lean Elab Command

structure Analogy where
  src : Name
  tgt : Name
  src' : Name
  tgt' : Name
  descr : Option String := none
deriving Hashable, BEq

initialize analogyExt : SimplePersistentEnvExtension Analogy (Std.HashSet Analogy) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := .insert
    addImportedFn := fun ess => ess.foldl (fun m es => es.foldl .insert m) ∅
  }

syntax (name := analogy) declModifiers "analogy := " ident " : " ident " :: " ident " : " ident : command

@[command_elab analogy]
def elabAnalogy : CommandElab
  | `($mods:declModifiers analogy := $s:ident : $t:ident :: $s':ident : $t':ident) => do
    let mods ← elabModifiers mods
    let s ← resolveGlobalConstNoOverload s
    let t ← resolveGlobalConstNoOverload t
    let s' ← resolveGlobalConstNoOverload s'
    let t' ← resolveGlobalConstNoOverload t'
    modifyEnv fun env => analogyExt.addEntry env <| .mk s t s' t' mods.docString?
  | _ => throwUnsupportedSyntax

def Analogy.format (a : Analogy) : CoreM Format := Meta.MetaM.run' do
  let env ← getEnv
  let some csrc := env.find? a.src | throwError "Unable to find {a.src}"
  let some ctgt := env.find? a.tgt | throwError "Unable to find {a.tgt}"
  let some csrc' := env.find? a.src' | throwError "Unable to find {a.src'}"
  let some ctgt' := env.find? a.tgt' | throwError "Unable to find {a.tgt'}"
  let mut out := Format.nil
  out := out ++ a.descr.getD "" ++ f!"\n"
  out := out ++ f!"{csrc.name} : {← Meta.ppExpr csrc.type}\n\n"
  out := out ++ "is to\n\n"
  out := out ++ f!"{ctgt.name} : {← Meta.ppExpr ctgt.type}\n\n"
  out := out ++ "as\n\n"
  out := out ++ f!"{csrc'.name} : {← Meta.ppExpr csrc'.type}\n\n"
  out := out ++ "is to\n\n"
  out := out ++ f!"{ctgt'.name} : {← Meta.ppExpr ctgt'.type}\n\n"
  return out

elab "#analogies" : command => do
  let analogies := analogyExt.getState (← getEnv)
  for analogy in analogies do
    let fmt ← Command.liftCoreM analogy.format
    println! fmt
    println! "\n"

