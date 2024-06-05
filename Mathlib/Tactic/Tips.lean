/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Print

/-!
#  Tips

The declarations in the environment that do not appear in the expression of other declarations.
-/

open Lean Elab.Command

namespace Tips

theorem a : True := .intro

/-- removes the entries of `ts` from the entries of `s`. -/
def eraseMany (s ts : NameSet) : NameSet :=
  Id.run do
  let mut fin := s
  for t in ts do
    fin := fin.erase t
  return fin

abbrev exclude : HashSet String := HashSet.empty |>.insert "_" |>.insert "«"

/-- The declarations in the environment that do not appear in the expression of other declarations.
-/
def tips (env : Environment) : NameSet :=
  let decls := env.constants.map₂.foldl (fun (m : NameSet) n _ =>
    if n.components.any (exclude.contains <|·.toString.take 1) then m else m.insert n
    ) {}
  dbg_trace "total decls: {decls.size} {decls.toList}"
  decls.fold (init := decls) (fun ns decl =>
    let (_, { visited, .. }) := CollectAxioms.collect decl |>.run env |>.run {}
    eraseMany ns (visited.erase decl))

#eval show CoreM _ from do
  dbg_trace (Tips.tips (← getEnv)).toList
