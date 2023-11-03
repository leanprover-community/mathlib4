/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Mac Malone
-/
import Lean

/-!
# Supressing compilation to executable code in a file or in a section

Currently, the compiler may spend a lot of time trying to produce executable code for complicated
definitions. This is a waste of resources for definitions in area of mathematics that will never
lead to executable code. The command `suppress_compilation` is a hack to disable code generation
on all definitions (in a section or in a whole file). See the issue mathlib4#7103
-/

open Lean Parser Elab Command

/-- Replacing `def` and `instance` by `noncomputable def` and `noncomputable instance`, designed
to disable the compiler in a given file or a given section.
This is a hack to work around mathlib4#7103. -/
def elabSuppressCompilationDecl : CommandElab := fun
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal $(term?)? $(decr?)?) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal $(term?)? $(decr?)?)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal deriving $derivs,* $(term?)? $(decr?)?) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal deriving $derivs,* $(term?)? $(decr?)?)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? $(attrKind?)? instance $(prio?)? $(id?)? $sig:declSig $val:declVal $(term?)?) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? $(attrKind?)? instance $(prio?)? $(id?)? $sig:declSig $val:declVal $(term?)?)
| _ => throwUnsupportedSyntax

/-- Replacing `def` and `instance` by `noncomputable def` and `noncomputable instance`, designed
to disable the compiler in a given file or a given section.
This is a hack to work around mathlib4#7103. -/
macro "suppress_compilation" : command => do
  let kind := mkIdent ``declaration
  let etor := mkCIdent ``elabSuppressCompilationDecl
  `(attribute [local command_elab $kind] $etor)
