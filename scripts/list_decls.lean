/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib

/-!
# `list_decls`

Building this file outputs the fully-qualified name of "every" declaration in the environment.
-/

namespace ListDecls
open Lean Elab Meta Command

/-- `listDeclsCore` is the main implementation of the `list_decls` command. -/
def listDeclsCore {m : Type → Type} [Monad m] [MonadEnv m] (all? : Bool) :
    m (Array Name) := do
  let names ← (← getEnv).constants.map₁.foldM (init := #[]) (fun ns n c => do
    if all? && (c.isUnsafe || (← n.isBlackListed)) then return ns else return ns.push n)
  return names.qsort (·.toString < ·.toString)

/-- The `list_decls` command prints the array of all non-unsafe, non-blacklisted declarations in
the environment.

To include *all* declarations, use `list_decls!`.
-/
elab (name := listDeclsCmd) "list_decls" tk:"!"? : command => do
  IO.println <| "\n".intercalate <| (← listDeclsCore tk.isNone).map (·.toString) |>.toList

@[inherit_doc listDeclsCmd]
macro "list_decls!" : command => `(list_decls !)

end ListDecls

--list_decls
