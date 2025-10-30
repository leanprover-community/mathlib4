/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Init

namespace Lean.Elab.Command

def Scope.addOpenDecl (o : OpenDecl) (oldScope : Scope) : Scope :=
  { oldScope with openDecls := o :: oldScope.openDecls }

elab "open " "unscoped " nss:ident* : command => do
  for ns in nss do
    for ns in (← resolveNamespace ns) do
      modifyScope <| Scope.addOpenDecl <| .simple ns []

end Lean.Elab.Command
