/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Init

/-! # Open unscoped

`open unscoped Foo` opens the namespace `Foo` without activating its scope,
meaning without activating any of its scoped instances or notations.

Example usage:
```lean
namespace Nat

def pi : Nat := 3
scoped notation "π" => pi

end Nat

open unscoped Nat

#check pi
#check π -- error
```
-/

namespace Lean.Elab.Command

/-- Adds a declaration or a namespace to the list of opened namespaces in the scope. -/
def Scope.addOpenDecl (o : OpenDecl) (oldScope : Scope) : Scope :=
  { oldScope with openDecls := o :: oldScope.openDecls }

/--
`open unscoped Foo` opens the namespace `Foo` without activating its scope,
meaning without activating any of its scoped instances or notations.

Example usage:
```lean
namespace Nat

def pi : Nat := 3
scoped notation "π" => pi

end Nat

open unscoped Nat

#check pi
#check π -- error
```
-/
elab "open " "unscoped " nss:ident* : command => do
  for ns in nss do
    for ns in (← resolveNamespace ns) do
      modifyScope <| Scope.addOpenDecl <| .simple ns []

end Lean.Elab.Command
