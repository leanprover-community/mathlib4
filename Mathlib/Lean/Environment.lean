/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean.Environment

/--
Like `findConstVal?`, but only finds the `ConstantVal` for `decl` in `env` if it is a theorem.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
def Lean.Environment.findTheoremConstVal? (env : Environment) (decl : Name)
    (skipRealize := false) : Option ConstantVal := do
  -- Note: if upstreamed , we could check the (private) base first, then use `findAsyncCore?`
  let info ← env.findAsync? decl skipRealize
  if info.kind matches .thm then info.toConstantVal else none
