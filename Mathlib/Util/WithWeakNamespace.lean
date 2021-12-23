/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam, Gabriel Ebner
-/

import Lean

namespace Lean.Elab.Command

/-- Changes the current namespace without causing scoped things to go out of scope -/
def withWeakNamespace (ns : Name) (m : CommandElabM α) : CommandElabM α := do
  let old ← getCurrNamespace
  modifyScope ({ · with currNamespace := ns })
  try m finally modifyScope ({ · with currNamespace := old })

def withWeakNamespaceRelative (ns : Name) (m : CommandElabM α) : CommandElabM α := do
  withWeakNamespace ((← getCurrNamespace) ++ ns) m

/-- Changes the current namespace without causing scoped things to go out of scope -/
elab "with_weak_namespace " ns:ident cmd:command : command =>
  withWeakNamespace ns.getId (elabCommand cmd)
