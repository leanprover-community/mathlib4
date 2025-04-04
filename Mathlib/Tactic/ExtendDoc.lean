/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Init
import Lean.Elab.ElabRules
import Lean.DocString

/-!
#  `extend_doc` command

In a file where declaration `decl` is defined, writing
```lean
extend_doc decl
  before "I will be added as a prefix to the docs of `decl`"
  after "I will be added as a suffix to the docs of `decl`"
```

does what is probably clear: it extends the doc-string of `decl` by adding the string of
`before` at the beginning and the string of `after` at the end.

At least one of `before` and `after` must appear, but either one of them is optional.
-/

namespace Mathlib.Tactic.ExtendDocs

/-- `extend_docs <declName> before <prefix_string> after <suffix_string>` extends the
docs of `<declName>` by adding `<prefix_string>` before and `<suffix_string>` after. -/
syntax "extend_docs" ident (colGt &"before" str)? (colGt &"after" str)? : command

open Lean Elab Command in
elab_rules : command
  | `(command| extend_docs $na:ident $[before $bef:str]? $[after $aft:str]?) => do
    if bef.isNone && aft.isNone then throwError "expected at least one of 'before' or 'after'"
    let declName ← liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo na
    let bef := if bef.isNone then "" else (bef.get!).getString ++ "\n\n"
    let aft := if aft.isNone then "" else "\n\n" ++ (aft.get!).getString
    let oldDoc := (← findDocString? (← getEnv) declName).getD ""
    addDocStringCore declName <| bef ++ oldDoc ++ aft

end Mathlib.Tactic.ExtendDocs
