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

open Lean Elab Command

set_option autoImplicit true in
open private docStringExt in addDocString in
/-- Replace a declaration's docstring. If `declName` does not have a docstring yet, add it.

Note that the docstring extension maintains both a `List (Name × String)` (for serialization) and a
`NameMap String` (for state). Each `Name` in this `List` should be unique.
`addDocString declName docString` assumes that `declName` does not have a docstring yet, and simply
prepends `(declName, docString)` to the list. As such, it is unsuitable for modifying extant
docstrings. -/
private def replaceDocString [Monad m] [MonadError m] [MonadEnv m]
    (declName : Name) (docString : String) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  modifyEnv fun env => PersistentEnvExtension.modifyState docStringExt env fun (entries, map) =>
    let entries := if map.contains declName then
      modifyEntry entries else (declName, docString) :: entries
    -- Note that `NameMap.insert` overwrites any existing key-value pairs.
    (entries, map.insert declName docString)
where
  /-- Replace the `String` in the first pair that contains `declName`. (`declName` is assumed to
  appear somewhere in the list.) -/
  modifyEntry : List (Name × String) → List (Name × String)
  | e@(n, _) :: entries =>
    if n == declName then (n, docString) :: entries else e :: modifyEntry entries
  | [] => []

/-- `extend_docs <declName> before <prefix_string> after <suffix_string>` extends the
docs of `<declName>` by adding `<prefix_string>` before and `<suffix_string>` after. -/
syntax "extend_docs" ident (colGt &"before" str)? (colGt &"after" str)? : command

elab_rules : command
  | `(command| extend_docs $na:ident $[before $bef:str]? $[after $aft:str]?) => do
    if bef.isNone && aft.isNone then throwError "expected at least one of 'before' or 'after'"
    let declName ← liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo na
    let bef := if bef.isNone then "" else (bef.get!).getString ++ "\n\n"
    let aft := if aft.isNone then "" else "\n\n" ++ (aft.get!).getString
    let oldDoc := (← findDocString? (← getEnv) declName).getD ""
    replaceDocString declName <| bef ++ oldDoc ++ aft

end Mathlib.Tactic.ExtendDocs
