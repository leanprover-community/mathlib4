import Mathlib
import Mathlib.Util.Imports
import Mathlib.Util.WhatsNew

open Lean Meta

/--
info:
-/
#guard_msgs in
#eval show MetaM _ from do
  guard <| (← redundantImports).toArray = #[`Mathlib.Util.Imports, `Mathlib.Util.WhatsNew]

/--
info:
Found the following transitively redundant imports:
Mathlib.Util.Imports
Mathlib.Util.WhatsNew
-/
#guard_msgs in
#redundant_imports
