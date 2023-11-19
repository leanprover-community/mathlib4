import Mathlib
import Mathlib.Util.Imports
import Mathlib.Util.WhatsNew

open Lean Meta
#eval show MetaM _ from do
  guard <| (← redundantImports).toArray = #[`Mathlib.Util.Imports, `Mathlib.Util.WhatsNew]

#redundant_imports
