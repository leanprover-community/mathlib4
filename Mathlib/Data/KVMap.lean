/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Lean.Data.KVMap

/-!
# Additional functionality for `KVMap`
-/

namespace Lean.KVMap

/-- erase pairs whose names match the second argument from a list of
`Name × DataValue` pairs-/
def eraseCore : List (Name × DataValue) → Name → List (Name × DataValue)
  | l, n => List.dropWhile (fun a => a.1 == n) l

/-- erase an entry from the map -/
def erase : KVMap → Name → KVMap
  | ⟨m⟩, k => ⟨eraseCore m k⟩

end Lean.KVMap
