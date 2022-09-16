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

def eraseCore : List (Name × DataValue) → Name → List (Name × DataValue)
  | l, n => List.dropWhile (fun a => a.1 == n) l

def erase : KVMap → Name → KVMap
  | ⟨m⟩, k => ⟨eraseCore m k⟩

end Lean.KVMap
