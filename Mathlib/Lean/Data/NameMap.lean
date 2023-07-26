/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import Lean.Data.NameMap

/-!
# Additional functions on `Lean.NameMap`.

We provide `NameMap.filter`.
-/

namespace Lean.NameMap

/--
Filter a `NameMap`. Takes a second optional argument `modify : α → α` which allows
to modify/filter the value of each (key, value)-pair simultaneously.
-/
def filter (m : NameMap α) (f : Name → Bool) (modify : α → α := id) : NameMap α :=
  m.fold process {}
where
  process (r : NameMap α) (n : Name) (i : α) :=
    if f n then r.insert n (modify i) else r
