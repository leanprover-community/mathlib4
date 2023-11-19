/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import Lean.Data.NameMap
import Std.Data.RBMap

/-!
# Additional functions on `Lean.NameMap`.

We provide `NameMap.filter` and `NameMap.filterMap`.
-/

set_option autoImplicit true

namespace Lean.NameMap

instance : ForIn m (NameMap β) (Name × β) :=
  inferInstanceAs <| ForIn m (RBMap Name β _) _

/--
`filter f m` returns the `NameMap` consisting of all
"`key`/`val`"-pairs in `m` where `f key val` returns `true`.
-/
def filter (f : Name → α → Bool) (m : NameMap α) : NameMap α :=
  m.fold process {}
where
  process (r : NameMap α) (n : Name) (i : α) :=
    if f n i then r.insert n i else r

/--
`filterMap f m` allows to filter a `NameMap` and simultaneously modify the filtered values.

It takes a function `f : Name → α → Option β` and applies `f name` to the value with key `name`.
The resulting entries with non-`none` value are collected to form the output `NameMap`.
-/
def filterMap (f : Name → α → Option β) (m : NameMap α) : NameMap β :=
  m.fold process {}
where
  process (r : NameMap β) (n : Name) (i : α) :=
    match f n i with
    | none => r
    | some b => r.insert n b
