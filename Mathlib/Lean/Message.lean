/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Lean.Message

/-!
# Additional utilities for working with `MessageData`
-/

section WithPlural

/-!
Thin wrappers around `if count = 1 then singular else plural` for Lean's different textual
datatypes. This helps readability of source when constructing logged messages that require dynamic
pluralization.
-/

/-- `"foo".withPlural "foos" count` returns `"foo"` when `count` is `1`, and `"foos"` otherwise. -/
def String.withPlural (singular plural : String) (count : Nat) : String :=
  if count = 1 then singular else plural

/--
`f!"foo".withPlural f!"foos" count` returns `f!"foo"` when `count` is `1`, and `f!"foos"`
otherwise.
-/
def Std.Format.withPlural (singular plural : Format) (count : Nat) : Format :=
  if count = 1 then singular else plural

/--
`m!"foo".withPlural m!"foos" count` returns `m!"foo"` when `count` is `1`, and `m!"foos"`
otherwise.
-/
def Lean.MessageData.withPlural (singular plural : MessageData) (count : Nat) : MessageData :=
  if count = 1 then singular else plural
