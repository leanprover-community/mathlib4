/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Mathlib.Init

/-!
# Additional utilities for working with `MessageData`
-/

@[expose] public section

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

/--
`"no foo".withPlurals "foo" "foos" count` returns `"no foo"` when `count` is `0`,
`"foo"` when `count` is `1`, and `"foos"` otherwise.
-/
def String.withPlurals (zero singular plural : String) (count : Nat) : String :=
  if count = 0 then zero else if count = 1 then singular else plural

/--
`f!"no foo".withPlural f!"foo" f!"foos" count` returns `f!"no foo"` when `count` is `0`,
`f!"foo"` when `count` is `1`, and `f!"foos"` otherwise.
-/
def Std.Format.withPlurals (zero singular plural : Format) (count : Nat) : Format :=
  if count = 0 then zero else if count = 1 then singular else plural

/--
`m!"no foo".withPlural m!"foo" m!"foos" count` returns `m!"no foo"` when `count` is `0`,
`m!"foo"` when `count` is `1`, and `m!"foos"` otherwise.
-/
def Lean.MessageData.withPlurals (zero singular plural : MessageData) (count : Nat) : MessageData :=
  if count = 0 then zero else if count = 1 then singular else plural

end WithPlural
