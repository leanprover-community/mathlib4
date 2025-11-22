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
@[macro_inline]
def String.withPlural (singular plural : String) (count : Nat) : String :=
  if count = 1 then singular else plural

/--
`f!"foo".withPlural f!"foos" count` returns `f!"foo"` when `count` is `1`, and `f!"foos"`
otherwise.
-/
@[macro_inline]
def Std.Format.withPlural (singular plural : Format) (count : Nat) : Format :=
  if count = 1 then singular else plural

/--
`m!"foo".withPlural m!"foos" count` returns `m!"foo"` when `count` is `1`, and `m!"foos"`
otherwise.
-/
@[macro_inline]
def Lean.MessageData.withPlural (singular plural : MessageData) (count : Nat) : MessageData :=
  if count = 1 then singular else plural

/--
`"one foo".withPlurals "some foos" "no foos" count` returns `"no foos"` when `count` is `0`,
`"one foo"` when `count` is `1`, and `"some foos"` otherwise.
-/
@[macro_inline]
def String.withPlurals (singular plural zero : String) (count : Nat) : String :=
  if count = 0 then zero else if count = 1 then singular else plural

/--
`f!"one foo".withPlurals f!"some foos" f!"no foos" count` returns `f!"no foos"` when `count` is `0`,
`f!"one foo"` when `count` is `1`, and `f!"some foos"` otherwise.
-/
@[macro_inline]
def Std.Format.withPlurals (singular plural zero : Format) (count : Nat) : Format :=
  if count = 0 then zero else if count = 1 then singular else plural

/--
`m!"one foo".withPlurals m!"some foos" m!"no foos" count` returns `m!"no foos"` when `count` is `0`,
`m!"one foo"` when `count` is `1`, and `m!"some foos"` otherwise.
-/
@[macro_inline]
def Lean.MessageData.withPlurals (singular plural zero : MessageData) (count : Nat) : MessageData :=
  if count = 0 then zero else if count = 1 then singular else plural

end WithPlural
