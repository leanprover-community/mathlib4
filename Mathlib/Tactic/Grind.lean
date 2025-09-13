/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# Simple frontends for `grind`

These macros will be replaced with proper implementations in Lean soon,
but are starting out here for quick experimentation.

Notes:
* If these survive to `v4.24.0`, remember to add `-ac` to the macros.
* I'll later replace these with an implementation that uses a minimal configuration
  and then reactivates modules as needed.
* It would be nice if these macros supported all the `grind` configurations, too.
-/

/--
`grobner` is a wrapper around `grind`
with only the ring normalization and Grobner basis modules enabled.
In particular, no case splitting or theorem instantiation occurs,
and the other solvers (e.g. `linarith`, `cutsat`) are disabled.
-/
macro "grobner" : tactic =>
  `(tactic| grind (ematch := 0) (splits := 0) -ext -mbtc -linarith -cutsat)

/--
`cutsat` is a wrapper around `grind`,
with only case splitting and the cutsat (integer linear arithmetic) module enabled.
In particular, no theorem instantiation occurs
and the other solvers (e.g. `linarith`, `ring`) are disabled.

This should mostly be functionally equivalent to `omega`,
although we know of discrepancies in both directions. (No need to report these.)
Where both work, `cutsat` is recommended as the implementation of `omega` is showing its age.
-/
macro "cutsat" : tactic =>
  `(tactic| grind (ematch := 0) -ext -mbtc -linarith -ring)
