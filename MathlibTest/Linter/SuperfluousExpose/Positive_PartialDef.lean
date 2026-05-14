/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: file with only `partial def`s. Per the Lean reference,
`partial def`s are "treated as opaque constants by the kernel and are
neither unfolded nor reduced". Their bodies are irrelevant to downstream
typechecking. (Internally they become `opaqueInfo`s, which the linter
already skips, but we document the case explicitly.) -/

@[expose] public section

namespace SuperfluousExposeTest.PartialDef

partial def loopWhile (n : Nat) : Nat :=
  if n = 0 then 0 else loopWhile (n - 1)

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.PartialDef
-- Expected: linter warning at end-of-file.
