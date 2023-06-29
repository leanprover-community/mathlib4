/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner
-/

import Lean

/-!
Defines the `use` tactic.

TODO: This does not match the full functionality of `use` from mathlib3.
See failing tests in `test/Use.lean`.
-/

open Lean.Elab.Tactic

namespace Mathlib.Tactic

/--
`use e₁, e₂, ⋯` applies the tactic `refine ⟨e₁, e₂, ⋯, ?_⟩` and then tries
to close the goal with `with_reducible rfl` (which may or may not close it). It's
useful, for example, to advance on existential goals, for which terms as
well as proofs of some claims about them are expected.

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```
-/
-- TODO extend examples in doc-string once mathlib3 parity is achieved.
macro "use " es:term,+ : tactic =>
  `(tactic| (refine ⟨$es,*, ?_⟩; try with_reducible rfl))
