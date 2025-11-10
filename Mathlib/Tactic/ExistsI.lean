/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Moritz Doll
-/
module

public import Mathlib.Init
/-!
# The `existsi` tactic
This file defines the `existsi` tactic: its purpose is to instantiate existential quantifiers.
Internally, it applies the `refine` tactic.
-/

public meta section

namespace Mathlib.Tactic

/--
`existsi e₁, e₂, ⋯` applies the tactic `refine ⟨e₁, e₂, ⋯, ?_⟩`. It's purpose is to instantiate
existential quantifiers.

Examples:

```lean
example : ∃ x : Nat, x = x := by
  existsi 42
  rfl

example : ∃ x : Nat, ∃ y : Nat, x = y := by
  existsi 42, 42
  rfl
```
-/
macro "existsi " es:term,+ : tactic =>
  `(tactic| refine ⟨$es,*, ?_⟩)

end Mathlib.Tactic
