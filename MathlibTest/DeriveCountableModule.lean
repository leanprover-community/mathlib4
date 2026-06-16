module

import Mathlib.Tactic.DeriveCountable
import Mathlib.Data.Countable.Basic

/-!
# Regression test: `deriving Countable` under the module system

The deriving handler emits user-facing code that mentions a few helper lemmas.
Under the module system, marking those helpers `private` makes them invisible
to importers (without `import all`), so `deriving Countable` failed with
`Unknown constant '_private.Mathlib.Tactic.DeriveCountable.0.…cons_eq_imp_init'`.

These tests cover the single-constructor MWE from the bug report and a
recursive case that exercises `cons_eq_imp` and `pair_encode_step`.
-/

namespace Test

inductive Single where
  | test
  deriving Countable

example : Countable Single := inferInstance

inductive Tree where
  | leaf (n : Nat)
  | node (l r : Tree)
  deriving Countable

example : Countable Tree := inferInstance

end Test
