module

import MathlibTest.UnusedInstancesInType.Basic
import Mathlib.Data.Fintype.Defs -- Import `Fintype`, but not interface

set_option linter.unusedFintypeInType true

/--
warning: `foo` does not use the following hypothesis in its type:
  • [Fintype α] (#2)

Consider replacing this hypothesis with the corresponding instance of `Finite` and using `Fintype.ofFinite` in the proof, or removing it entirely.

Note: Add `import Mathlib.Data.Fintype.EquivFin` to make `Fintype.ofFinite` available.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo {α} [Fintype α] : True := True.intro
