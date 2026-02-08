module

import MathlibTest.UnusedInstancesInType.Basic
import Mathlib.Data.Fintype.Defs -- Import `Fintype`, but not interface

set_option linter.unusedFintypeInType true

/--
warning: `foo` has the hypothesis:
  • [Fintype α] (#2)
which is not used in the remainder of the type.

Consider replacing this hypothesis with the corresponding instance of `Finite` and using `Fintype.ofFinite` in the proof, or removing it entirely.

Note: Add `import Mathlib.Data.Fintype.EquivFin` to make `Fintype.ofFinite` available.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
theorem foo {α} [Fintype α] : True := True.intro
