module

import MathlibTest.UnusedInstancesInType.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Test workaround for lean4#11313 -/

namespace decidableTest

set_option linter.unusedDecidableInType true

-- Silenceable
set_option linter.unusedDecidableInType false in
theorem foo [DecidablePred Nonempty] [DecidableEq (Nat → Nat)] :
    Uses (DecidableEq (Nat → Nat)) → True :=
  fun _ => trivial

set_option linter.unusedDecidableInType false

-- Overrideable
/--
warning: `foo'` has the hypothesis:
  • [DecidablePred Nonempty] (#1)
which is not used in the remainder of the type.

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
-/
#guard_msgs in
set_option linter.unusedDecidableInType true in
/-- Same as `foo`.-/
theorem foo' [DecidablePred Nonempty] [DecidableEq (Nat → Nat)] :
    Uses (DecidableEq (Nat → Nat)) → True :=
  fun _ => trivial

end decidableTest

namespace fintypeTest

set_option linter.unusedFintypeInType true

-- Silenceable
set_option linter.unusedFintypeInType false in
theorem foo [Fintype Bool] [Fintype (Nat → Nat)] :
    Uses (Fintype (Nat → Nat)) → True :=
  fun _ => trivial

set_option linter.unusedFintypeInType false

-- Overrideable
/--
warning: `foo'` has the hypothesis:
  • [Fintype Bool] (#1)
which is not used in the remainder of the type.

Consider replacing this hypothesis with the corresponding instance of `Finite` and using `Fintype.ofFinite` in the proof, or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
-/
#guard_msgs in
set_option linter.unusedFintypeInType true in
/-- Same as `foo'`.-/
theorem foo' [Fintype Bool] [Fintype (Nat → Nat)] :
    Uses (Fintype (Nat → Nat)) → True :=
  fun _ => trivial
