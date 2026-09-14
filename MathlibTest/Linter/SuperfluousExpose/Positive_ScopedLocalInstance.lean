/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: a class, a `scoped instance`, a `local instance`, and a theorem. The linter
classifies a constant at the command that creates it, while the instance is active, so
`Lean.Meta.isInstanceCore` identifies both instances. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.ScopedLocalInstance

class Tagged (α : Type) where dummy : Unit

scoped instance instTaggedNat : Tagged Nat := ⟨()⟩

local instance instTaggedInt : Tagged Int := ⟨()⟩

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ScopedLocalInstance

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end
