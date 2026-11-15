module

import Mathlib.Init
import MathlibTest.Linter.InternalConstructor.Source

/--
@ +1:16...19
error: `Foo._mkInternal` is an internal constructor and should not be used directly.

Note: This linter can be disabled with `set_option linter.internalConstructors false`
-/
#guard_msgs (positions := true) in
def e₁ : Foo := ⟨4⟩

/--
@ +1:16...31
error: `Foo._mkInternal` is an internal constructor and should not be used directly.

Note: This linter can be disabled with `set_option linter.internalConstructors false`
-/
#guard_msgs (positions := true) in
def e₂ : Foo := Foo._mkInternal 4
