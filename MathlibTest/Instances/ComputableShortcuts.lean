/-
This test must import everything to make the noncomputable instances which we don't want available.
-/
import Mathlib

/-!
# Tests that basic algebraic typeclasses are computable

Frequently mathlib will have instances of the form
```
instance : FooAndBar X := ...

-- in a later file
noncomputable instance : VeryNoncomputableFoo X := ...
```
which means that `Foo X` will sometimes be synthesized noncomputably even though a computable
version is available.

TODO: test this more exhaustively.
-/

macro "#guard_computable" t:term : command =>
  `(#guard_msgs (drop info) in #eval $t)

section Real

#guard_computable LinearMap.mul ℝ ℝ 2 3
#guard_computable LinearEquiv.neg ℝ (2 : ℝ)

end Real

section Complex

#guard_computable LinearMap.mul ℂ ℂ 2 3
#guard_computable LinearEquiv.neg ℂ (2 : ℂ)

end Complex
