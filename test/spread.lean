import Mathlib.Tactic.Spread

set_option autoImplicit true
class Foo (α : Type) where
  bar : True

class Something where
  bar : True

instance : Something where
  bar := by trivial

instance : Foo α where
  __ := instSomething -- include fields from `instSomething`

example : Foo α := {
  __ := instSomething -- include fields from `instSomething`
}
