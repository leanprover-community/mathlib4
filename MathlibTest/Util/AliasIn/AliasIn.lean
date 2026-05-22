import Mathlib.Util.AliasIn

/-! Tests for the `@[alias_in]` attribute without the module system -/

@[alias_in Baz] def Foo.Bar.baz : Nat := 1
/-- info: Foo.Baz.baz : Nat -/
#guard_msgs in
#check Foo.Baz.baz

@[alias_in Baz.Qux 1] def Foo.Bar.baz2 : Nat := 2
/-- info: Foo.Baz.Qux.baz2 : Nat -/
#guard_msgs in
#check Foo.Baz.Qux.baz2

/--
error: Foo.Bar.baz3 has only 2 namespaces, cannot remove 3.
Use `@[alias_in Baz.Qux 2]` instead.
-/
#guard_msgs in
@[alias_in Baz.Qux 3] def Foo.Bar.baz3 : Nat := 2


/-- error: The `alias_in` attribute cannot be used for private declarations. -/
#guard_msgs in
@[alias_in Baz] private def Foo.Bar.baz4 : Nat := 2
