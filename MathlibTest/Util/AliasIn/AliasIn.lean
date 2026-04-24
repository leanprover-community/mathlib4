import Mathlib.Util.AliasIn

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
