import Mathlib.Util.AliasIn

@[alias_in Baz] def Foo.Bar.baz : Nat := 1
/-- info: Baz.Bar.baz : Nat -/
#guard_msgs in
#check Baz.Bar.baz

example : Baz.Bar.baz = 1 := rfl

/- Test that this evaluates correctly (note: this requires applicationTime `.afterCompilation`) -/
/-- info: 1 -/
#guard_msgs in
#eval Baz.Bar.baz

@[alias_in Baz.Qux] def Foo.Bar.baz2 : Nat := 2
/-- info: Baz.Qux.baz2 : Nat -/
#guard_msgs in
#check Baz.Qux.baz2

@[alias_in Baz.Qux 1] def Foo.Bar.baz3 : Nat := 2
/-- info: Baz.Qux.Bar.baz3 : Nat -/
#guard_msgs in
#check Baz.Qux.Bar.baz3

@[alias_in Baz.qux 3] def Foo.Bar.baz4 : Nat := 2
/-- info: Baz.qux : Nat -/
#guard_msgs in
#check Baz.qux
