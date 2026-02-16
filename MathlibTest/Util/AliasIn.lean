import Mathlib.Util.AliasIn

@[alias_in Baz] def Foo.Bar.baz : Nat := 1
/-- info: Foo.Baz.baz : Nat -/
#guard_msgs in
#check Foo.Baz.baz

example : Foo.Baz.baz = 1 := rfl

/- Test that this evaluates correctly (note: this requires applicationTime `.afterCompilation`) -/
/-- info: 1 -/
#guard_msgs in
#eval Foo.Baz.baz

@[alias_in Baz.Qux] def Foo.Bar.baz2 : Nat := 2
/-- info: Baz.Qux.baz2 : Nat -/
#guard_msgs in
#check Baz.Qux.baz2

@[alias_in Baz.Qux 1] def Foo.Bar.baz3 : Nat := 2
/-- info: Foo.Baz.Qux.baz3 : Nat -/
#guard_msgs in
#check Foo.Baz.Qux.baz3

attribute [alias_in Another.Alias] Foo.Bar.baz3
/-- info: Another.Alias.baz3 : Nat -/
#guard_msgs in
#check Another.Alias.baz3

/--
error: Foo.Bar.baz4 has only 2 namespaces, cannot remove 3.
Use `@[alias_in Baz.Qux 2]` instead.
-/
#guard_msgs in
@[alias_in Baz.Qux 3] def Foo.Bar.baz4 : Nat := 2


/--
error: Bar.baz4 has only 1 namespaces, cannot remove 3.
Use `@[alias_in Baz.Qux.Foo 1]` instead.
-/
#guard_msgs in
@[alias_in Baz.Qux.Foo] def Bar.baz4 : Nat := 2

/-- error: The `alias_in` attribute cannot be local. -/
#guard_msgs in
@[local alias_in Baz] def non.local : Nat := 2

/-- error: The `alias_in` attribute cannot be scoped. -/
#guard_msgs in
@[scoped alias_in Baz] def non.scoped : Nat := 2


/-- Look at this docstring! -/
@[alias_in Baz] def Foo.Bar.baz5 : Nat := 2

/--
info: **Alias** of `Foo.Bar.baz5`.

---

Look at this docstring!
-/
#guard_msgs in
open Lean in
run_cmd logInfo m!"{(← Lean.findDocString? (← getEnv) `Foo.Baz.baz5).get!}"
