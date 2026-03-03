import Mathlib.Tactic.Linter.ClassReturningDef

class Foo where
  x : Nat

/--
error: definition `bad` returns the class `Foo` but is not marked @[reducible] or @[implicit_reducible]. Consider marking it @[implicit_reducible].
-/
#guard_msgs in
def bad : Foo := { x := 1 }   -- should warn

@[reducible]
def ok1 : Foo := { x := 2 }  -- no warning

@[implicit_reducible]
def ok2 : Foo := { x := 3 }  -- no warning

abbrev ok3 : Foo := { x := 4 }  -- no warning

class Bar (α : Type) : Prop where
  eq : true

theorem ok4 : Bar (unit) := ⟨rfl⟩  -- no warning because it's a theorem
