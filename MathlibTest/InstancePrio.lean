import Mathlib.Init

class Foo (a : Type)

-- A specific instance gets a high priority.
instance instFooNat : Foo Nat where
/-- info: some (2000) -/
#guard_msgs in
#eval do Lean.logInfo m!"{← Lean.Meta.getInstancePriority? ``instFooNat}"

-- While instances coming from inheritance or otherwise unspecific ones get a low priority.
class Bar (a : Type) extends Foo a
/-- info: some (1000) -/
#guard_msgs in
#eval do Lean.logInfo m!"{← Lean.Meta.getInstancePriority? ``Bar.toFoo}"

instance Bar.toFoo2 [Bar a] : Foo a where
/-- info: some (1000) -/
#guard_msgs in
#eval do Lean.logInfo m!"{← Lean.Meta.getInstancePriority? ``Bar.toFoo2}"

-- Also make sure a specific instance that doesn't come from an `instance` command gets higher priority.
class Baz (a : Type) extends Foo Nat
/-- info: some (2000) -/
#guard_msgs in
#eval do Lean.logInfo m!"{← Lean.Meta.getInstancePriority? ``Baz.toFoo}"
