import Mathlib.Tactic.Lint
import Mathlib.Tactic.ToAdditive

set_option linter.dupNamespace true in
/-- warning:
The namespace 'add' is duplicated in the declaration 'add.add'
[linter.dupNamespace]
-/
#guard_msgs in
def add.add := True

namespace Foo
set_option linter.dupNamespace true in
/-- warning:
The namespace 'Foo' is duplicated in the declaration 'Foo.Foo.foo'
[linter.dupNamespace]
-/
#guard_msgs in
def Foo.foo := True

-- the `dupNamespace` linter does not notice that `to_additive` created `Foo.add.add`.
#guard_msgs in
@[to_additive] theorem add.mul : True := .intro

--  However, the declaration `Foo.add.add` is present in the environment.
run_cmd Lean.Elab.Command.liftTermElabM do
  let decl := (← Lean.getEnv).find? ``Foo.add.add
  guard decl.isSome

namespace Nat
/--
warning:
The namespace 'Nat' is duplicated in the declaration 'Foo.Nat.Nat.Nats' [linter.dupNamespace]
-/
#guard_msgs in
alias Nat.Nats := Nat

end Nat
end Foo

namespace add
/--
warning: The namespace 'add' is duplicated in the declaration 'add.add' [linter.dupNamespace]
-/
#guard_msgs in
export Nat (add)
