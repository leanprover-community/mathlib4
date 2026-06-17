import Batteries.Tactic.Alias
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.ToAdditive
/--
warning: The namespace `add` is duplicated in the declaration `add.add`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
def add.add := True

namespace Foo

/--
warning: The namespace `Foo` is duplicated in the declaration `Foo.Foo.foo`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
def Foo.foo := True

set_option linter.translateRedundant false in
/--
warning: The namespace `add` is duplicated in the declaration `Foo.add.add`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
@[to_additive] theorem add.mul : True := .intro

--  However, the declaration `Foo.add.add` is present in the environment.
run_cmd Lean.Elab.Command.liftTermElabM do
  let decl := (← Lean.getEnv).find? ``Foo.add.add
  guard decl.isSome

namespace Nat

/--
warning: The namespace `Nat` is duplicated in the declaration `Foo.Nat.Nat.Nats`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
alias Nat.Nats := Nat

end Nat
end Foo

namespace add

/--
warning: The namespace `add` is duplicated in the declaration `add.add`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
---
warning: The namespace `add` is duplicated in the declaration `add.add`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
export Nat (add add_comm add)

end add

/--
warning: The declaration 'double__underscore' contains '__',
which does not follow the mathlib naming conventions. Consider using single underscores instead.

Note: This linter can be disabled with `set_option linter.style.nameCheck false`
-/
#guard_msgs in
set_option linter.style.nameCheck true in
theorem double__underscore : True := trivial

/--
warning: The namespace `Foo` is duplicated in the declaration `Foo.Foo`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Foo.Foo : True := trivial

/--
warning: The namespace `Foo` is duplicated in the declaration `Bar.Foo.Foo`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Bar.Foo.Foo : True := trivial

/--
warning: The namespace `Foo` is duplicated in the declaration `Foo.Foo.Bar`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Foo.Foo.Bar : True := trivial

/--
warning: The namespace `Foo` is duplicated in the declaration `Foo.Foo.Bar.Baz.hoge`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Foo.Foo.Bar.Baz.hoge : True := trivial

#guard_msgs in
lemma Foo.Foos.Bar.Baz : True := trivial

/--
warning: The namespace `Foo` is duplicated in the declaration `Foo.Bar.Foo.baz`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Foo.Bar.Foo.baz : True := trivial

/--
warning: The namespaces `Foo` and `Bar` are duplicated in the declaration `Foo.Bar.Foo.Bar.baz`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Foo.Bar.Foo.Bar.baz : True := trivial

/--
warning: The namespaces `Foo` and `Baz` are duplicated in the declaration `Foo.Bar.Baz.Hoge.Foo.Baz.baz`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Foo.Bar.Baz.Hoge.Foo.Baz.baz : True := trivial

/--
warning: The namespaces `Foo` and `Bar` are duplicated in the declaration `Foo.Bar.Baz.Hoge.Foo.Bar.baz`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Foo.Bar.Baz.Hoge.Foo.Bar.baz : True := trivial

/--
warning: The namespaces `Foo`, `Bar`, and `Baz` are duplicated in the declaration `Foo.Bar.Baz.Hoge.Foo.Bar.Baz.az`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
lemma Foo.Bar.Baz.Hoge.Foo.Bar.Baz.az : True := trivial

-- The linter detects the final name and not just what's written in the syntax.
namespace Foo.Bar
/--
warning: The namespaces `Foo` and `Bar` are duplicated in the declaration `Foo.Bar.baz'`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
def Foo.Bar.baz' := 42
end Foo.Bar

-- We detect additional generated names.
/--
warning: The namespace `AddSubgroup` is duplicated in the declaration `AddSubgroup.AddSubgroup.foo`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
@[to_additive AddSubgroup.AddSubgroup.foo]
def Subgroup.AddSubgroup.foo := 42
-- (`AddSubgroup` is duplicated but only after translation)

-- The linter works on deprecated decls: this is important
-- since people can forget to add a `_root_` when adding deprecations.
/--
warning: The namespace `Foo` is duplicated in the declaration `Foo.Bar.Foo.baz'`.

Note: This linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
@[deprecated "" (since := "")]
def Foo.Bar.Foo.baz' := 42
