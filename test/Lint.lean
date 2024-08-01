import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.ToAdditive

-- TODO: the linter also runs on the #guard_msg, so disable it once
-- See https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/.23guard_msgs.20doesn't.20silence.20warnings/near/423534679

set_option linter.dupNamespace false

/--
warning: The namespace 'add' is duplicated in the declaration 'add.add'
note: this linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
def add.add := True

namespace Foo

/--
warning: The namespace 'Foo' is duplicated in the declaration 'Foo.Foo.foo'
note: this linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
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
warning: The namespace 'Nat' is duplicated in the declaration 'Foo.Nat.Nat.Nats'
note: this linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
alias Nat.Nats := Nat

end Nat
end Foo

namespace add

/--
warning: The namespace 'add' is duplicated in the declaration 'add.add'
note: this linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
export Nat (add)

end add

set_option linter.cdot false in
/--
warning: Please, use '·' (typed as `\·`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
---
warning: Please, use '·' (typed as `\·`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
---
warning: Please, use '·' (typed as `\·`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
-/
#guard_msgs in
set_option linter.cdot true in
attribute [instance] Int.add in
instance : Inhabited Nat where
  default := by
    . have := 0
      · have : Nat → Nat → Nat := (· + .)
        . exact 0

set_option linter.cdot false in
/--
warning: Please, use '·' (typed as `\·`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
-/
#guard_msgs in
set_option linter.cdot true in
example : Add Nat where add := (. + ·)

-- Tests for the badVariable linter.
set_option autoImplicit false

-- HACK. inserting temporary sections to make the linter work.
-- TODO fix the linter and remove these again!

-- These are all fine.
section
variable {a : Type*}

section
variable {n : ℕ} (m : ℕ := 42) (k : ℕ := by exact 0)

section
variable {p q} {r s : Prop}

section
variable ⦃x y : Int⦄  ⦃x y⦄

section
variable (a : Type*) (b : Prop) [DecidableEq a]

section
variable [DecidableEq a] [Inhabited b] {f : a → b}

-- `a` is changed, but no new variable is declared (only typeclass instances are added):
-- this is fine, right?
-- That means typeclasses and instance implicits are fine for this purpose?
-- (I can certainly write a linter ignoring these for now, and see if it yields useful results)
section
variable (a)
theorem foo : True := trivial

section
variable {a} [DecidableEq b]

-- These should error.
section
variable (a) -- dummy line
section
variable {a} (b : Type)
section
variable (a) {b : Type}

-- I guess this is also bad, changing b and adding a --- i.e., the binder order doesn't matter?!
section
variable {b : Type*}
-- XXX: this line errors about a "redundant binder update"... which also seems fishy
section
-- variable {a : Type} (b)

end
end
end
end
end
end
end
end
end
end
end
end
end
