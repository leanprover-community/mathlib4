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
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
---
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
---
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.
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
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
-/
#guard_msgs in
set_option linter.cdot true in
example : Add Nat where add := (. + ·)

set_option linter.longLine false
/--
warning: This line exceeds the 100 character limit, please shorten it!
note: this linter can be disabled with `set_option linter.longLine false`
-/
#guard_msgs in
set_option linter.longLine true in
/-!                                                                                                -/

#guard_msgs in
-- Lines with more than 100 characters containing URLs are allowed.
set_option linter.longLine true in
/-!  http                                                                                          -/

set_option linter.longLine true
-- The *argument* of `#guard_msgs` is *not* exempt from the linter.
/--
warning: This line exceeds the 100 character limit, please shorten it!
note: this linter can be disabled with `set_option linter.longLine false`
-/
#guard_msgs in                                                                            #guard true

-- However, the *doc-string* of #guard_msgs is exempt from the linter:
-- these are automatically generated, hence linting them is not helpful.
/--
info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
-/
#guard_msgs in
#eval List.range 27

/- Tests for the `openClassical` linter -/

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.
note: this linter can be disabled with `set_option linter.openClassical false`
-/
#guard_msgs in
open Classical

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.
note: this linter can be disabled with `set_option linter.openClassical false`
-/
#guard_msgs in
open Nat Classical Nat

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.
note: this linter can be disabled with `set_option linter.openClassical false`
-/
#guard_msgs in
open Classical hiding choose

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.
note: this linter can be disabled with `set_option linter.openClassical false`
-/
#guard_msgs in
open Classical renaming choose -> foo, byCases -> bar

-- Only opening specific items.
/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.
note: this linter can be disabled with `set_option linter.openClassical false`
-/
#guard_msgs in
open Classical (choose)

-- TODO: `open scoped Classical` is also linted
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Int Classical Nat

-- `open ... in` is *not* linted.
#guard_msgs in
open Classical (choose) in
def foo : Nat := 1
