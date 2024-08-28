import Mathlib.Tactic.Linter.AssertNotExists

/-! A doc-module string -/

-- and some comments

/-! Another doc-module string -/

/- more comments -/

assert_not_exists Nats
assert_not_exists Nats
assert_not_exists Nats
assert_not_exists Nats

/--
warning: `assert_not_exists   Nats` appears too late: it can only be preceded by
`import` statements doc-module strings and other `assert_not_exists` statements.
note: this linter can be disabled with `set_option linter.style.assertNotExists false`
-/
#guard_msgs in
-- anything that is not a doc-module string or an `assert_not_exists`
-- (the `#guard_msgs in` command in this case), triggers the linter
assert_not_exists Nats
