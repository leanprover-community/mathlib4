module

import Mathlib.Init

set_option linter.style.numericProjection true

open Lean

structure Foo where a : Nat
structure Bar extends Foo where b : Nat

variable (r : Rat) (bar : Bar)

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.den`.

To exempt terms of type `Rat`, add `@[allow_numeric_proj]` at the declaration site of `Rat`.

Note: This linter can be disabled with `set_option linter.style.numericProjection false`
-/
#guard_msgs in
example := r.2

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjection false`
-/
#guard_msgs in
example := bar.2

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.toFoo`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjection false`
---
warning: Numeric projections are disallowed.

  [apply] Instead, use `.a`.

To exempt terms of type `Foo`, add `@[allow_numeric_proj]` at the declaration site of `Foo`.

Note: This linter can be disabled with `set_option linter.style.numericProjection false`
-/
#guard_msgs in
example := bar.1.1

structure Fn where f : Nat → Nat

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.f`.

To exempt terms of type `Fn`, add `@[allow_numeric_proj]` at the declaration site of `Fn`.

Note: This linter can be disabled with `set_option linter.style.numericProjection false`
-/
#guard_msgs in
example (g : Fn) := g.1 3

/-! The structure is the one the projection actually belongs to, found after unfolding. -/

def MyAnd (p q : Prop) : Prop := p ∧ q

#guard_msgs in
example (h : MyAnd True True) := h.2

/-! There is no named field to suggest for an `inductive` with one constructor. -/

inductive Ind | mk (x y : Nat)

#guard_msgs in
example (i : Ind) := i.2
