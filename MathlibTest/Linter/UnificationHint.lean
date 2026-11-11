module

import Mathlib.Tactic.Linter.UnificationHint

/-! Tests for the `unificationHint` linter. -/

/-- The type of functions from `α` to `β`, behind a definition. -/
@[expose] public def Arrow (α β : Type) : Type := α → β

/-- A correct hint: `Arrow α β` is `α → β`. -/
unif_hint arrow_eq (α α' β β' : Type) where
  α ≟ α'
  β ≟ β' ⊢
  Arrow α β ≟ (α' → β')

-- A correct anonymous hint without constraints.
unif_hint (α : Type) where ⊢ Arrow α α ≟ (α → α)

/-- A reversed hint, which `unif_hint` accepts by identifying `α` and `β`. -/
unif_hint arrow_eq_reversed (α α' β β' : Type) where
  α ≟ α'
  β ≟ β' ⊢
  Arrow α β ≟ (β' → α')

/-- A hint that holds only under its constraint `List α ≟ List β`, which is not solved by
substitution. -/
unif_hint arrow_eq_of_list (α β : Type) where
  List α ≟ List β ⊢
  Arrow α β ≟ (α → α)

namespace Scoped

/-- A reversed hint registered in the namespace `Scoped`, which is closed when the linter runs. -/
scoped unif_hint arrow_eq_reversed (α α' β β' : Type) where
  α ≟ α'
  β ≟ β' ⊢
  Arrow α β ≟ (β' → α')

end Scoped

/--
error: -- Found 3 errors in 5 declarations (plus 1 automatically generated ones) in the current file with 1 linters

/- The `unificationHint` linter reports:
FOUND UNIFICATION HINTS WHOSE TWO SIDES ARE NOT DEFINITIONALLY EQUAL.
This linter can be disabled with `@[nolint unificationHint]`. -/
#check arrow_eq_reversed /- once its constraints are solved by substitution, its two sides
  Arrow α β
and
  β → α
are not definitionally equal. -/
#check arrow_eq_of_list /- once its constraints are solved by substitution, its two sides
  Arrow α β
and
  α → α
are not definitionally equal.
The check leaves out the constraints not solved by substitution: `List α ≟ List β`. -/
#check Scoped.arrow_eq_reversed /- once its constraints are solved by substitution, its two sides
  Arrow α β
and
  β → α
are not definitionally equal. -/
-/
#guard_msgs in
#lint only unificationHint
