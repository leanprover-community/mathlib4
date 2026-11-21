module

meta import Mathlib.Algebra.Group.WithOne.Defs
meta import Mathlib.Order.TypeTags
meta import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
Tests that the `Repr` instances of `WithBot`, `WithTop`, `WithOne`, `WithZero`, and `OnePoint`
parenthesize their argument (#45767).
-/

#guard reprStr (⊥ : WithBot ℤ) = "⊥"
#guard reprStr (⊤ : WithTop ℤ) = "⊤"
#guard reprStr (1 : WithOne ℤ) = "1"
#guard reprStr (0 : WithZero ℤ) = "0"
#guard reprStr (OnePoint.infty : OnePoint ℤ) = "∞"
#guard reprStr ((3 : ℕ) : WithTop ℕ) = "↑3"
#guard reprStr ((-1 : ℤ) : WithBot ℤ) = "↑(-1)"
#guard reprStr ((-1 : ℤ) : WithTop ℤ) = "↑(-1)"
#guard reprStr ((some 3 : Option ℕ) : WithTop (Option ℕ)) = "↑(some 3)"
#guard reprStr (((-1 : ℤ) : WithBot ℤ) : WithTop (WithBot ℤ)) = "↑↑(-1)"
#guard reprStr (some ((-1 : ℤ) : WithTop ℤ)) = "some ↑(-1)"
#guard reprStr ((-1 : ℤ) : WithOne ℤ) = "↑(-1)"
#guard reprStr ((-1 : ℤ) : WithZero ℤ) = "↑(-1)"
#guard reprStr ((-1 : ℤ) : OnePoint ℤ) = "↑(-1)"
