/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Monoid.Defs

/-!

# General Valued Constraint Satisfaction Problems

-/

/-- Type of functions `α^n → β` for a general arity `n : ℕ` -/
def ofArity (α β : Type _) : ℕ → Type
| 0   => β
| n+1 => α → ofArity α β n

/-- A template for a valued CSP problem with costs in `C` which is usually `ℚ≥0` -/
structure ValuedCspTemplate (C : Type) [LinearOrderedAddCommMonoid C] where
  D : Type                           -- Domain of "labels"
  F : Set (Σ (k : ℕ), ofArity D C k) -- Cost functions `D^k → C` for any `k`
