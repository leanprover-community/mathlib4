/-
Copyright (c) 2024 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Variable

/-!
# Vector spaces

This file provides `VectorSpace` as a simple alias for a module over a field using the
`variable_alias` attribute.
-/

/-- A vector space is a module over a field. -/
@[variable_alias]
structure VectorSpace (k V : Type*)
  [Field k] [AddCommGroup V] [Module k V]

/-- If 𝔽 is a field, 𝔽^n is a vector space over 𝔽. -/
example {𝔽 : Type*} [Field 𝔽] {n : ℕ} : VectorSpace 𝔽 (Fin n → 𝔽) := {}
