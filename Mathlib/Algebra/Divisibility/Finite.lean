/-
Copyright (c) 2025 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Data.Fintype.Basic

/-!
# Divisibility in finite types
-/

variable {M : Type*} [Semigroup M]

instance [Fintype M] [DecidableEq M] (a b : M) : Decidable (a ∣ b) :=
  decidable_of_iff (∃ c, b = a * c) dvd_def

