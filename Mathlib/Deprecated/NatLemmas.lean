/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Batteries.Data.Nat.Lemmas
import Mathlib.Util.AssertExists
import Mathlib.Data.Nat.Notation

/-!
# Note about deprecated files

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.
-/

assert_not_exists Preorder

universe u

namespace Nat

/-! multiplication -/

@[deprecated (since := "2024-08-23")] alias ⟨eq_zero_of_mul_eq_zero, _⟩ := mul_eq_zero

-- TODO: there are four variations, depending on which variables we assume to be nonneg

/-! successor and predecessor -/

@[deprecated "No deprecation message was provided." (since := "2024-08-23")]
def discriminate {B : Sort u} {n : ℕ} (H1 : n = 0 → B) (H2 : ∀ m, n = succ m → B) : B := by
  induction n with
  | zero => exact H1 rfl
  | succ n _ => apply H2 _ rfl

end Nat
