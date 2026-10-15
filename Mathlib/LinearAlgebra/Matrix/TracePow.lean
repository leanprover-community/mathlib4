import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace of powers of products

This file contains trace identities for powers of products of rectangular matrices.
-/

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R]

/-- The trace of a positive power of `A * B` is unchanged when the factors are reversed.

This extends `trace_mul_comm` to positive powers, including rectangular matrices `A` and `B`.
The exponent is positive because the statement need not hold at exponent zero when the index
types have different cardinalities.
-/
theorem trace_mul_pow_comm (A : Matrix m n R) (B : Matrix n m R) (k : ℕ) :
    trace ((A * B) ^ (k + 1)) = trace ((B * A) ^ (k + 1)) := by
  have hpow : ∀ k : ℕ, (B * A) ^ (k + 1) = B * (A * B) ^ k * A := by
    intro k
    induction k with
    | zero =>
        simp [mul_assoc]
    | succ k ih =>
        calc
          (B * A) ^ (Nat.succ k + 1) = (B * A) ^ (k + 1) * (B * A) := by
            congr 1
            omega
          _ = (B * (A * B) ^ k * A) * (B * A) := by rw [ih]
          _ = B * ((A * B) ^ k * (A * B)) * A := by
            simpa only [mul_assoc]
          _ = B * (A * B) ^ (k + 1) * A := by
            rw [pow_succ]
  calc
    trace ((A * B) ^ (k + 1)) = trace ((A * B) ^ k * A * B) := by
      rw [pow_succ]
      congr 1
      exact (mul_assoc ((A * B) ^ k) A B).symm
    _ = trace (B * (A * B) ^ k * A) := Matrix.trace_mul_cycle _ _ _
    _ = trace ((B * A) ^ (k + 1)) := by rw [← hpow k]

end Matrix
