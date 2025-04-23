import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib

open Nat

theorem gould_aux (n k : ℕ) :
    Finset.gcd {(n + 1).choose (k + 2), (n + 2).choose (k + 1), n.choose k} ((↑) : ℕ → ℤ) ∣
      Finset.gcd {(n + 2).choose (k + 2), n.choose (k + 1), (n + 1).choose k} ((↑) : ℕ → ℤ) := by
  simp only [Finset.dvd_gcd_iff, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    id_eq, forall_eq]
  refine ⟨?_, ?_, ?_⟩
  · have : ((n + 2).choose (k + 2) : ℤ) =
        (n.choose k) * (- (n + 1)) + ((n + 1).choose (k + 2)) * (- (k + 1)) +
          (n + 2).choose (k + 1) * (n - k + 1) := by
      sorry
    done
