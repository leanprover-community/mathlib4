
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace List

open Nat

/-- All elements of `fin n`, from `0` to `n-1`. The corresponding finset is `finset.univ`. -/
def finRange (n : ℕ) : List (Fin n) :=
  (range n).pmap Fin.mk fun _ => List.mem_range.1

@[simp]
theorem fin_range_zero : finRange 0 = [] :=
  rfl

@[simp]
theorem mem_fin_range {n : ℕ} (a : Fin n) : a ∈ finRange n :=
  mem_pmap.2 ⟨a.1, mem_range.2 a.2, Finₓ.eta _ _⟩

theorem nodup_fin_range (n : ℕ) : (finRange n).Nodup :=
  (nodup_range _).pmap fun _ _ _ _ => Finₓ.veq_of_eq
