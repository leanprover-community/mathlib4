
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace List

open Nat

@[simp]
theorem mem_range' {m : ℕ} : ∀ {s n : ℕ}, m ∈ range' s n ↔ s ≤ m ∧ m < s + n
  | s, 0 => (false_iff _).2 fun ⟨H1, H2⟩ => not_le_of_lt H2 H1
  | s, succ n =>
    have : m = s → m < s + n + 1 := fun e => e ▸ lt_succ_of_le (Nat.le_add_right _ _)
    have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m := by
      simpa only [eq_comm] using (@Decidable.le_iff_eq_or_lt _ _ _ s m).symm
    (mem_cons_iff _ _ _).trans <| by
      simp only [mem_range', or_and_distrib_left, or_iff_right_of_imp this, l, add_right_commₓ] <;> rfl

theorem range_core_range' : ∀ s n : ℕ, rangeCore s (range' s n) = range' 0 (n + s)
  | 0, n => rfl
  | s + 1, n => by
    rw [show n + (s + 1) = n + 1 + s from add_right_commₓ n s 1] <;> exact range_core_range' s (n + 1)

theorem range_eq_range' (n : ℕ) : range n = range' 0 n :=
  (range_core_range' n 0).trans <| by
    rw [zero_add]

@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range', Nat.zero_leₓ, true_andₓ, zero_addₓ]

/-- All elements of `fin n`, from `0` to `n-1`. The corresponding finset is `finset.univ`. -/
def finRange (n : ℕ) : List (Fin n) :=
  (range n).pmap Fin.mk fun _ => mem_range.1

@[simp]
theorem fin_range_zero : finRange 0 = [] :=
  rfl

@[simp]
theorem mem_fin_range {n : ℕ} (a : Fin n) : a ∈ finRange n :=
  mem_pmap.2 ⟨a.1, mem_range.2 a.2, Fin.eta _ _⟩

theorem nodup_fin_range (n : ℕ) : (finRange n).Nodup :=
  (nodup_range _).pmap fun _ _ _ _ => Fin.veq_of_eq
