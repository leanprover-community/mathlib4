/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.Order.Basic
import Mathlib.Data.Finite.Basic

/-!
# Fixed points of function `f` with `f(x) ≥ x`

In this file we consider the fixed points of function `f : α → α` with `f(x) ≥ x`. If `α` is
a finite type, then the sequence `x, f(x), f(f(x)), ...` will eventually be a constant.

# Main definitions
* `fixedPointIndex`: The smallest `n` such that the sequence `x, f(x), f(f(x)), ...`
  becomes a constant after this index.
* `eventuallyValue`: The value that the sequence converges to after sufficient number
  of iterations of `f` on `x`.
-/
namespace Function

variable {α : Type*} [PartialOrder α] [Fintype α] {f : α → α} (hf : ∀ x, x ≤ f x)

/-- If `x` is a fixed point of `f`, then the nᵗʰ iteration of `f` on `x` is `x`. -/
lemma iterate_fixed_point {x : α} (hx : IsFixedPt f x) (n : ℕ) : f^[n] x = x := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [add_comm, iterate_add_apply]
    simpa [ih] using hx

/-- If `f^[m + 1] x = f^[m] x`, then the sequence `n ↦ f^[n] x` is constant after index `m`. -/
lemma iterate_fixed_point_from_index
    {m n : ℕ} {x : α} (hx : f^[m + 1] x = f^[m] x) (hn : n ≥ m) : f^[n] x = f^[m] x := by
  rw [add_comm, iterate_add_apply] at hx
  rw [show n = n - m + m by omega, iterate_add_apply]
  apply iterate_fixed_point hx

/-- Monotonicity of `n ↦ f^[n] x`. -/
lemma monotone_iterate (x : α) : Monotone (fun n => f^[n] x) := by
  intro i j le
  simp only
  induction j with
  | zero => simp at le; rw [le]
  | succ k ih =>
    replace le : i ≤ k ∨ i = k + 1 := by omega
    cases' le with le le
    · rw [add_comm, iterate_add_apply _ 1 k]
      exact (ih le).trans (hf _)
    · rw [le]

/-- The theorem states that the iteration will eventually become a constant. -/
lemma eventually_constant_iterate (x : α) :
    ∃ n, ∀ m ≥ n, f^[m] x = f^[n] x := by
  obtain ⟨m, n, h₁, h₂⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => f^[n] x)
  use min m n
  intro n' hn'
  have eq : f^[min m n] x = f^[min m n + 1] x := by
    have ineq₁ : f^[min m n] x ≤ f^[min m n + 1] x := by
      apply monotone_iterate hf
      omega
    have ineq₂ : f^[min m n + 1] x ≤ f^[max m n] x := by
      apply monotone_iterate hf
      dsimp; omega
    replace h₂ : f^[min m n] x = f^[max m n] x := by
      by_cases h : m <= n
      · simpa [h]
      · replace h : n ≤ m := by omega
        simp [h]
        exact h₂.symm
    exact le_antisymm ineq₁ (h₂ ▸ ineq₂)
  exact iterate_fixed_point_from_index eq.symm hn'

/-- The index at which the iteration sequence of `f` on `x` starts to become constant. -/
noncomputable def fixedPointIndex (x : α) : ℕ := (eventually_constant_iterate hf x).choose

lemma fixedPointIndex_spec (x : α) :
    ∀ m ≥ fixedPointIndex hf x, f^[m] x = f^[fixedPointIndex hf x] x :=
  (eventually_constant_iterate hf x).choose_spec

/-- The eventual value of iteration of `f` on `x`. -/
noncomputable def eventualValue (x : α) := f^[fixedPointIndex hf x] x

/-- The eventual value is a fixed point of `f`. -/
lemma fixed_eventualValue (x : α) : IsFixedPt f (eventualValue hf x) := by
  unfold IsFixedPt
  simp only [eventualValue, ← iterate_succ_apply']
  apply fixedPointIndex_spec
  simp

/-- The eventual value is larger or equal than `x` itself. -/
lemma self_le_eventualValue (x : α) : x ≤ eventualValue hf x := by
  simp only [eventualValue]
  conv_lhs => rw [show x = f^[0] x from rfl]
  apply monotone_iterate hf
  simp

end Function
