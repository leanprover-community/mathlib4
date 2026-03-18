/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Formalization of IMO 1987, Q1

Let $p_{n, k}$ be the number of permutations of a set of cardinality `n ≥ 1` that fix exactly `k`
elements. Prove that $∑_{k=0}^n k p_{n,k}=n!$.

To prove this identity, we show that both sides are equal to the cardinality of the set
`{(x : α, σ : Perm α) | σ x = x}`, regrouping by `card (fixedPoints σ)` for the left-hand side and
by `x` for the right-hand side.

The original problem assumes `n ≥ 1`. It turns out that a version with `n * (n - 1)!` in the RHS
holds true for `n = 0` as well, so we first prove it, then deduce the original version in the case
`n ≥ 1`. -/

variable (α : Type*) [Fintype α] [DecidableEq α]

open scoped Nat

open Equiv Fintype Function

open Finset (range sum_const)

open Set (Iic)

namespace Imo1987Q1

/-- The set of pairs `(x : α, σ : Perm α)` such that `σ x = x` is equivalent to the set of pairs
`(x : α, σ : Perm {x}ᶜ)`. -/
def fixedPointsEquiv : { σx : α × Perm α // σx.2 σx.1 = σx.1 } ≃ Σ x : α, Perm ({x}ᶜ : Set α) :=
  calc
    { σx : α × Perm α // σx.2 σx.1 = σx.1 } ≃ Σ x : α, { σ : Perm α // σ x = x } :=
      setProdEquivSigma _
    _ ≃ Σ x : α, { σ : Perm α // ∀ y : ({x} : Set α), σ y = Equiv.refl (↥({x} : Set α)) y } :=
      (sigmaCongrRight fun x => Equiv.setCongr <| by simp only [SetCoe.forall]; simp)
    _ ≃ Σ x : α, Perm ({x}ᶜ : Set α) := sigmaCongrRight fun x => by apply Equiv.Set.compl

theorem card_fixed_points :
    card { σx : α × Perm α // σx.2 σx.1 = σx.1 } = card α * (card α - 1)! := by
  simp only [card_congr (fixedPointsEquiv α), card_sigma, card_perm]
  have (x : _) : ({x}ᶜ : Set α) = Finset.filter (· ≠ x) Finset.univ := by
    ext; simp
  simp [this]

/-- Given `α : Type*` and `k : ℕ`, `fiber α k` is the set of permutations of `α` with exactly `k`
fixed points. -/
def fiber (k : ℕ) : Set (Perm α) :=
  {σ : Perm α | card (fixedPoints σ) = k}

instance {k : ℕ} : Fintype (fiber α k) := by unfold fiber; infer_instance

@[simp]
theorem mem_fiber {σ : Perm α} {k : ℕ} : σ ∈ fiber α k ↔ card (fixedPoints σ) = k :=
  Iff.rfl

/-- `p α k` is the number of permutations of `α` with exactly `k` fixed points. -/
def p (k : ℕ) :=
  card (fiber α k)

/-- The set of triples `(k ≤ card α, σ ∈ fiber α k, x ∈ fixedPoints σ)` is equivalent
to the set of pairs `(x : α, σ : Perm α)` such that `σ x = x`. The equivalence sends
`(k, σ, x)` to `(x, σ)` and `(x, σ)` to `(card (fixedPoints σ), σ, x)`.

It is easy to see that the cardinality of the LHS is given by
`∑ k : Fin (card α + 1), k * p α k`. -/
def fixedPointsEquiv' :
    (Σ (k : Fin (card α + 1)) (σ : fiber α k), fixedPoints σ.1) ≃
      { σx : α × Perm α // σx.2 σx.1 = σx.1 } where
  toFun p := ⟨⟨p.2.2, p.2.1⟩, p.2.2.2⟩
  invFun p :=
    ⟨⟨card (fixedPoints p.1.2), (card_subtype_le _).trans_lt (Nat.lt_succ_self _)⟩, ⟨p.1.2, rfl⟩,
      ⟨p.1.1, p.2⟩⟩
  left_inv := fun ⟨⟨k, hk⟩, ⟨σ, hσ⟩, ⟨x, hx⟩⟩ => by
    simp only [mem_fiber] at hσ
    subst k; rfl
  right_inv := fun ⟨⟨x, σ⟩, h⟩ => rfl

/-- Main statement for any `(α : Type*) [Fintype α]`. -/
theorem main_fintype : ∑ k ∈ range (card α + 1), k * p α k = card α * (card α - 1)! := by
  have A : ∀ (k) (σ : fiber α k), card (fixedPoints (↑σ : Perm α)) = k := fun k σ => σ.2
  simpa [A, ← Fin.sum_univ_eq_sum_range, -card_ofFinset, Finset.card_univ, card_fixed_points,
    mul_comm] using card_congr (fixedPointsEquiv' α)

/-- Main statement for permutations of `Fin n`, a version that works for `n = 0`. -/
theorem main₀ (n : ℕ) : ∑ k ∈ range (n + 1), k * p (Fin n) k = n * (n - 1)! := by
  simpa using main_fintype (Fin n)

/-- Main statement for permutations of `Fin n`. -/
theorem main {n : ℕ} (hn : 1 ≤ n) : ∑ k ∈ range (n + 1), k * p (Fin n) k = n ! := by
  rw [main₀, Nat.mul_factorial_pred (Nat.one_le_iff_ne_zero.mp hn)]

end Imo1987Q1
