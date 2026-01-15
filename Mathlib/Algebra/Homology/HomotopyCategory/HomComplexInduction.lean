/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Construction of cochains by induction

Let `K` and `L` be cochain complexes in a preadditive category `C`.
We provide an API to construct a cochain in `Cochain K L d` in the following
situation. Assume that `X n : Set (Cochain K L d)` is a sequence of subsets
of `Cochain K L d`, and `φ n : X n → X (n + 1)` is a sequence of maps such
that for a certain `p₀ : ℕ` and any `x : X n`, `φ n x` and `x` coincide
up to the degree `p₀ + n`, then we construct a cochain
`InductionUp.limitSequence` in `Cochain K L d` which coincides with the
`n`th-iteration of `φ` evaluated on `x₀` up to the degree `p₀ + n` for any `n : ℕ`.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex.HomComplex.Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

/-- Given `p₀ : ℤ`, this is the condition on two cochains `α` and `β` in `Cochain K L N`
saying that `α.v p q _ = β.v p q _` when `p ≤ p₀`. -/
def EqUpTo {n : ℤ} (α β : Cochain K L n) (p₀ : ℤ) : Prop :=
  ∀ (p q : ℤ) (hpq : p + n = q), p ≤ p₀ → α.v p q hpq = β.v p q hpq

namespace InductionUp

variable {d : ℤ} {X : ℕ → Set (Cochain K L d)} (φ : ∀ (n : ℕ), X n → X (n + 1))
   {p₀ : ℤ} (hφ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n)) (x₀ : X 0)

/-- Assuming we have a sequence of subsets `X n : Set (Cochain K L d)` for all `n : ℕ`,
a sequence of maps `φ n : X n → X (n + 1)` for `n : ℕ`, and an element `x₀ : X 0`,
this is the dependent sequence in `∀ (n : ℕ), X n` obtained by evaluation iterations of `φ`
on `x₀`. -/
def sequence : ∀ n, X n
  | 0 => x₀
  | n + 1 => φ n (sequence n)

include hφ in
lemma sequence_eqUpTo (n₁ n₂ : ℕ) (h : n₁ ≤ n₂) :
    (sequence φ x₀ n₁).val.EqUpTo (sequence φ x₀ n₂).val (p₀ + n₁) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k generalizing n₁ with
  | zero => intro _ _ _ _; simp
  | succ k hk =>
    intro p q hpq hp
    rw [hk n₁ p q hpq hp, ← hφ (n₁ + k) (sequence φ x₀ (n₁ + k)) p q hpq (by lia)]
    dsimp [sequence]

/-- Assuming we have a sequence of subsets `X n : Set (Cochain K L d)` for all `n : ℕ`,
a sequence of maps `φ n : X n → X (n + 1)` for `n : ℕ`, and an element `x₀ : X 0`,
and under the assumption that for any `x : X n` the cochain `φ n x` coincides
with `x` up to the degree `p₀ + n`, this is a cochain in `Cochain K L d` which
can be understood as the "limit" of the sequence of cochains obtained by
evaluating iterations of `φ` on `x₀`. -/
@[nolint unusedArguments]
def limitSequence (_ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n)) (x₀ : X 0) :
    Cochain K L d :=
  Cochain.mk (fun p q hpq => (sequence φ x₀ (p - p₀).toNat).1.v p q hpq)

lemma limitSequence_eqUpTo (n : ℕ) :
    (limitSequence φ hφ x₀).EqUpTo (sequence φ x₀ n).1 (p₀ + n) := by
  intro p q hpq hp
  exact sequence_eqUpTo φ hφ _ _ _ (by lia) _ _ _ (by lia)

end InductionUp

end CochainComplex.HomComplex.Cochain
