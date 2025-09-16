/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNReal.Basic

/-!
# Finite Stochastic Matrices

The category of finite types with stochastic matrices as morphisms,
providing a concrete Markov category for probabilistic computations.

FinStoch handles real probability, unlike cartesian categories which have only
deterministic morphisms. It includes both deterministic functions (permutation matrices)
and random processes (general stochastic matrices).

A morphism `f : m → n` is a stochastic matrix where `f[i,j]` gives the probability
of transitioning from state `i` to state `j`. Composition follows the Chapman-Kolmogorov
equation, and tensor products model independent parallel processes.

## Main definitions

* `StochasticMatrix m n` - An `m × n` matrix where each row sums to 1
* `FinStoch` - The category of finite types with stochastic matrices as morphisms
* `StochasticMatrix.id` - The identity stochastic matrix
* `StochasticMatrix.comp` - Composition of stochastic matrices
* `StochasticMatrix.tensor` - Tensor product (Kronecker product) of stochastic matrices

## Implementation notes

We use row-stochastic matrices (rows sum to 1). This aligns with standard probability
notation P(j|i) and makes matrix multiplication implement the Chapman-Kolmogorov equation.

The row sum constraint is in the type, ensuring validity by construction.
We use `NNReal` for entries to prevent negative probabilities at the type level.

We bundle `Fintype` and `DecidableEq` instances with `FinStoch` objects to avoid
diamond problems in categorical constructions.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, stochastic matrix, probability, category theory
-/

namespace CategoryTheory.MarkovCategory

universe u

/-- A stochastic matrix representing a conditional probability distribution P(n|m).

Entry (i,j) gives the probability of transitioning from state i to state j.
Each row is a probability distribution over output states. -/
structure StochasticMatrix (m n : Type u) [Fintype m] [Fintype n] where
  /-- The matrix of non-negative reals -/
  toMatrix : Matrix m n NNReal
  /-- Each row sums to 1 -/
  row_sum : ∀ i : m, ∑ j : n, toMatrix i j = 1

namespace StochasticMatrix

variable {m n p : Type u} [Fintype m] [Fintype n] [Fintype p]

/-- The identity stochastic matrix, where each state transitions to itself with probability 1.

This represents the deterministic identity function; no randomness, each state
maps to itself. This is the "do nothing" transition. -/
def id (m : Type u) [Fintype m] [DecidableEq m] : StochasticMatrix m m where
  toMatrix := fun i j => if i = j then (1 : NNReal) else 0
  row_sum := fun i => by
    -- Only the diagonal entry (i,i) contributes to the sum
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [if_neg (Ne.symm hj)]
    · intro h
      exfalso
      exact h (Finset.mem_univ _)

/-- Composition of stochastic matrices corresponds to the Chapman-Kolmogorov equation:
P(Z|X) = ∑_Y P(Y|X) * P(Z|Y).

This is the key equation of Markov processes: to get from X to Z, we sum
over all possible intermediate states Y, weighting by the probability of each path.
Matrix multiplication naturally implements this sum over intermediate states. -/
def comp (f : StochasticMatrix m n) (g : StochasticMatrix n p) : StochasticMatrix m p where
  toMatrix := fun i k => ∑ j : n, f.toMatrix i j * g.toMatrix j k
  row_sum := fun i => by
    -- Key insight: summing first over outputs k, then intermediates j
    -- equals summing first over j, then k (by Fubini/sum exchange)
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    -- Both matrices are stochastic
    simp only [g.row_sum, mul_one, f.row_sum]

/-- Tensor product of stochastic matrices (Kronecker product).

Models independent parallel processes: P((Y₁,Y₂)|(X₁,X₂)) = P(Y₁|X₁) * P(Y₂|X₂). -/
def tensor {m₁ n₁ m₂ n₂ : Type u} [Fintype m₁] [Fintype n₁] [Fintype m₂] [Fintype n₂]
    (f : StochasticMatrix m₁ n₁) (g : StochasticMatrix m₂ n₂) :
    StochasticMatrix (m₁ × m₂) (n₁ × n₂) where
  toMatrix := fun ij kl => f.toMatrix ij.1 kl.1 * g.toMatrix ij.2 kl.2
  row_sum := fun ij => by
    obtain ⟨i₁, i₂⟩ := ij
    -- Sum over product = product of sums
    rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [← Finset.sum_mul_sum]
    -- Each row sums to 1
    simp only [f.row_sum i₁, g.row_sum i₂, one_mul]

@[ext]
theorem ext {f g : StochasticMatrix m n} (h : f.toMatrix = g.toMatrix) : f = g := by
  cases f
  cases g
  congr

end StochasticMatrix

/-- The category of finite types with stochastic matrices as morphisms.

Objects are finite state spaces. Morphisms are stochastic matrices.
Composition follows the Chapman-Kolmogorov equation. -/
structure FinStoch : Type (u+1) where
  carrier : Type u
  [fintype : Fintype carrier]
  [decidableEq : DecidableEq carrier]

namespace FinStoch

instance (X : FinStoch) : Fintype X.carrier := X.fintype

instance (X : FinStoch) : DecidableEq X.carrier := X.decidableEq

/-- Morphisms in FinStoch are stochastic matrices. -/
abbrev Hom (X Y : FinStoch) := StochasticMatrix X.carrier Y.carrier

instance : CategoryStruct FinStoch where
  Hom := Hom
  id X := StochasticMatrix.id X.carrier
  comp f g := StochasticMatrix.comp f g

instance : Category FinStoch where
  id_comp f := by
    apply StochasticMatrix.ext
    ext i j
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    simp only [CategoryStruct.id]
    -- Identity matrix selects row i
    rw [Finset.sum_eq_single i]
    · simp [StochasticMatrix.id, one_mul]
    · intro k _ hk
      simp [StochasticMatrix.id, zero_mul]
      intro h
      exact absurd h (Ne.symm hk)
    · intro h
      exfalso
      exact h (Finset.mem_univ _)
  comp_id f := by
    apply StochasticMatrix.ext
    ext i j
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    simp only [CategoryStruct.id]
    -- Identity matrix selects column j
    rw [Finset.sum_eq_single j]
    · simp [StochasticMatrix.id, mul_one]
    · intro k _ hk
      simp [StochasticMatrix.id, mul_zero]
      intro h
      exact absurd h.symm (Ne.symm hk)
    · intro h
      exfalso
      exact h (Finset.mem_univ _)
  assoc f g h := by
    apply StochasticMatrix.ext
    ext i k
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    -- Associativity of matrix multiplication
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    -- Interchange summation order
    rw [Finset.sum_comm]

/-- The tensor unit: a singleton type.

Represents a one-state system. Identity for tensor products. -/
def tensorUnit : FinStoch where
  carrier := Unit

/-- Tensor product of objects: the product of carrier types.

If X has m states and Y has n states, X ⊗ Y has m×n states. -/
def tensorObj (X Y : FinStoch) : FinStoch where
  carrier := X.carrier × Y.carrier

end FinStoch

end CategoryTheory.MarkovCategory
