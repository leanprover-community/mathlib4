/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Finite Stochastic Matrices

The category of finite types with stochastic matrices as morphisms.

FinStoch has both deterministic morphisms (permutation matrices) and
random processes (stochastic matrices), unlike cartesian categories.

Entry `f[i,j]` gives the probability of going from state `i` to state `j`.
Composition follows Chapman-Kolmogorov. Tensor products model independent processes.

## Main definitions

* `StochasticMatrix m n` - Matrix where each row sums to 1
* `FinStoch` - Category of finite types with stochastic matrices
* `StochasticMatrix.id` - Identity matrix
* `StochasticMatrix.comp` - Matrix composition
* `StochasticMatrix.tensor` - Kronecker product

## Implementation notes

Rows sum to 1 (row-stochastic). This matches P(j|i) notation.
Matrix multiplication implements Chapman-Kolmogorov.

Row sums enforced in the type. `NNReal` prevents negative probabilities.

`Fintype` and `DecidableEq` bundled with `FinStoch` to avoid diamonds.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, stochastic matrix, probability, category theory
-/

namespace CategoryTheory.MarkovCategory

universe u

/-- Stochastic matrix representing P(n|m).

Entry (i,j) is the probability from state i to state j. Each row sums to 1. -/
structure StochasticMatrix (m n : Type u) [Fintype m] [Fintype n] where
  /-- The matrix of non-negative reals -/
  toMatrix : Matrix m n NNReal
  /-- Each row sums to 1 -/
  row_sum : ∀ i : m, ∑ j : n, toMatrix i j = 1

namespace StochasticMatrix

variable {m n p : Type u} [Fintype m] [Fintype n] [Fintype p]

/-- Identity matrix. Each state stays in itself with probability 1. -/
def id (m : Type u) [Fintype m] [DecidableEq m] : StochasticMatrix m m where
  toMatrix := fun i j => if i = j then (1 : NNReal) else 0
  row_sum := fun i => by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [if_neg (Ne.symm hj)]
    · intro h
      exfalso
      exact h (Finset.mem_univ _)

/-- Composition via Chapman-Kolmogorov: P(Z|X) = ∑_Y P(Y|X) * P(Z|Y).

To get from X to Z, sum over all paths through Y. -/
def comp (f : StochasticMatrix m n) (g : StochasticMatrix n p) : StochasticMatrix m p where
  toMatrix := fun i k => ∑ j : n, f.toMatrix i j * g.toMatrix j k
  row_sum := fun i => by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    simp only [g.row_sum, mul_one, f.row_sum]

/-- Kronecker product. Models independent processes: P((Y₁,Y₂)|(X₁,X₂)) = P(Y₁|X₁) * P(Y₂|X₂). -/
def tensor {m₁ n₁ m₂ n₂ : Type u} [Fintype m₁] [Fintype n₁] [Fintype m₂] [Fintype n₂]
    (f : StochasticMatrix m₁ n₁) (g : StochasticMatrix m₂ n₂) :
    StochasticMatrix (m₁ × m₂) (n₁ × n₂) where
  toMatrix := fun ij kl => f.toMatrix ij.1 kl.1 * g.toMatrix ij.2 kl.2
  row_sum := fun ij => by
    obtain ⟨i₁, i₂⟩ := ij
    rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [← Finset.sum_mul_sum]
    simp only [f.row_sum i₁, g.row_sum i₂, one_mul]

@[ext]
theorem ext {f g : StochasticMatrix m n} (h : f.toMatrix = g.toMatrix) : f = g := by
  cases f
  cases g
  congr

end StochasticMatrix

/-- Category of finite types with stochastic matrices as morphisms. -/
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
    -- Identity selects row i
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
    -- Identity selects column j
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
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]

/-- Tensor unit. A singleton type. -/
def tensorUnit : FinStoch where
  carrier := Unit

/-- Tensor product. If X has m states and Y has n states, X ⊗ Y has m×n states. -/
def tensorObj (X Y : FinStoch) : FinStoch where
  carrier := X.carrier × Y.carrier


end FinStoch

end CategoryTheory.MarkovCategory
