/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.RingTheory.Coalgebra.Convolution

import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The convolution intrinsic star ring on `n → R`

We show what the convolutive ring on a matrix looks like. In particular:
* `Matrix.toLin'_hadamard_eq_convMul`:
  the convolutive product corresponds to the Hadamard product
* `LinearMap.toMatrix'_convOne`: the convolutive unit `1` corresponds to the matrix of all
  `1`s
* `Matrix.id_convMul_toLin'_eq_zero_iff`, `Matrix.id_convMul_toLin'_eq_one_iff`:
  a diagonal of a matrix `A` is `0` (resp., `1`) iff `id * A.toLin' = 0` (resp., `= id`)

As a result, we get that a matrix `A` is an adjacency matrix iff its linear map is
convolutively idempotent, has its intrinsic star equal to its adjoint,
and has `id * A.toLin' = 0`.
With the complete simple graph corresponding to `1 - id`.
(See `Matrix.isAdjMatrix_iff_toLin'`.)

These properties (i.e., convolutively idempotent, `id * f = 0` or `= id`, and `star f = f.adjoint`)
are properties of a "quantum adjacency matrix operator," thus showing that a classical finite
adjacency matrix operator is a quantum adjacency matrix operator.

## TODO:

* relate everything to definitions of non-commutative graphs later when we introduce it

## References

* [Daws, *Quantum graphs: different perspectives, homomorphisms and quantum automorphisms*]
  [daws2024]

## Tags

finite pi coalgebra, non-commutative graph, quantum graph, quantum adjacency matrix
-/

public section

open TensorProduct LinearMap Coalgebra Matrix Pi
open scoped ConvolutionProduct IntrinsicStar

-- This ensures that we always take the convolution product in this file when we write `*` and
-- the convolution unit when we write `1`.
attribute [-instance] Module.End.instOne Module.End.instMul Module.End.instSemiring
  Module.End.instMonoid Module.End.instRing in
section

variable {R R' m n : Type*} [CommSemiring R] [CommRing R'] [Fintype n] [DecidableEq n]
  (G : SimpleGraph n) [DecidableRel G.Adj]

/-- The convolutive product corresponds to the Hadamard product. -/
@[simp] theorem LinearMap.toMatrix'_convMul_eq_hadamard (f g : (n → R) →ₗ[R] m → R) :
    (f * g).toMatrix' = f.toMatrix' ⊙ g.toMatrix' := by ext; simp

@[simp] theorem Matrix.toLin'_hadamard_eq_convMul (A B : Matrix m n R) :
    (A ⊙ B).toLin' = A.toLin' * B.toLin' := by simp [← toMatrix'.injective.eq_iff]

theorem LinearMap.ConvolutionProduct.isIdempotentElem_iff_toMatrix' {f : (n → R) →ₗ[R] m → R} :
    IsIdempotentElem f ↔ ∀ i j, IsIdempotentElem (f.toMatrix' i j) := by
  simp [IsIdempotentElem, ← toMatrix'.injective.eq_iff, hadamard_self_eq_self_iff]

variable (K) in
/-- A simple finite graph is idempotent with respect to the convolutive product. -/
@[simp] theorem SimpleGraph.convolutionProduct_isIdempotentElem_toLin'_adjMatrix
    [IsLeftCancelMulZero R] : IsIdempotentElem (G.adjMatrix R).toLin' := by
  aesop (add simp [IsIdempotentElem, hadamard_self_eq_self_iff])

/-- The matrix of the convolutive unit is all `1`s. -/
@[simp] theorem LinearMap.toMatrix'_convOne :
    (1 : (n → R) →ₗ[R] m → R).toMatrix' = .of fun _ _  ↦ 1 := by simp [counit, ← ext_iff]

@[simp] theorem Matrix.toLin'_of_one : (of fun _ _ ↦ 1 : Matrix m n R).toLin' = 1 := by aesop

variable (n R') in
/-- The matrix of `1 - id` is exactly the adjacency matrix of `SimpleGraph.completeGraph`. -/
@[simp] theorem SimpleGraph.toMatrix'_convOne_sub_id_eq_adjMatrix_completeGraph :
    toMatrix' (1 - .id) = (completeGraph n).adjMatrix R' := by aesop

variable (n R') in
@[simp] theorem SimpleGraph.toLin'_adjMatrix_completeGraph :
    ((completeGraph n).adjMatrix R').toLin' = 1 - .id := by
  simp [← toMatrix'_convOne_sub_id_eq_adjMatrix_completeGraph, -toMatrix'_convOne]

variable (R) in
@[simp] theorem SimpleGraph.id_convMul_toLin'_adjMatrix_eq_zero :
    .id * (G.adjMatrix R).toLin' = 0 := by simp [← toMatrix'.injective.eq_iff]

variable (R) in
@[simp] theorem SimpleGraph.toLin'_convMul_id_adjMatrix_eq_zero :
    (G.adjMatrix R).toLin' * .id = 0 := by simp [← toMatrix'.injective.eq_iff]

/-- All linear maps on euclidean spaces are intrinsically self-adjoint if they are
convolutively idempotent. -/
theorem LinearMap.ConvolutionProduct.IsIdempotentElem.intrinsicStar_isSelfAdjoint
    [IsLeftCancelMulZero R] [StarRing R]
    {f : (n → R) →ₗ[R] m → R} (hf : IsIdempotentElem f) : IsSelfAdjoint f := by
  classical
  simp_rw [ConvolutionProduct.isIdempotentElem_iff_toMatrix',
    IsIdempotentElem.iff_eq_zero_or_one] at hf
  rw [IsSelfAdjoint, ← toMatrix'.injective.eq_iff]
  ext i j
  obtain (h | h) := hf i j <;> simp_all

open ConvolutionProduct in
variable (R) in
/-- A simple graph is intrinisically self-adjoint. -/
@[simp] theorem SimpleGraph.intrinsicStar_isSelfAdjoint_toLin'_adjMatrix [StarRing R] :
    IsSelfAdjoint (G.adjMatrix R).toLin' := by ext; aesop

/-- A matrix `A` is an adjacency matrix iff its linear map is convolutively
idempotent, its intrinsic star is equal to the conjugate transpose,
and its convolutive product with `id` is `0`. -/
theorem Matrix.isAdjMatrix_iff_toLin' [IsLeftCancelMulZero R] {A : Matrix n n R} [StarRing R] :
    A.IsAdjMatrix ↔ IsIdempotentElem A.toLin' ∧
      star A.toLin' = (star A).toLin' ∧ .id * A.toLin' = 0 := by
  rw [isAdjMatrix_iff_hadamard, ← isSymm_iff_intrinsicStar_toLin',
    ConvolutionProduct.isIdempotentElem_iff_toMatrix', ← toMatrix'.injective.eq_iff]
  simp [hadamard_self_eq_self_iff, one_hadamard_eq_zero_iff]

end
