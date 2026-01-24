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

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
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

variable {R R' K m n : Type*} [CommSemiring R] [CommRing R'] [Field K] [Fintype n] [DecidableEq n]
  (G : SimpleGraph n) [DecidableRel G.Adj]

theorem Pi.intrinsicStar_comul [StarRing R] {A : n → Type*} [Π i, AddCommMonoid (A i)]
    [Π i, Module R (A i)] [Π i, CoalgebraStruct R (A i)] [Π i, StarAddMonoid (A i)]
    [∀ i, StarModule R (A i)]
    (h : ∀ i, star (comul (R := R) (A := A i)) = TensorProduct.comm R (A i) (A i) ∘ₗ comul) :
    star (comul (R := R) (A := Π i, A i)) =
      TensorProduct.comm R (Π i, A i) (Π i, A i) ∘ₗ comul := by
  ext i x
  have := by simpa using congr($(h i) x)
  simp [star_map_apply_eq_map_intrinsicStar, this, map_comm]

@[simp] theorem Pi.intrinsicStar_comul_commSemiring [StarRing R] :
    star (comul (R := R) (A := n → R)) = TensorProduct.comm R (n → R) (n → R) ∘ₗ comul :=
  intrinsicStar_comul fun _ ↦ by ext; simp

/-- The convolutive product corresponds to the Hadamard product. -/
@[simp] theorem LinearMap.toMatrix'_convMul_eq_hadamard (f g : (n → R) →ₗ[R] m → R) :
    (f * g).toMatrix' = f.toMatrix' ⊙ g.toMatrix' := by ext; simp

@[simp] theorem Matrix.toLin'_hadamard_eq_convMul (A B : Matrix m n R) :
    (A ⊙ B).toLin' = A.toLin' * B.toLin' := by simp [← toMatrix'.injective.eq_iff]

/-- A linear map is convolutively idempotent iff its matrix is all `1`s and `0`s. -/
theorem LinearMap.ConvolutionProduct.isIdempotentElem_iff {f : (n → K) →ₗ[K] m → K} :
    IsIdempotentElem f ↔ ∀ i j, f.toMatrix' i j = 0 ∨ f.toMatrix' i j = 1 := by
  rw [IsIdempotentElem, ← toMatrix'.injective.eq_iff, toMatrix'_convMul_eq_hadamard]
  simp only [← ext_iff, hadamard_apply, ← sub_eq_zero (b := toMatrix' _ _ _),
    ← mul_sub_one, mul_eq_zero, sub_eq_zero]

/-- A matrix's linear map is convolutively idempotent iff it is all `1`s and `0`s. -/
theorem Matrix.ConvolutionProduct.isIdempotentElem_toLin'_iff {A : Matrix m n K} :
    IsIdempotentElem A.toLin' ↔ ∀ i j, A i j = 0 ∨ A i j = 1 := by
  simp only [ConvolutionProduct.isIdempotentElem_iff, toMatrix'_toLin']

variable (K) in
/-- A simple finite graph is idempotent with respect to the convolutive product. -/
@[simp] theorem SimpleGraph.convolutionProduct_isIdempotentElem_toLin'_adjMatrix :
    IsIdempotentElem (G.adjMatrix K).toLin' := by
  grind [ConvolutionProduct.isIdempotentElem_toLin'_iff, adjMatrix_apply]

/-- The matrix of the convolutive unit is all `1`s. -/
@[simp] theorem LinearMap.toMatrix'_convOne :
    (1 : (n → R) →ₗ[R] m → R).toMatrix' = .of fun _ _  ↦ 1 := by simp [counit, ← ext_iff]

variable (n R') in
/-- The matrix of `1 - id` is exactly the adjacency matrix of `SimpleGraph.completeGraph`. -/
@[simp] theorem SimpleGraph.toMatrix'_convOne_sub_id_eq_adjMatrix_completeGraph :
    toMatrix' (1 - .id) = (completeGraph n).adjMatrix R' := by aesop

variable (n R') in
@[simp] theorem SimpleGraph.toLin'_adjMatrix_completeGraph :
    ((completeGraph n).adjMatrix R').toLin' = 1 - .id := by
  simp [← toMatrix'_convOne_sub_id_eq_adjMatrix_completeGraph, -toMatrix'_convOne]

theorem LinearMap.id_convMul_eq_zero_iff_diag_toMatrix'_eq_zero
    {f : (n → R) →ₗ[R] n → R} : .id * f = 0 ↔ f.toMatrix'.diag = 0 := by
  rw [← toMatrix'.injective.eq_iff, toMatrix'_convMul_eq_hadamard]
  simp [one_hadamard, ← ext_iff, diagonal_apply, funext_iff]

theorem LinearMap.convMul_id_eq_zero_iff_diag_toMatrix'_eq_zero
    {f : (n → R) →ₗ[R] n → R} : f * .id = 0 ↔ f.toMatrix'.diag = 0 := by
  rw [← toMatrix'.injective.eq_iff, toMatrix'_convMul_eq_hadamard]
  simp [hadamard_one, ← ext_iff, diagonal_apply, funext_iff]

theorem LinearMap.id_convMul_eq_id_iff_diag_toMatrix'_eq_one
    {f : (n → R) →ₗ[R] n → R} : .id * f = .id ↔ f.toMatrix'.diag = 1 := by
  rw [← toMatrix'.injective.eq_iff, toMatrix'_convMul_eq_hadamard]
  simp only [toMatrix'_id, one_hadamard, toMatrix'_apply, ← ext_iff, diagonal_apply,
    Matrix.one_apply, funext_iff, diag_apply, Pi.one_apply]
  exact ⟨fun h i ↦ by simpa using h i i, by grind⟩

theorem LinearMap.convMul_id_eq_id_iff_diag_toMatrix'_eq_one
    {f : (n → R) →ₗ[R] n → R} : f * .id = .id ↔ f.toMatrix'.diag = 1 := by
  rw [← toMatrix'.injective.eq_iff, toMatrix'_convMul_eq_hadamard]
  simp only [toMatrix'_id, hadamard_one, toMatrix'_apply, ← ext_iff, diagonal_apply,
    Matrix.one_apply, funext_iff, diag_apply, Pi.one_apply]
  exact ⟨fun h i ↦ by simpa using h i i, by grind⟩

/-- `id * A.toLin' = 0` iff the diagonal of the matrix is all `0`s,
where `*` is the convolutive product. -/
theorem Matrix.id_convMul_toLin'_eq_zero_iff {A : Matrix n n R} :
    .id * A.toLin' = 0 ↔ A.diag = 0 := by
  simp [id_convMul_eq_zero_iff_diag_toMatrix'_eq_zero]

theorem Matrix.toLin'_convMul_id_eq_zero_iff {A : Matrix n n R} :
    A.toLin' * .id = 0 ↔ A.diag = 0 := by
  simp [convMul_id_eq_zero_iff_diag_toMatrix'_eq_zero]

/-- `id * A.toLin' = id` iff the diagonal of `A` is all `1`s,
where `*` is the convolutive product. -/
theorem Matrix.id_convMul_toLin'_eq_id_iff {A : Matrix n n R} :
    .id * A.toLin' = .id ↔ A.diag = 1 := by
  simp [id_convMul_eq_id_iff_diag_toMatrix'_eq_one]

theorem Matrix.toLin'_convMul_id_eq_id_iff {A : Matrix n n R} :
    A.toLin' * .id = .id ↔ A.diag = 1 := by
  simp [convMul_id_eq_id_iff_diag_toMatrix'_eq_one]

variable (R) in
@[simp] theorem SimpleGraph.id_convMul_toLin'_adjMatrix_eq_zero :
    .id * (G.adjMatrix R).toLin' = 0 := by
  simp [id_convMul_toLin'_eq_zero_iff, funext_iff]

variable (R) in
@[simp] theorem SimpleGraph.toLin'_convMul_id_adjMatrix_eq_zero :
    (G.adjMatrix R).toLin' * .id = 0 := by
  simp [toLin'_convMul_id_eq_zero_iff, funext_iff]

/-- All linear maps on euclidean spaces are intrinsically self-adjoint if they are
convolutively idempotent. -/
theorem LinearMap.ConvolutionProduct.IsIdempotentElem.intrinsicStar_isSelfAdjoint [StarRing K]
    {f : (n → K) →ₗ[K] m → K} (hf : IsIdempotentElem f) : IsSelfAdjoint f := by
  classical
  rw [ConvolutionProduct.isIdempotentElem_iff] at hf
  rw [IsSelfAdjoint, ← toMatrix'.injective.eq_iff]
  ext i j
  obtain (h | h) := hf i j <;> simp_all

open ConvolutionProduct in
variable (R) in
/-- A simple graph is intrinisically self-adjoint. -/
@[simp] theorem SimpleGraph.intrinsicStar_isSelfAdjoint_toLin'_adjMatrix [StarRing R] :
    IsSelfAdjoint (G.adjMatrix R).toLin' := by ext; aesop

/-- A matrix is symmetric if the intrinsic star of its linear map is equal to the
conjugate transpose. -/
theorem Matrix.isSymm_iff_intrinsicStar_toLin' {A : Matrix n n R} [StarRing R] :
    A.IsSymm ↔ star A.toLin' = (star A).toLin' := by
  rw [intrinsicStar_toLin', toLin'.injective.eq_iff, ← transpose_conjTranspose,
    star_eq_conjTranspose, conjTranspose_inj, IsSymm]

/-- A matrix `A` is an adjacency matrix iff its linear map is convolutively
idempotent, its intrinsic star is equal to the conjugate transpose,
and its convolutive product with `id` is `0`. -/
theorem Matrix.isAdjMatrix_iff_toLin' {A : Matrix n n K} [StarRing K] :
    A.IsAdjMatrix ↔ IsIdempotentElem A.toLin' ∧
      star A.toLin' = (star A).toLin' ∧ .id * A.toLin' = 0 := by
  simp only [id_convMul_toLin'_eq_zero_iff, ← isSymm_iff_intrinsicStar_toLin',
    ConvolutionProduct.isIdempotentElem_iff, toMatrix'_toLin', funext_iff, diag]
  exact ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

omit [DecidableEq n] in
variable (R) in
/-- The number of edges of a classical adjacency matrix is equal to
`⟪1, G.adjMatrix.toEuclideanLin 1⟫`. -/
theorem SimpleGraph.card_dart_eq_dotProduct : Fintype.card G.Dart = adjMatrix R G *ᵥ 1 ⬝ᵥ 1 := by
  simp [G.dart_card_eq_sum_degrees, dotProduct_one]

end
