/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Topology.UniformSpace.Matrix

#align_import analysis.normed_space.matrix_exponential from "leanprover-community/mathlib"@"1e3201306d4d9eb1fd54c60d7c4510ad5126f6f9"

/-!
# Lemmas about the matrix exponential

In this file, we provide results about `exp` on `Matrix`s over a topological or normed algebra.
Note that generic results over all topological spaces such as `exp_zero` can be used on matrices
without issue, so are not repeated here. The topological results specific to matrices are:

* `Matrix.exp_transpose`
* `Matrix.exp_conjTranspose`
* `Matrix.exp_diagonal`
* `Matrix.exp_blockDiagonal`
* `Matrix.exp_blockDiagonal'`

Lemmas like `exp_add_of_commute` require a canonical norm on the type; while there are multiple
sensible choices for the norm of a `Matrix` (`Matrix.normedAddCommGroup`,
`Matrix.frobeniusNormedAddCommGroup`, `Matrix.linftyOpNormedAddCommGroup`), none of them
are canonical. In an application where a particular norm is chosen using
`attribute [local instance]`, then the usual lemmas about `exp` are fine. When choosing a norm is
undesirable, the results in this file can be used.

In this file, we copy across the lemmas about `exp`, but hide the requirement for a norm inside the
proof.

* `Matrix.exp_add_of_commute`
* `Matrix.exp_sum_of_commute`
* `Matrix.exp_nsmul`
* `Matrix.isUnit_exp`
* `Matrix.exp_units_conj`
* `Matrix.exp_units_conj'`

Additionally, we prove some results about `matrix.has_inv` and `matrix.div_inv_monoid`, as the
results for general rings are instead stated about `Ring.inverse`:

* `Matrix.exp_neg`
* `Matrix.exp_zsmul`
* `Matrix.exp_conj`
* `Matrix.exp_conj'`

## TODO

* Show that `Matrix.det (exp A) = exp (Matrix.trace A)`

## References

* https://en.wikipedia.org/wiki/Matrix_exponential
-/


open scoped Matrix BigOperators

open NormedSpace -- For `exp`.

variable (𝕂 : Type*) {m n p : Type*} {n' : m → Type*} {𝔸 : Type*}

namespace Matrix

section Topological

section Ring

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [Ring 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸]
  [Algebra ℚ 𝔸] [T2Space 𝔸]

theorem exp_diagonal (v : m → 𝔸) : exp (diagonal v) = diagonal (exp v) := by
  simp_rw [exp_eq_tsum, diagonal_pow, ← diagonal_smul, ← diagonal_tsum]
#align matrix.exp_diagonal Matrix.exp_diagonal

theorem exp_blockDiagonal (v : m → Matrix n n 𝔸) :
    exp (blockDiagonal v) = blockDiagonal (exp v) := by
  simp_rw [exp_eq_tsum, ← blockDiagonal_pow, ← blockDiagonal_smul, ← blockDiagonal_tsum]
#align matrix.exp_block_diagonal Matrix.exp_blockDiagonal

theorem exp_blockDiagonal' (v : ∀ i, Matrix (n' i) (n' i) 𝔸) :
    exp (blockDiagonal' v) = blockDiagonal' (exp v) := by
  simp_rw [exp_eq_tsum, ← blockDiagonal'_pow, ← blockDiagonal'_smul, ← blockDiagonal'_tsum]
#align matrix.exp_block_diagonal' Matrix.exp_blockDiagonal'

theorem exp_conjTranspose [StarRing 𝔸] [ContinuousStar 𝔸] (A : Matrix m m 𝔸) :
    exp Aᴴ = (exp A)ᴴ :=
  (star_exp A).symm
#align matrix.exp_conj_transpose Matrix.exp_conjTranspose

theorem IsHermitian.exp [StarRing 𝔸] [ContinuousStar 𝔸] {A : Matrix m m 𝔸} (h : A.IsHermitian) :
    (exp A).IsHermitian :=
  (exp_conjTranspose _).symm.trans <| congr_arg _ h
#align matrix.is_hermitian.exp Matrix.IsHermitian.exp

end Ring

section CommRing

variable [Fintype m] [DecidableEq m] [CommRing 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸]
  [Algebra ℚ 𝔸] [T2Space 𝔸]

theorem exp_transpose (A : Matrix m m 𝔸) : exp Aᵀ = (exp A)ᵀ := by
  simp_rw [exp_eq_tsum, transpose_tsum, transpose_smul, transpose_pow]
#align matrix.exp_transpose Matrix.exp_transpose

theorem IsSymm.exp {A : Matrix m m 𝔸} (h : A.IsSymm) : (exp A).IsSymm :=
  (exp_transpose _).symm.trans <| congr_arg _ h
#align matrix.is_symm.exp Matrix.IsSymm.exp

end CommRing

end Topological

section Normed

variable [RCLike 𝕂] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [NormedRing 𝔸] [Algebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

nonrec theorem exp_add_of_commute (A B : Matrix m m 𝔸) (h : Commute A B) :
    exp (A + B) = exp A * exp B := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_add_of_commute 𝕂 h
#align matrix.exp_add_of_commute Matrix.exp_add_of_commute

nonrec theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → Matrix m m 𝔸)
    (h : (s : Set ι).Pairwise fun i j => Commute (f i) (f j)) :
    exp (∑ i in s, f i) =
      s.noncommProd (fun i => exp (f i)) fun i hi j hj _ => (h.of_refl hi hj).exp := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_sum_of_commute 𝕂 s f h
#align matrix.exp_sum_of_commute Matrix.exp_sum_of_commute

nonrec theorem exp_nsmul (n : ℕ) (A : Matrix m m 𝔸) : exp (n • A) = exp A ^ n := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_nsmul 𝕂 n A
#align matrix.exp_nsmul Matrix.exp_nsmul

nonrec theorem isUnit_exp (A : Matrix m m 𝔸) : IsUnit (exp A) := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact isUnit_exp 𝕂 A
#align matrix.is_unit_exp Matrix.isUnit_exp

-- TODO(mathlib4#6607): fix elaboration so `val` isn't needed
nonrec theorem exp_units_conj (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp (U.val * A * (U⁻¹).val) = U.val * exp A * (U⁻¹).val := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_units_conj 𝕂 U A
#align matrix.exp_units_conj Matrix.exp_units_conj

-- TODO(mathlib4#6607): fix elaboration so `val` isn't needed
theorem exp_units_conj' (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp ((U⁻¹).val * A * U.val) = (U⁻¹).val * exp A * U.val :=
  exp_units_conj 𝕂 U⁻¹ A
#align matrix.exp_units_conj' Matrix.exp_units_conj'

end Normed

section NormedComm

variable [RCLike 𝕂] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [NormedCommRing 𝔸] [Algebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

theorem exp_neg (A : Matrix m m 𝔸) : exp (-A) = (exp A)⁻¹ := by
  rw [nonsing_inv_eq_ring_inverse]
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact (Ring.inverse_exp 𝕂 A).symm
#align matrix.exp_neg Matrix.exp_neg

theorem exp_zsmul (z : ℤ) (A : Matrix m m 𝔸) : exp (z • A) = exp A ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_coe_nat, natCast_zsmul, exp_nsmul 𝕂]
  · have : IsUnit (exp A).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_exp 𝕂 _)
    rw [Matrix.zpow_neg this, zpow_coe_nat, neg_smul, exp_neg 𝕂, natCast_zsmul, exp_nsmul 𝕂]
#align matrix.exp_zsmul Matrix.exp_zsmul

theorem exp_conj (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp (U * A * U⁻¹) = U * exp A * U⁻¹ :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj 𝕂 u A
#align matrix.exp_conj Matrix.exp_conj

theorem exp_conj' (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp (U⁻¹ * A * U) = U⁻¹ * exp A * U :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj' 𝕂 u A
#align matrix.exp_conj' Matrix.exp_conj'

end NormedComm

end Matrix
