/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The Cauchy–Binet formula

For matrices `A : Matrix l ι R` and `B : Matrix ι o R` over a commutative ring, with `ι` finite
and linearly ordered, the `n × n` minors of `A * B` are sums of products of `n × n` minors of `A`
and `B`, over the `n`-element subsets of `ι`.

The proof goes through the exterior power `⋀[R]^n (ι → R)`: the minors of a matrix are the
coordinates of the exterior products of its columns in the basis `Module.Basis.exteriorPower`
(`exteriorPower.ιMultiDual_apply_ιMulti`), and the formula is the expansion of the exterior
product of the columns of `B` in that basis, followed by the linear map induced by `A`.

## Main statements

* `Matrix.det_submatrix_mul`: the Cauchy–Binet formula for the minors of a product.
* `Matrix.det_mul_eq_sum_powersetCard`: the Cauchy–Binet formula for `det (A * B)` when `A * B`
  is square.
-/

public section

open Module Set exteriorPower

namespace Matrix

variable {R l o ι : Type*} [CommRing R] [Fintype ι] [LinearOrder ι]

/-- The **Cauchy–Binet formula** for minors: the minor of `A * B` on rows `I` and columns `K`
is the sum, over the `n`-element subsets `s` of `ι`, of the products of the minors of `A` on rows
`I` and columns `s` and of `B` on rows `s` and columns `K`. The subsets are enumerated in
increasing order. -/
theorem det_submatrix_mul {n : ℕ} (A : Matrix l ι R) (B : Matrix ι o R) (I : Fin n → l)
    (K : Fin n → o) :
    ((A * B).submatrix I K).det = ∑ s : powersetCard ι n,
      (A.submatrix I (powersetCard.ofFinEmbEquiv.symm s)).det *
        (B.submatrix (powersetCard.ofFinEmbEquiv.symm s) K).det := by
  let b := Pi.basisFun R ι
  let G : (ι → R) [⋀^Fin n]→ₗ[R] R :=
    detRowAlternating.compLinearMap (A.submatrix I id).mulVecLin
  have hG (v : Fin n → ι → R) : G v = (of fun i j ↦ ∑ k, A (I j) k * v i k).det := by
    change det (of fun i ↦ _) = _
    congr 1
  let w : Fin n → ι → R := fun i k ↦ B k (K i)
  have h := congrArg (alternatingMapLinearEquiv G) ((b.exteriorPower n).sum_repr (ιMulti R n w))
  rw [map_sum, alternatingMapLinearEquiv_apply_ιMulti] at h
  calc ((A * B).submatrix I K).det = G w := by
        rw [hG, ← det_transpose]; congr 1
    _ = _ := h.symm
    _ = _ := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [map_smul, basis_apply, ιMulti_family, alternatingMapLinearEquiv_apply_ιMulti, hG,
        basis_repr_apply, ιMultiDual_apply_ιMulti, smul_eq_mul, mul_comm, ← det_transpose,
        ← det_transpose (B.submatrix _ K)]
      congr 2
      ext i j
      simp [b, Pi.single_apply]

/-- The **Cauchy–Binet formula**: for `A : Matrix (Fin n) ι R` and `B : Matrix ι (Fin n) R`,
`det (A * B)` is the sum, over the `n`-element subsets `s` of `ι`, of the products of the
maximal minors of `A` and `B` indexed by `s`. -/
theorem det_mul_eq_sum_powersetCard {n : ℕ} (A : Matrix (Fin n) ι R) (B : Matrix ι (Fin n) R) :
    (A * B).det = ∑ s : powersetCard ι n,
      (A.submatrix id (powersetCard.ofFinEmbEquiv.symm s)).det *
        (B.submatrix (powersetCard.ofFinEmbEquiv.symm s) id).det := by
  simpa using det_submatrix_mul A B id id

end Matrix
