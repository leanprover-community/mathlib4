/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.ZPow
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# Lemmas about the matrix exponential

In this file, we provide results about `NormedSpace.exp` on `Matrix`s
over a topological or normed algebra.
Note that generic results over all topological spaces such as `NormedSpace.exp_zero`
can be used on matrices without issue, so are not repeated here.
The topological results specific to matrices are:

* `Matrix.exp_transpose`
* `Matrix.exp_conjTranspose`
* `Matrix.exp_diagonal`
* `Matrix.exp_blockDiagonal`
* `Matrix.exp_blockDiagonal'`

Lemmas like `NormedSpace.exp_add_of_commute` require a canonical norm on the type;
while there are multiple sensible choices for the norm of a `Matrix` (`Matrix.normedAddCommGroup`,
`Matrix.frobeniusNormedAddCommGroup`, `Matrix.linftyOpNormedAddCommGroup`), none of them
are canonical. In an application where a particular norm is chosen using
`attribute [local instance]`, then the usual lemmas about `NormedSpace.exp` are fine.
When choosing a norm is undesirable, the results in this file can be used.

In this file, we copy across the lemmas about `NormedSpace.exp`,
but hide the requirement for a norm inside the proof.

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

* Show that `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`

## References

* https://en.wikipedia.org/wiki/Matrix_exponential
-/

public section

open scoped Matrix

open NormedSpace -- For `exp`.

variable {m n : Type*} {n' : m → Type*} {𝔸 : Type*}

namespace Matrix

section Topological

section Ring

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]
  [T2Space 𝔸]

theorem exp_diagonal [Algebra ℚ 𝔸] (v : m → 𝔸) : exp (diagonal v) = diagonal (exp v) := by
  simp_rw [exp_eq_tsum_rat, diagonal_pow, ← diagonal_smul, ← diagonal_tsum]

theorem exp_blockDiagonal [Algebra ℚ 𝔸] (v : m → Matrix n n 𝔸) :
    exp (blockDiagonal v) = blockDiagonal (exp v) := by
  simp_rw [exp_eq_tsum_rat, ← blockDiagonal_pow, ← blockDiagonal_smul, ← blockDiagonal_tsum]

theorem exp_blockDiagonal' [Algebra ℚ 𝔸] (v : ∀ i, Matrix (n' i) (n' i) 𝔸) :
    exp (blockDiagonal' v) = blockDiagonal' (exp v) := by
  simp_rw [exp_eq_tsum_rat, ← blockDiagonal'_pow, ← blockDiagonal'_smul, ← blockDiagonal'_tsum]

theorem exp_conjTranspose [StarRing 𝔸] [ContinuousStar 𝔸] (A : Matrix m m 𝔸) :
    exp Aᴴ = (exp A)ᴴ :=
  (star_exp A).symm

theorem IsHermitian.exp [StarRing 𝔸] [ContinuousStar 𝔸] {A : Matrix m m 𝔸} (h : A.IsHermitian) :
    (exp A).IsHermitian :=
  (exp_conjTranspose _).symm.trans <| congr_arg _ h

end Ring

lemma exp_eq_isNilpotent_exp [Fintype m] [DecidableEq m] [Field 𝕂] [DivisionRing 𝔸] [CharZero 𝔸]
    [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] [IsScalarTower ℚ 𝕂 𝔸]
    {A : Matrix m m 𝔸} (ha : IsNilpotent A) : exp 𝕂 A = IsNilpotent.exp A := by
  rw [exp_eq_finset_sum_of_isNilpotent 𝕂 ha]
  congrm ∑ _ ∈ _, ?_
  rw [← Rat.cast_inv_nat]
  apply Rat.cast_smul_eq_qsmul

section CommRing

variable [Fintype m] [DecidableEq m] [CommRing 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸] [Algebra ℚ 𝔸] [T2Space 𝔸]

theorem exp_transpose (A : Matrix m m 𝔸) : exp Aᵀ = (exp A)ᵀ := by
  simp_rw [exp_eq_tsum_rat, transpose_tsum, transpose_smul, transpose_pow]

theorem IsSymm.exp {A : Matrix m m 𝔸} (h : A.IsSymm) : (exp A).IsSymm :=
  (exp_transpose _).symm.trans <| congr_arg _ h

end CommRing

end Topological

section Normed

variable [Fintype m] [DecidableEq m] [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_add_of_commute (A B : Matrix m m 𝔸) (h : Commute A B) :
    exp (A + B) = exp A * exp B :=
  open scoped Norms.Operator in exp_add_of_commute h

set_option backward.isDefEq.respectTransparency false in
open scoped Function in -- required for scoped `on` notation
nonrec theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → Matrix m m 𝔸)
    (h : (s : Set ι).Pairwise (Commute on f)) :
    exp (∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp (f i)) fun _ hi _ hj _ => (h.of_refl hi hj).exp :=
  open scoped Norms.Operator in exp_sum_of_commute s f h

set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_nsmul (n : ℕ) (A : Matrix m m 𝔸) : exp (n • A) = exp A ^ n :=
  open scoped Norms.Operator in exp_nsmul n A

set_option backward.isDefEq.respectTransparency false in
nonrec theorem isUnit_exp (A : Matrix m m 𝔸) : IsUnit (exp A) :=
  open scoped Norms.Operator in isUnit_exp A

set_option backward.isDefEq.respectTransparency false in
-- TODO: without disabling this instance we get a timeout, see lean4#10414:
-- https://github.com/leanprover/lean4/issues/10414
-- and zulip discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Coercion.20instance.20problems.20with.20matrix.20exponential/with/539770030
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
nonrec theorem exp_units_conj (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp (U * A * U⁻¹) = U * exp A * U⁻¹ :=
  open scoped Norms.Operator in exp_units_conj U A

-- TODO: without disabling this instance we get a timeout, see lean4#10414:
-- https://github.com/leanprover/lean4/issues/10414
-- and zulip discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Coercion.20instance.20problems.20with.20matrix.20exponential/with/539770030
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem exp_units_conj' (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp (U⁻¹ * A * U) = U⁻¹ * exp A * U :=
  exp_units_conj U⁻¹ A

end Normed

section NormedComm

variable [Fintype m] [DecidableEq m]
  [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

set_option backward.isDefEq.respectTransparency false in
theorem exp_neg (A : Matrix m m 𝔸) : exp (-A) = (exp A)⁻¹ := by
  rw [nonsing_inv_eq_ringInverse]
  open scoped Norms.Operator in exact (Ring.inverse_exp A).symm

theorem exp_zsmul (z : ℤ) (A : Matrix m m 𝔸) : exp (z • A) = exp A ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · have : IsUnit (exp A).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_exp _)
    rw [Matrix.zpow_neg this, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]

theorem exp_conj (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp (U * A * U⁻¹) = U * exp A * U⁻¹ :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj u A

theorem exp_conj' (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp (U⁻¹ * A * U) = U⁻¹ * exp A * U :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj' u A

end NormedComm

end Matrix
