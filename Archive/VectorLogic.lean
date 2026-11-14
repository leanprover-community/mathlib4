/-
Copyright (c) 2026 Yuzuki Arai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuzuki Arai
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic

/-!
# Negation in two-valued vector logic

For orthonormal real vectors `s` and `n`, Mizraji represents truth and falsity
by `s` and `n` and negation by `N = n sᵀ + s nᵀ`. The corresponding logical
identity is `I₂ = s sᵀ + n nᵀ`. Here the ambient dimension is arbitrary;
there are still only two distinguished truth values.

We prove that `N` exchanges `s` and `n`, that `N * N = I₂`, and that double
negation fixes every linear combination of `s` and `n`. In a larger ambient
space `I₂` need not be the full identity matrix: vectors orthogonal to both
truth vectors are annihilated by `N`.

## References

Eduardo Mizraji, *Vector logics: The matrix-vector representation of logical
calculus*, Fuzzy Sets and Systems 50 (1992),
https://doi.org/10.1016/0165-0114(92)90216-Q.

The same definitions are reproduced in §4.2, equations (15)–(16), of
*Illustrating a neural model of logic computations: The case of Sherlock
Holmes' old maxim*, Theoria 31 (2016), 7–25,
https://doi.org/10.1387/theoria.13959.
-/

@[expose] public section

open Matrix

namespace VectorLogic

variable {ι : Type*} [Fintype ι]

/-- The two truth vectors have unit length and are orthogonal. -/
structure TruthPair (ι : Type*) [Fintype ι] where
  truth : ι → ℝ
  falsity : ι → ℝ
  truth_dot_truth : truth ⬝ᵥ truth = 1
  falsity_dot_falsity : falsity ⬝ᵥ falsity = 1
  truth_dot_falsity : truth ⬝ᵥ falsity = 0

namespace TruthPair

variable (p : TruthPair ι)

/-- The logical identity on the space spanned by the two truth vectors. -/
noncomputable def logicalIdentity : Matrix ι ι ℝ :=
  vecMulVec p.truth p.truth + vecMulVec p.falsity p.falsity

/-- Mizraji's negation operator `n sᵀ + s nᵀ`. -/
noncomputable def negation : Matrix ι ι ℝ :=
  vecMulVec p.falsity p.truth + vecMulVec p.truth p.falsity

@[simp] theorem falsity_dot_truth : p.falsity ⬝ᵥ p.truth = 0 := by
  rw [dotProduct_comm, p.truth_dot_falsity]

/-- Negation maps the vector for truth to the vector for falsity. -/
@[simp] theorem negation_truth : p.negation *ᵥ p.truth = p.falsity := by
  simp [negation, add_mulVec, vecMulVec_mulVec, p.truth_dot_truth]

/-- Negation maps the vector for falsity to the vector for truth. -/
@[simp] theorem negation_falsity : p.negation *ᵥ p.falsity = p.truth := by
  simp [negation, add_mulVec, vecMulVec_mulVec, p.falsity_dot_falsity,
    p.truth_dot_falsity]

/-- Negation exchanges the coefficients of a weighted truth vector. -/
theorem negation_weighted (a b : ℝ) :
    p.negation *ᵥ (a • p.truth + b • p.falsity) =
      a • p.falsity + b • p.truth := by
  simp [mulVec_add, mulVec_smul]

/-- Double negation is the logical identity, not necessarily the ambient identity. -/
theorem negation_squared : p.negation * p.negation = p.logicalIdentity := by
  simp [negation, logicalIdentity, mul_add, add_mul,
    vecMulVec_mul_vecMulVec, p.truth_dot_truth, p.falsity_dot_falsity,
    p.truth_dot_falsity, add_comm]

/-- Double negation fixes all linear combinations of the truth vectors. -/
theorem double_negation_weighted (a b : ℝ) :
    p.negation *ᵥ (p.negation *ᵥ (a • p.truth + b • p.falsity)) =
      a • p.truth + b • p.falsity := by
  simp [mulVec_add, mulVec_smul]

/-- Negation annihilates a vector orthogonal to both truth vectors. -/
theorem negation_of_orthogonal (v : ι → ℝ)
    (hs : p.truth ⬝ᵥ v = 0) (hn : p.falsity ⬝ᵥ v = 0) :
    p.negation *ᵥ v = 0 := by
  simp [negation, add_mulVec, vecMulVec_mulVec, hs, hn]

end TruthPair
end VectorLogic
