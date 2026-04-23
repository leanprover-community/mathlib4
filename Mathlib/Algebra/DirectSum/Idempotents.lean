/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Andrew Yang
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Decomposition of the identity of a semiring into orthogonal idempotents

In this file we show that if a semiring `R` can be decomposed into a direct sum
of (left) ideals `R = V₁ ⊕ V₂ ⊕ ⋯ ⊕ Vₙ` then in the corresponding decomposition
`1 = e₁ + e₂ + ⋯ + eₙ` with `eᵢ ∈ Vᵢ`, each `eᵢ` is an idempotent and the
`eᵢ`'s form a family of complete orthogonal idempotents.
-/

@[expose] public section

namespace DirectSum

section OrthogonalIdempotents

variable {R I : Type*} [Semiring R] [DecidableEq I] (V : I → Ideal R) [Decomposition V]

/-- The decomposition of `(1 : R)` where `1 = e₁ + e₂ + ⋯ + eₙ` which is induced by
  the decomposition of the semiring `R = V1 ⊕ V2 ⊕ ⋯ ⊕ Vn`. -/
def idempotent (i : I) : R :=
  decompose V 1 i

lemma decompose_eq_mul_idempotent (x : R) (i : I) : decompose V x i = x * idempotent V i := by
  rw [← smul_eq_mul (a := x), idempotent, ← Submodule.coe_smul, ← smul_apply, ← decompose_smul,
    smul_eq_mul, mul_one]

lemma isIdempotentElem_idempotent (i : I) : IsIdempotentElem (idempotent V i : R) := by
  rw [IsIdempotentElem, ← decompose_eq_mul_idempotent, idempotent, decompose_coe, of_eq_same]

set_option backward.isDefEq.respectTransparency false in
/-- If a semiring can be decomposed into direct sum of finite left ideals `Vᵢ`
  where `1 = e₁ + ... + eₙ` and `eᵢ ∈ Vᵢ`, then `eᵢ` is a family of complete
  orthogonal idempotents. -/
theorem completeOrthogonalIdempotents_idempotent [Fintype I] :
    CompleteOrthogonalIdempotents (idempotent V) where
  idem := isIdempotentElem_idempotent V
  ortho i j hij := by
    simp only
    rw [← decompose_eq_mul_idempotent, idempotent, decompose_coe,
      of_eq_of_ne (h := hij.symm), Submodule.coe_zero]
  complete := by
    apply (decompose V).injective
    refine DFunLike.ext _ _ fun i ↦ ?_
    rw [decompose_sum, DFinsupp.finset_sum_apply]
    simp [idempotent, of_apply]

end OrthogonalIdempotents

end DirectSum
