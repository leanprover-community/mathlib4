/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Two-torsion points on Weierstrass curves

This file bounds the number of points on a Weierstrass curve that are killed by two.

## Main results

* `WeierstrassCurve.Affine.Point.ncard_twoTorsion_le`: over a field of characteristic
  different from two, a Weierstrass curve has at most four points killed by two.
-/

@[expose] public section

open Polynomial

universe u

namespace WeierstrassCurve.Affine.Point

variable {F : Type u} [Field F] (W : WeierstrassCurve F) [NeZero (2 : F)]

noncomputable section

/-- A local classical decidable equality used to instantiate the affine group law. -/
local instance instDecidableEqTwoTorsion : DecidableEq F := Classical.decEq F

private noncomputable def twoTorsionRootMap :
    {P : W.toAffine.Point // (2 : ℕ) • P = 0} →
      Option (W.twoTorsionPolynomial.toPoly.rootSet F)
  | ⟨0, _⟩ => none
  | ⟨some x y h, htwo⟩ => Option.some ⟨x, by
      rw [mem_rootSet_of_ne]
      · simp only [aeval_def]
        rw [Algebra.algebraMap_self, eval₂_id]
        have hneg : some x y h = -some x y h := by
          rw [← add_eq_zero_iff_eq_neg]
          simpa [two_nsmul] using htwo
        have hy : y = W.toAffine.negY x y := by
          simpa only [neg_some, some.injEq, true_and] using hneg
        have heq := h.1
        rw [equation_iff] at heq
        simp only [negY] at hy heq
        have hlin : 2 * y + W.a₁ * x + W.a₃ = 0 := by
          linear_combination hy
        simp only [Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial,
          eval_add, eval_mul, eval_C, eval_pow, eval_X]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆]
        linear_combination -4 * heq +
          (2 * y + W.a₁ * x + W.a₃) * hlin
      · intro hp
        have hdeg : W.twoTorsionPolynomial.toPoly.natDegree = 3 :=
          Cubic.natDegree_of_a_ne_zero' (by
            rw [show (4 : F) = 2 ^ 2 by norm_num]
            exact pow_ne_zero 2 (NeZero.ne (2 : F)))
        rw [hp, natDegree_zero] at hdeg
        omega⟩

private theorem twoTorsionRootMap_injective :
    Function.Injective (twoTorsionRootMap W) := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  apply Subtype.ext
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y hxy => simp [twoTorsionRootMap] at h
  | some x y hxy =>
      cases Q with
      | zero => simp [twoTorsionRootMap] at h
      | some x' y' hxy' =>
          simp only [twoTorsionRootMap, Option.some.injEq,
            Subtype.mk.injEq] at h
          have hxrep : (some x y hxy).xRep = (some x' y' hxy').xRep := by
            simp [h]
          rcases eq_or_eq_neg_of_xRep_eq_xRep hxrep with heq | heq
          · exact heq
          · have hself : some x' y' hxy' = -some x' y' hxy' := by
              rw [← add_eq_zero_iff_eq_neg]
              simpa [two_nsmul] using hQ
            rw [hself.symm] at heq
            exact heq

/-- Over a field of characteristic different from two, a Weierstrass curve has at most
four points killed by two. -/
theorem ncard_twoTorsion_le :
    Set.ncard {P : W.toAffine.Point | (2 : ℕ) • P = 0} ≤ 4 := by
  rw [← Nat.card_coe_set_eq]
  calc
    Nat.card {P : W.toAffine.Point // (2 : ℕ) • P = 0}
        ≤ Nat.card (Option (W.twoTorsionPolynomial.toPoly.rootSet F)) :=
      Nat.card_le_card_of_injective (twoTorsionRootMap W)
        (twoTorsionRootMap_injective W)
    _ = Nat.card (W.twoTorsionPolynomial.toPoly.rootSet F) + 1 := by
      rw [Finite.card_option]
    _ ≤ 3 + 1 := by
      gcongr
      rw [Nat.card_coe_set_eq]
      exact (W.twoTorsionPolynomial.toPoly.ncard_rootSet_le F).trans_eq
        (Cubic.natDegree_of_a_ne_zero' (by
          rw [show (4 : F) = 2 ^ 2 by norm_num]
          exact pow_ne_zero 2 (NeZero.ne (2 : F))))
    _ = 4 := by norm_num

end

end WeierstrassCurve.Affine.Point
