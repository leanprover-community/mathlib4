/-
Copyright (c) 2026 William Weishuhn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Weishuhn
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint

/-! # Moore-Penrose pseudo-inverse

This file defines `IsMoorePenroseInverse`, a predicate stating that one element is the
Moore-Penrose pseudo-inverse of another. The definition uses heterogeneous multiplication
so it applies to non-square matrices and linear maps between different spaces.

## Main definitions

* `IsMoorePenroseInverse A As`: `As` satisfies the four Penrose conditions with respect to `A`.

## Main results

* `IsMoorePenroseInverse.unique`: the Moore-Penrose inverse is unique in any `Semigroup`
  with `StarMul`.

## References

* "The Moore-Penrose inverse over a commutative ring"
  (Dec 1992, Linear Algebra and its Applications)
-/

/-- `As` is a Moore-Penrose pseudo-inverse of `A` if the four Penrose conditions hold:
1. `A * As * A = A`
2. `As * A * As = As`
3. `A * As` is self-adjoint (`star (A * As) = A * As`)
4. `As * A` is self-adjoint (`star (As * A) = As * A`) -/
structure IsMoorePenroseInverse {α β γ δ} [HMul α β γ] [HMul β α δ] [HMul γ α α]
    [HMul δ β β] [Star γ] [Star δ] (A : α) (As : β) : Prop where
  mul_mul_cancel_left : A * As * A = A
  mul_mul_cancel_right : As * A * As = As
  star_mul_self : star (A * As) = A * As
  star_self_mul : star (As * A) = As * A

attribute [simp] IsMoorePenroseInverse.mul_mul_cancel_left
  IsMoorePenroseInverse.mul_mul_cancel_right
  IsMoorePenroseInverse.star_mul_self
  IsMoorePenroseInverse.star_self_mul

namespace IsMoorePenroseInverse

section Heterogeneous

variable {α β γ δ : Type*} [HMul α β γ] [HMul β α δ] [HMul γ α α] [HMul δ β β]
    [Star γ] [Star δ]
variable {A : α} {As : β}

/-- If `As` is a Moore-Penrose inverse of `A`, then `A` is a Moore-Penrose
inverse of `As`. -/
lemma symm (h : IsMoorePenroseInverse A As) : IsMoorePenroseInverse As A where
  mul_mul_cancel_left := h.mul_mul_cancel_right
  mul_mul_cancel_right := h.mul_mul_cancel_left
  star_mul_self := h.star_self_mul
  star_self_mul := h.star_mul_self

lemma isSelfAdjoint_mul (h : IsMoorePenroseInverse A As) : IsSelfAdjoint (A * As) :=
  h.star_mul_self

lemma isSelfAdjoint_mul' (h : IsMoorePenroseInverse A As) : IsSelfAdjoint (As * A) :=
  h.star_self_mul

end Heterogeneous

section Unique

variable {R : Type*} [Semigroup R] [StarMul R]

/-- The Moore-Penrose inverse is unique: if both `B` and `C` satisfy the four
Penrose conditions with respect to `A`, then `B = C`. -/
theorem unique {A B C : R}
    (hB : IsMoorePenroseInverse A B) (hC : IsMoorePenroseInverse A C) :
    B = C := by
  have h1 : B * A = C * A := by
    have eq1 : B * A = (B * A) * (C * A) := by
      calc B * A = B * (A * C * A) := by rw [hC.mul_mul_cancel_left]
        _ = (B * A) * (C * A) := by simp only [mul_assoc]
    have eq2 : C * A = (C * A) * (B * A) := by
      calc C * A = C * (A * B * A) := by rw [hB.mul_mul_cancel_left]
        _ = (C * A) * (B * A) := by simp only [mul_assoc]
    have eq3 : C * A = (B * A) * (C * A) := by
      have h := congr_arg star eq2
      rw [hC.star_self_mul] at h
      rw [star_mul, hB.star_self_mul, hC.star_self_mul] at h
      exact h
    exact eq1.trans eq3.symm
  have h2 : A * B = A * C := by
    have eq1 : A * B = (A * C) * (A * B) := by
      calc A * B = (A * C * A) * B := by rw [hC.mul_mul_cancel_left]
        _ = (A * C) * (A * B) := by simp only [mul_assoc]
    have eq2 : A * C = (A * B) * (A * C) := by
      calc A * C = (A * B * A) * C := by rw [hB.mul_mul_cancel_left]
        _ = (A * B) * (A * C) := by simp only [mul_assoc]
    have eq3 : A * C = (A * C) * (A * B) := by
      have h := congr_arg star eq2
      rw [hC.star_mul_self] at h
      rw [star_mul, hB.star_mul_self, hC.star_mul_self] at h
      exact h
    exact eq1.trans eq3.symm
  calc B = B * A * B := hB.mul_mul_cancel_right.symm
    _ = C * A * B := by rw [h1]
    _ = C * (A * B) := mul_assoc _ _ _
    _ = C * (A * C) := by rw [h2]
    _ = C * A * C := (mul_assoc _ _ _).symm
    _ = C := hC.mul_mul_cancel_right

end Unique

end IsMoorePenroseInverse
