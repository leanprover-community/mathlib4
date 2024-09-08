/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# Canonial Hilbert space from Inner product space

This file defines a complete inner product space from a preinner product space by
quotienting the null space and taking the completion.

## Main results

- **

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `RealInnerProductSpace`, `ComplexInnerProductSpace`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

-/

noncomputable section

open RCLike Real Filter

open Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

open Submodule Quotient LinearMap InnerProductSpace InnerProductSpace.Core

variable (𝕜 E : Type*) [k: RCLike 𝕜]

section Nullspace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def nullSpace : Submodule 𝕜 E where
  carrier := {x : E | ‖x‖ = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq] at hy
    simp only [Set.mem_setOf_eq]
    apply le_antisymm _ (norm_nonneg (x+y))
    apply le_trans (norm_add_le x y)
    rw [hx, hy]
    linarith
  zero_mem' := norm_zero
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq]
    rw [norm_smul, hx, mul_zero]

lemma mem_nullSpace_iff_norm_eq_zero {x : E} : x ∈ nullSpace 𝕜 E ↔ ‖x‖ = 0 := by
  exact Eq.to_iff rfl

abbrev Q := (mk : E → (E ⧸ (nullSpace 𝕜 E)))

lemma inner_nullSpace_eq_zero (x y : E) (h : x ∈ nullSpace 𝕜 E): ⟪x, y⟫_𝕜 = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff]
  apply le_antisymm _ (sq_nonneg _)
  rw [sq]
  nth_rw 2 [← RCLike.norm_conj]
  rw [_root_.inner_conj_symm]
  calc ‖⟪x, y⟫_𝕜‖ * ‖⟪y, x⟫_𝕜‖ ≤ re ⟪x, x⟫_𝕜 * re ⟪y, y⟫_𝕜 := inner_mul_inner_self_le _ _
  _ = (‖x‖ * ‖x‖) * re ⟪y, y⟫_𝕜 := by rw [inner_self_eq_norm_mul_norm x]
  _ = (0 * 0) * re ⟪y, y⟫_𝕜 := by rw [(mem_nullSpace_iff_norm_eq_zero 𝕜 E).mp h]
  _ = 0 := by ring

lemma inner_nullSpace_eq_zero' (x y : E) (h : y ∈ nullSpace 𝕜 E): ⟪x, y⟫_𝕜 = 0 := by
  rw [inner_eq_zero_symm]
  exact inner_nullSpace_eq_zero 𝕜 E y x h

theorem nullSpace_le_ker_toDualMap (x : E) : (nullSpace 𝕜 E) ≤ ker (toDualMap 𝕜 E x) := by
  intro y hy
  refine LinearMap.mem_ker.mpr ?_
  simp only [toDualMap_apply]
  exact inner_nullSpace_eq_zero' 𝕜 E x y hy

def innerQ : E ⧸ (nullSpace 𝕜 E) → E ⧸ (nullSpace 𝕜 E) → 𝕜 :=
  @liftQ 𝕜 E _ _ _ (nullSpace 𝕜 E) 𝕜 _ _ _ _ k.conjToRingEquiv (toDualMap 𝕜 E)

-- to define quotient space, define inner product on it,
-- use Submodule.liftQ, but need a conjugate-linear version of it
-- then make an instance of PreInnerProductSpace.Core

end Nullspace

end

#min_imports
