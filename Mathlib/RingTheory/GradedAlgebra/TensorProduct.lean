/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tensor product of graded algebra

In this file we show that if `𝒜` is a graded `R`-algebra, and `S` is any `R`-algebra, then
`S ⊗[R] 𝒜` is a graded `S`-algebra with the same grading.
-/

namespace GradedAlgebra

variable {ι R A S : Type*} [DecidableEq ι] [AddMonoid ι]
  [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  [CommSemiring S] [Algebra R S]

open TensorProduct Submodule SetLike

instance baseChange : GradedAlgebra fun i ↦ (𝒜 i).baseChange S where
  one_mem := tmul_mem_baseChange_of_mem _ <| one_mem_graded 𝒜
  mul_mem i j := by
    suffices h : ((𝒜 i).baseChange S).map₂ (Algebra.lmul S (S ⊗[R] A)) ((𝒜 j).baseChange S) ≤
      (𝒜 (i + j)).baseChange S from fun xi xj ↦ (h <| apply_mem_map₂ _ · ·)
    simp_rw [baseChange_eq_span, map₂_span_span, span_le, Set.image2_subset_iff]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    simpa using subset_span <| Set.mem_image_of_mem _ <| mul_mem_graded hx hy

end GradedAlgebra
