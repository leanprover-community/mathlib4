/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tensor product of graded algebra

In this file we show that if `𝒜` is a graded `R`-algebra, and `S` is any `R`-algebra, then
`S ⊗[R] 𝒜` is a graded `S`-algebra with the grading `fun i ↦ (𝒜 i).baseChange S`.

## Implementation notes

We need to provide the shortcut instances afterwards for the grade zero because it is expensive to
deduce via unification the function `fun i ↦ (𝒜 i).baseChange S`.
-/

@[expose] public section

open TensorProduct Submodule SetLike

namespace GradedAlgebra

variable {ι R A S : Type*}

section Semiring
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddMonoid ι]
variable [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

instance baseChange : GradedAlgebra fun i ↦ (𝒜 i).baseChange S where
  one_mem := tmul_mem_baseChange_of_mem _ <| one_mem_graded 𝒜
  mul_mem i j := by
    suffices h : ((𝒜 i).baseChange S).map₂ (Algebra.lmul S (S ⊗[R] A)) ((𝒜 j).baseChange S) ≤
      (𝒜 (i + j)).baseChange S from fun xi xj ↦ (h <| apply_mem_map₂ _ · ·)
    simp_rw [baseChange_eq_span, map₂_span_span, span_le, Set.image2_subset_iff]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    simpa using subset_span <| Set.mem_image_of_mem _ <| mul_mem_graded hx hy

instance : Semiring ((𝒜 0).baseChange S) :=
  GradeZero.instSemiring fun i ↦ (𝒜 i).baseChange S

instance : Algebra S ((𝒜 0).baseChange S) :=
  GradeZero.instAlgebra fun i ↦ (𝒜 i).baseChange S

@[simp] lemma coe_algebraMap_apply (s : S) :
    (algebraMap _ ((𝒜 0).baseChange S) s : S ⊗[R] A) = s ⊗ₜ 1 := rfl

end Semiring

section CommSemiring
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

instance : CommSemiring ((𝒜 0).baseChange S) :=
  GradeZero.instCommSemiring fun i ↦ (𝒜 i).baseChange S

end CommSemiring

section Algebra
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddCommMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

instance : Algebra ((𝒜 0).baseChange S) (S ⊗[R] A) :=
  GradeZero.instAlgebraSubtypeMemOfNat fun i ↦ (𝒜 i).baseChange S

@[simp] lemma algebraMap_apply (x : (𝒜 0).baseChange S) : algebraMap _ (S ⊗[R] A) x = x := rfl

end Algebra

section Ring
variable [CommSemiring R] [CommRing S] [Algebra R S]
variable [DecidableEq ι] [AddMonoid ι]
variable [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

instance : Ring ((𝒜 0).baseChange S) :=
  GradeZero.instRing fun i ↦ (𝒜 i).baseChange S

end Ring

section CommRing
variable [CommSemiring R] [CommRing S] [Algebra R S]
variable [DecidableEq ι] [AddCommMonoid ι]
variable [CommSemiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

instance : CommRing ((𝒜 0).baseChange S) :=
  GradeZero.instCommRing fun i ↦ (𝒜 i).baseChange S

end CommRing

end GradedAlgebra
