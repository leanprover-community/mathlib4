/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.NAry
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike

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

namespace GradedAlgHom

section liftEquiv

variable {ι R S A B : Type*}
variable [DecidableEq ι] [AddMonoid ι]
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
variable (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule S B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable [Algebra R S] [Algebra R B] [IsScalarTower R S B]

open TensorProduct

/-- A map from the base change of a graded algebra is the same as a map to the scalar restriction.

In category-theoretical terms, this is an adjunction between:
1. `𝒜 ↦ (𝒜 · |>.baseChange S)`, a functor from Graded `R`-Algebra to Graded `S`-Algebra; and:
2. `ℬ ↦ (ℬ · |>.restrictScalars R)`, a functor from Graded `S`-Algebra to Graded `R`-Algebra.
-/
def liftEquiv : (𝒜 →ₐᵍ[R] (ℬ · |>.restrictScalars R)) ≃ ((𝒜 · |>.baseChange S) →ₐᵍ[S] ℬ) where
  toFun f :=
    { AlgHom.liftEquiv R S A B f with
      map_mem hx := by
        obtain ⟨x, rfl⟩ := toBaseChange_surjective' _ _ hx
        induction x with
        | zero => simp
        | add => simp_all [add_mem]
        | tmul r x => simpa using smul_mem _ _ <| by exact f.map_mem x.2 }
  invFun f :=
    { AlgHom.liftEquiv R S A B |>.symm f with
      map_mem hx := f.map_mem <| tmul_mem_baseChange_of_mem _ hx }
  left_inv f := coe_algHom_injective <| by simp
  right_inv f := coe_algHom_injective <| by simp

variable {𝒜 ℬ}

@[simp] lemma liftEquiv_tmul (f : 𝒜 →ₐᵍ[R] (ℬ · |>.restrictScalars R)) (r : S) (x : A) :
    liftEquiv 𝒜 ℬ f (r ⊗ₜ[R] x) = r • f x := rfl

@[simp] lemma liftEquiv_symm_apply (f : (𝒜 · |>.baseChange S) →ₐᵍ[S] ℬ) (x : A) :
    (liftEquiv 𝒜 ℬ).symm f x = f (1 ⊗ₜ[R] x) := rfl

variable (S 𝒜)

/-- Graded version of  `Algebra.TensorProduct.includeRight`, i.e. the inclusion from a graded
`R`-algebra `𝒜` to its base change to `S` and then restricted back to `R`. (The restriction does
not change the actual sets).

In categorical terms, this is the unit of the adjunction `GradedAlgHom.liftEquiv`. -/
def includeRight : 𝒜 →ₐᵍ[R] (𝒜 · |>.baseChange S |>.restrictScalars R) where
  __ := Algebra.TensorProduct.includeRight
  map_mem hx := tmul_mem_baseChange_of_mem _ hx

variable {𝒜}

@[simp] lemma includeRight_apply (x : A) : includeRight S 𝒜 x = 1 ⊗ₜ[R] x := rfl

end liftEquiv

end GradedAlgHom
