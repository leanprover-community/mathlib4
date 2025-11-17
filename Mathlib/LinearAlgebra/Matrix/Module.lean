/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Pi

/-!
# Main Results

- `Matrix.matrixModule`: This instance shows `ι → M` is a module over `Matrix ι ι R`, and the action
  of it is a generalization of `Matrix.mulVec`.
- `LinearMap.mapModule`: This defines a linear map from `ι → M` to `ι → N` over
  `Matrix ι ι R` induced by a linear map from `M` to `N` and together with `Matrix.matrixModule`
  it gives a functor from the category of `R`-modules to the category of `Matrix ι ι R`-modules.

## Tags
matrix, module
-/

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

namespace Matrix.Module

/-- `Mⁿ` is a `Mₙ(R)` module, note that this creates a diamond when `M` is `Matrix ι ι R` or when
  `M` is `R`. (The intended name in lemmas is `smulVec`.) -/
scoped instance matrixModule : Module (Matrix ι ι R) (ι → M) where
  smul N v i := ∑ j : ι, N i j • v j
  one_smul v := funext fun i ↦ show ∑ _, _ = _ by simp [one_apply]
  mul_smul N₁ N₂ v := funext fun i ↦ show ∑ _, _ = ∑ _, _ • (∑ _, _) by
    simp_rw [mul_apply, Finset.smul_sum, Finset.sum_smul, MulAction.mul_smul]
    rw [Finset.sum_comm]
  smul_zero v := funext fun i ↦ show ∑ _, _ = _ by simp
  smul_add N v₁ v₂ := funext fun i ↦ show ∑ j : ι, N i j • (v₁ + v₂) j = (∑ _, _) + (∑ _, _) by
    simp [smul_add, Finset.sum_add_distrib]
  add_smul N₁ N₂ v := funext fun i ↦ show ∑ j : ι, (N₁ + N₂) i j • v j = (∑ _, _) + (∑ _, _) by
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul v := funext fun i ↦ show ∑ _, _ = _ by simp

lemma smulVec_def (N : Matrix ι ι R) (v : ι → M) :
    N • v = fun i ↦ ∑ j : ι, N i j • v j := rfl

lemma smulVec_def' (N : Matrix ι ι R) (v : ι → M) : N • v = ∑ j : ι, fun i ↦ N i j • v j := by
  ext; simp [smulVec_def]

@[simp]
lemma smul_vec_apply (N : Matrix ι ι R) (v : ι → M) (i : ι) :
    (N • v) i = ∑ j : ι, N i j • v j := rfl

instance (S) [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    IsScalarTower R (Matrix ι ι S) (ι → M) where
  smul_assoc _ _ _ := by ext; simp [Finset.smul_sum]

end Matrix.Module

namespace LinearMap

open Matrix.Module

/-- The induced linear map from `Mⁿ` to `Nⁿ` by a linear map `f : M → N`, this is the matrix linear
  version of `LinearMap.compLeft`. -/
@[simps]
def mapMatrixModule (f : M →ₗ[R] N) : (ι → M) →ₗ[Matrix ι ι R] (ι → N) where
  toFun := LinearMap.compLeft f ι
  map_add' := map_add _
  map_smul' _ _ := by ext; simp

@[simp]
lemma id_mapMatrixModule :
    LinearMap.id.mapMatrixModule = .id (R := Matrix ι ι R) (M := ι → M) := by
  ext; simp

lemma comp_mapMatrixModule (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (g ∘ₗ f).mapMatrixModule (ι := ι) = g.mapMatrixModule ∘ₗ f.mapMatrixModule := by
  ext; simp

end LinearMap
