/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! # Decomposition of tensor product

In this file we show that if `ℳ` is a decomposition of an `R`-module `M` indexed by a type `ι`,
then the `S`-module `S ⊗[R] M` has a decomposition `fun i ↦ (ℳ i).baseChange S` indexed by the
same `ι`.
-/

@[expose] public section

open TensorProduct LinearMap

namespace DirectSum

variable {ι R M S : Type*} [DecidableEq ι]
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M)
  [CommSemiring S] [Algebra R S]

section Decomposition
variable [Decomposition ℳ]

instance Decomposition.baseChange : Decomposition fun i ↦ (ℳ i).baseChange S := by
  refine .ofLinearMap _ (lmap (ℳ · |>.toBaseChange S) ∘ₗ
    (directSumRight R S S fun i ↦ ℳ i).toLinearMap ∘ₗ
    ((decomposeLinearEquiv ℳ).baseChange R S)) ?_ ?_
  · simp_rw [← comp_assoc]
    rw [← LinearEquiv.eq_comp_toLinearMap_symm]
    ext
    simp
  · ext : 1
    rw [← LinearMap.cancel_right ((ℳ _).toBaseChange_surjective S)]
    ext : 3
    simp

theorem toBaseChange_injective (i : ι) : Function.Injective ((ℳ i).toBaseChange S) := fun x y h ↦ by
  have := (Function.Bijective.of_comp_iff (lmap (ℳ · |>.toBaseChange S))
    (by rw [← LinearEquiv.coe_trans]; exact LinearEquiv.bijective _)).1
    (decompose (M := S ⊗[R] M) fun i ↦ (ℳ i).baseChange S).bijective
  refine of_injective (β := fun i ↦ S ⊗[R] ℳ i) i <| this.injective ?_
  simpa using congr(of (fun i ↦ (ℳ i).baseChange S) i $h)

theorem toBaseChange_bijective (i : ι) : Function.Bijective ((ℳ i).toBaseChange S) :=
  ⟨toBaseChange_injective ℳ i, (ℳ i).toBaseChange_surjective S⟩

/-- The submodule of a tensor product corresponding to a decomposition on the left. -/
def decomposeTensor (N : Type*) [AddCommGroup N] [Module R N] :
    ι → Submodule R (M ⊗[R] N) :=
  fun i ↦ LinearMap.range ((ℳ i).subtype.rTensor N)

/-- The linear map to the submodule from the tensor product with a summand. Make this an equiv? -/
@[simps]
def toDecomposeTensor (N : Type*) [AddCommGroup N] [Module R N]
    (i : ι) : (ℳ i) ⊗[R] N →ₗ[R] decomposeTensor ℳ N i where
  toFun x := ⟨(LinearMap.rTensor N (ℳ i).subtype) x, by solve_by_elim⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

end Decomposition

namespace IsInternal

theorem baseChange (hm : IsInternal ℳ) : IsInternal fun i ↦ (ℳ i).baseChange S :=
  haveI := hm.chooseDecomposition
  Decomposition.isInternal _

theorem toBaseChange_bijective (hm : IsInternal ℳ) (i : ι) :
    Function.Bijective ((ℳ i).toBaseChange S) :=
  haveI := hm.chooseDecomposition
  DirectSum.toBaseChange_bijective ℳ i

theorem toBaseChange_injective (hm : IsInternal ℳ) (i : ι) :
    Function.Injective ((ℳ i).toBaseChange S) :=
  (toBaseChange_bijective ℳ hm i).injective

end IsInternal

end DirectSum
