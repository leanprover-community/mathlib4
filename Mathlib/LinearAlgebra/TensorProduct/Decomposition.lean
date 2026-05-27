/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! # Decomposition of tensor product

In this file, we describe the properties of decomposition under tensor product. Suppose `ℳ` is a
decomposition of an `R`-module `M` indexed by a type `ι`. Given an `R`-module `N`, the `R`-module
`M ⊗[R] N` has a decomposition into pieces `fun i ↦ (ℳ i) ⊗[R] N`. Given a commutative `R`-algebra
`S`, the `S`-module `S ⊗[R] M` has a decomposition `fun i ↦ (ℳ i).baseChange S`.

## Declarations

-/

public section

open TensorProduct LinearMap

namespace DirectSum

variable {ι R M S : Type*}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M)

section BaseChange

variable [DecidableEq ι] [Decomposition ℳ] [CommSemiring S] [Algebra R S]

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

end BaseChange

section TensorModule

variable (N : Type*) [AddCommMonoid N] [Module R N]

/-- The submodule of a tensor product corresponding to a decomposition on the left. -/
def decomposeTensor : ι → Submodule R (M ⊗[R] N) :=
  fun i ↦ ((ℳ i).subtype.rTensor N).range

lemma decomposeTensor_apply {i : ι} :
    decomposeTensor ℳ N i = ((ℳ i).subtype.rTensor N).range := by
  exact Submodule.toSubMulAction_inj.mp rfl

variable [DecidableEq ι] [Decomposition ℳ]

lemma subtype_rTensor_injective (i : ι) :
    Function.Injective ((ℳ i).subtype.rTensor N) :=
  injective_of_comp_eq_id ((ℳ i).subtype.rTensor N) (((component R ι (fun i ↦ ↥(ℳ i)) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap).rTensor N) (by ext; simp)

/-- The linear isomorphism to the submodule from the tensor product with a summand. -/
noncomputable def decomposeTensorEquiv (i : ι) :
    (ℳ i) ⊗[R] N ≃ₗ[R] decomposeTensor ℳ N i :=
  LinearEquiv.ofInjective ((ℳ i).subtype.rTensor N) (subtype_rTensor_injective ℳ N i)

@[simp]
lemma decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) ⊗[R] N) :
    decomposeTensorEquiv ℳ N i x = ((ℳ i).subtype.rTensor N) x := by rfl

lemma decomposeTensorEquiv_of_apply {i : ι} (x : (ℳ i) ⊗[R] N) :
    (congrLinearEquiv fun a ↦ decomposeTensorEquiv ℳ N a) ((of (fun i ↦ ↥(ℳ i) ⊗[R] N) i) x) =
    (of (fun i ↦ ↥(decomposeTensor ℳ N i)) i) (decomposeTensorEquiv ℳ N i x) := by
  ext; simp [coe_congrLinearEquiv]

lemma decomposeLinearEquiv_comp_subtype {i : ι} :
    (decomposeLinearEquiv ℳ) ∘ₗ (ℳ i).subtype = lof R ι (fun i ↦ ℳ i) i := by
  ext; simp

lemma coe_decomposeTensor_apply (x : (⨁ (i : ι), decomposeTensor ℳ N i)) :
    (DirectSum.coeAddMonoidHom (decomposeTensor ℳ N)) x =
    ((DirectSum.decomposeLinearEquiv ℳ).symm.rTensor N)
    ((TensorProduct.directSumLeft R R (fun a ↦ ℳ a) N).symm
      ((DirectSum.congrLinearEquiv fun a ↦ decomposeTensorEquiv ℳ N a).symm x)) := by
  rw [← LinearEquiv.rTensor_symm, LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    obtain ⟨x, y, h⟩ := x
    simp only [← h, coeAddMonoidHom_of]
    rw [LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply, LinearEquiv.rTensor_apply,
      ← rTensor_comp_apply, decomposeLinearEquiv_comp_subtype]
    have : (rTensor N (lof R ι (fun i ↦ ↥(ℳ i)) i)) y =
        (directSumLeft R R (fun i ↦ ℳ i) N).symm ((of (fun i ↦ ℳ i ⊗[R] N) i) y) :=
      (TensorProduct.directSumLeft_symm_of R R (M₁ := fun i ↦ ℳ i) y).symm
    rw [this, LinearEquiv.apply_symm_apply, decomposeTensorEquiv_of_apply]
    rfl
  | add x y hx hy => simp [hx, hy]

/-- The decomposition of a tensor product induced by a decomposition of the left module. -/
@[reducible]
noncomputable def tensorDecomposition (N : Type*) [AddCommGroup N] [Module R N] :
    DirectSum.Decomposition (decomposeTensor ℳ N) where
  decompose' x := (DirectSum.congrLinearEquiv fun a ↦ decomposeTensorEquiv ℳ N a)
    (TensorProduct.directSumLeft R R (fun a ↦ ℳ a) N
      ((DirectSum.decomposeLinearEquiv ℳ).rTensor N x))
  left_inv x := by
    simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.rTensor_symm]
  right_inv x := by
    simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.rTensor_symm]

end TensorModule

namespace IsInternal

variable [DecidableEq ι] [CommSemiring S] [Algebra R S]

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
