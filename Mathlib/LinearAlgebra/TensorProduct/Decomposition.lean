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

public section

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
def decomposeTensor (N : Type*) [AddCommMonoid N] [Module R N] :
    ι → Submodule R (M ⊗[R] N) :=
  fun i ↦ LinearMap.range ((ℳ i).subtype.rTensor N)

lemma subtype_rTensor_injective (N : Type*) [AddCommMonoid N] [Module R N] (i : ι) :
    Function.Injective ((ℳ i).subtype.rTensor N) :=
  injective_of_comp_eq_id ((ℳ i).subtype.rTensor N) (((component R ι (fun i ↦ ↥(ℳ i)) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap).rTensor N) (by ext; simp)

/-- The linear isomorphism to the submodule from the tensor product with a summand. -/
noncomputable def toDecomposeTensor (N : Type*) [AddCommMonoid N] [Module R N]
    (i : ι) : (ℳ i) ⊗[R] N ≃ₗ[R] decomposeTensor ℳ N i :=
  LinearEquiv.ofInjective ((ℳ i).subtype.rTensor N) (subtype_rTensor_injective ℳ N i)

@[simp]
lemma toDecomposeTensor_apply (N : Type*) [AddCommMonoid N] [Module R N] {i : ι}
    (x : (ℳ i) ⊗[R] N) :
    toDecomposeTensor ℳ N i x = ((ℳ i).subtype.rTensor N) x := by rfl

lemma toDecomposeTensor_of_apply (N : Type*) [AddCommMonoid N] [Module R N] {i : ι}
    (x : (ℳ i) ⊗[R] N) :
    (congrLinearEquiv fun a ↦ toDecomposeTensor ℳ N a) ((of (fun i ↦ ↥(ℳ i) ⊗[R] N) i) x) =
    (of (fun i ↦ ↥(decomposeTensor ℳ N i)) i) (toDecomposeTensor ℳ N i x) := by
  ext; simp [coe_congrLinearEquiv]

/-lemma toDecomposeTensor_symm_apply (N : Type*) [AddCommMonoid N] [Module R N] {i : ι}
    (x : decomposeTensor ℳ N i) :
    (toDecomposeTensor ℳ N i).symm x = (((component R ι (fun i ↦ (ℳ i)) i) ∘ₗ
      ((DirectSum.decomposeLinearEquiv ℳ))).rTensor N) x := by sorry

lemma congrLinearEquiv_coeAddMonoidHom (N : Type*) [AddCommGroup N] [Module R N]
    (x : ⨁ (i : ι), ↥(ℳ i) ⊗[R] N) :
    (DirectSum.coeAddMonoidHom (decomposeTensor ℳ N))
      ((DirectSum.congrLinearEquiv fun a ↦ toDecomposeTensor ℳ N a) x) =
    ((DirectSum.decomposeLinearEquiv ℳ).symm.rTensor N)
      ((TensorProduct.directSumLeft R R (fun a ↦ ℳ a) N).symm x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>

    sorry
  | add x y hx hy => simp [hx, hy]

lemma coe_decomposeTensor (N : Type*) [AddCommGroup N] [Module R N]
    (x : (⨁ (i : ι), decomposeTensor ℳ N i)) :
    (DirectSum.coeAddMonoidHom (decomposeTensor ℳ N)) x =
    ((DirectSum.decomposeLinearEquiv ℳ).symm.rTensor N)
    ((TensorProduct.directSumLeft R R (fun a ↦ ℳ a) N).symm
      ((DirectSum.congrLinearEquiv fun a ↦ toDecomposeTensor ℳ N a).symm x)) := by
  have : (LinearEquiv.rTensor N (decomposeLinearEquiv ℳ).symm) =
      (LinearEquiv.rTensor N (decomposeLinearEquiv ℳ)).symm := rfl
  rw [this, LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    simp only [coeAddMonoidHom_of, toDecomposeTensor]
    rw [LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply]
    ext j
    by_cases h : i = j
    · rw [← h]
      simp only [of_eq_same, SetLike.coe_eq_coe]

      sorry
    · simp [of_apply, h]

      sorry
  | add x y hx hy => simp [hx, hy]

noncomputable instance (N : Type*) [AddCommGroup N] [Module R N] :
    DirectSum.Decomposition (decomposeTensor ℳ N) where
  decompose' x := (DirectSum.congrLinearEquiv fun a ↦ toDecomposeTensor ℳ N a)
    (TensorProduct.directSumLeft R R (fun a ↦ ℳ a) N
      ((DirectSum.decomposeLinearEquiv ℳ).rTensor N x))
  left_inv x := by
    rw [coe_decomposeTensor ℳ N _]
    simp only [LinearEquiv.symm_apply_apply]
    have : (LinearEquiv.rTensor N (decomposeLinearEquiv ℳ).symm) =
        (LinearEquiv.rTensor N (decomposeLinearEquiv ℳ)).symm := rfl
    simp [this]
  right_inv x := by
    rw [coe_decomposeTensor ℳ N _]
    have : (LinearEquiv.rTensor N (decomposeLinearEquiv ℳ).symm) =
        (LinearEquiv.rTensor N (decomposeLinearEquiv ℳ)).symm := rfl
    simp [this]
-/
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
