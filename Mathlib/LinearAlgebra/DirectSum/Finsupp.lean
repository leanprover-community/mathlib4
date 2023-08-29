/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

#align_import linear_algebra.direct_sum.finsupp from "leanprover-community/mathlib"@"9b9d125b7be0930f564a68f1d73ace10cf46064d"

/-!
# Results on finitely supported functions.

The tensor product of `ι →₀ M` and `κ →₀ N` is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`.
-/


universe u v w

noncomputable section

open DirectSum

open Set LinearMap Submodule

variable {R : Type u} {M : Type v} {N : Type w} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

section TensorProduct

open TensorProduct

open TensorProduct

open scoped Classical in
/-- The tensor product of `ι →₀ M` and `κ →₀ N` is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`. -/
def finsuppTensorFinsupp (R M N ι κ : Sort _) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : (ι →₀ M) ⊗[R] (κ →₀ N) ≃ₗ[R] ι × κ →₀ M ⊗[R] N :=
  TensorProduct.congr (finsuppLEquivDirectSum R M ι) (finsuppLEquivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R (fun _ : ι => M) fun _ : κ => N) ≪≫ₗ
      (finsuppLEquivDirectSum R (M ⊗[R] N) (ι × κ)).symm)
#align finsupp_tensor_finsupp finsuppTensorFinsupp

@[simp]
theorem finsuppTensorFinsupp_single (R M N ι κ : Sort _) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (i : ι) (m : M) (k : κ) (n : N) :
    finsuppTensorFinsupp R M N ι κ (Finsupp.single i m ⊗ₜ Finsupp.single k n) =
      Finsupp.single (i, k) (m ⊗ₜ n) :=
  by classical simp [finsuppTensorFinsupp]
     -- 🎉 no goals
#align finsupp_tensor_finsupp_single finsuppTensorFinsupp_single

@[simp]
theorem finsuppTensorFinsupp_apply (R M N ι κ : Sort _) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : ι →₀ M) (g : κ →₀ N) (i : ι) (k : κ) :
    finsuppTensorFinsupp R M N ι κ (f ⊗ₜ g) (i, k) = f i ⊗ₜ g k := by
  apply Finsupp.induction_linear f
  · simp
    -- 🎉 no goals
  · intro f₁ f₂ hf₁ hf₂
    -- ⊢ ↑(↑(finsuppTensorFinsupp R M N ι κ) ((f₁ + f₂) ⊗ₜ[R] g)) (i, k) = ↑(f₁ + f₂) …
    simp [add_tmul, hf₁, hf₂]
    -- 🎉 no goals
  · intro i' m
    -- ⊢ ↑(↑(finsuppTensorFinsupp R M N ι κ) (Finsupp.single i' m ⊗ₜ[R] g)) (i, k) =  …
    apply Finsupp.induction_linear g
    · simp
      -- 🎉 no goals
    · intro g₁ g₂ hg₁ hg₂
      -- ⊢ ↑(↑(finsuppTensorFinsupp R M N ι κ) (Finsupp.single i' m ⊗ₜ[R] (g₁ + g₂))) ( …
      simp [tmul_add, hg₁, hg₂]
      -- 🎉 no goals
    · intro k' n
      -- ⊢ ↑(↑(finsuppTensorFinsupp R M N ι κ) (Finsupp.single i' m ⊗ₜ[R] Finsupp.singl …
      simp only [finsuppTensorFinsupp_single]
      -- ⊢ ↑(Finsupp.single (i', k') (m ⊗ₜ[R] n)) (i, k) = ↑(Finsupp.single i' m) i ⊗ₜ[ …
      -- split_ifs; finish can close the goal from here
      by_cases h1 : (i', k') = (i, k)
      -- ⊢ ↑(Finsupp.single (i', k') (m ⊗ₜ[R] n)) (i, k) = ↑(Finsupp.single i' m) i ⊗ₜ[ …
      · simp only [Prod.mk.inj_iff] at h1
        -- ⊢ ↑(Finsupp.single (i', k') (m ⊗ₜ[R] n)) (i, k) = ↑(Finsupp.single i' m) i ⊗ₜ[ …
        simp [h1]
        -- 🎉 no goals
      · simp only [Prod.mk.inj_iff, not_and_or] at h1
        -- ⊢ ↑(Finsupp.single (i', k') (m ⊗ₜ[R] n)) (i, k) = ↑(Finsupp.single i' m) i ⊗ₜ[ …
        cases' h1 with h1 h1 <;> simp [h1]
        -- ⊢ ↑(Finsupp.single (i', k') (m ⊗ₜ[R] n)) (i, k) = ↑(Finsupp.single i' m) i ⊗ₜ[ …
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align finsupp_tensor_finsupp_apply finsuppTensorFinsupp_apply

@[simp]
theorem finsuppTensorFinsupp_symm_single (R M N ι κ : Sort _) [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (i : ι × κ) (m : M) (n : N) :
    (finsuppTensorFinsupp R M N ι κ).symm (Finsupp.single i (m ⊗ₜ n)) =
      Finsupp.single i.1 m ⊗ₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp_single _ _ _ _ _ _ _ _ _).symm
#align finsupp_tensor_finsupp_symm_single finsuppTensorFinsupp_symm_single

variable (S : Type*) [CommRing S] (α β : Type*)

/-- A variant of `finsuppTensorFinsupp` where both modules are the ground ring. -/
def finsuppTensorFinsupp' : (α →₀ S) ⊗[S] (β →₀ S) ≃ₗ[S] α × β →₀ S :=
  (finsuppTensorFinsupp S S S α β).trans (Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid S S))
#align finsupp_tensor_finsupp' finsuppTensorFinsupp'

@[simp]
theorem finsuppTensorFinsupp'_apply_apply (f : α →₀ S) (g : β →₀ S) (a : α) (b : β) :
    finsuppTensorFinsupp' S α β (f ⊗ₜ[S] g) (a, b) = f a * g b := by simp [finsuppTensorFinsupp']
                                                                     -- 🎉 no goals
#align finsupp_tensor_finsupp'_apply_apply finsuppTensorFinsupp'_apply_apply

@[simp]
theorem finsuppTensorFinsupp'_single_tmul_single (a : α) (b : β) (r₁ r₂ : S) :
    finsuppTensorFinsupp' S α β (Finsupp.single a r₁ ⊗ₜ[S] Finsupp.single b r₂) =
      Finsupp.single (a, b) (r₁ * r₂) := by
  ext ⟨a', b'⟩
  -- ⊢ ↑(↑(finsuppTensorFinsupp' S α β) (Finsupp.single a r₁ ⊗ₜ[S] Finsupp.single b …
  classical
  aesop (add norm [Finsupp.single_apply])
#align finsupp_tensor_finsupp'_single_tmul_single finsuppTensorFinsupp'_single_tmul_single

end TensorProduct
