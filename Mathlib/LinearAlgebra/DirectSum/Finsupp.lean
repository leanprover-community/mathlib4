/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.DirectSum.PiTensorProduct
import Mathlib.RingTheory.PiTensorProduct

#align_import linear_algebra.direct_sum.finsupp from "leanprover-community/mathlib"@"9b9d125b7be0930f564a68f1d73ace10cf46064d"

/-!
# Results on finitely supported functions.

* The tensor product of `ι →₀ M` and `κ →₀ N` is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`.
* The tensor product of the family `κ i →₀ M i` indexed by `ι` is linearly equivalent to
`∏ i, κ i →₀ ⨂[R] i, M i`.
-/

noncomputable section

open DirectSum Set LinearMap Submodule TensorProduct

section TensorProduct

variable (R M N ι κ : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open scoped Classical in
/-- The tensor product of `ι →₀ M` and `κ →₀ N` is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`. -/
def finsuppTensorFinsupp : (ι →₀ M) ⊗[R] (κ →₀ N) ≃ₗ[R] ι × κ →₀ M ⊗[R] N :=
  TensorProduct.congr (finsuppLEquivDirectSum R M ι) (finsuppLEquivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R (fun _ : ι => M) fun _ : κ => N) ≪≫ₗ
      (finsuppLEquivDirectSum R (M ⊗[R] N) (ι × κ)).symm)
#align finsupp_tensor_finsupp finsuppTensorFinsupp

@[simp]
theorem finsuppTensorFinsupp_single (i : ι) (m : M) (k : κ) (n : N) :
    finsuppTensorFinsupp R M N ι κ (Finsupp.single i m ⊗ₜ Finsupp.single k n) =
      Finsupp.single (i, k) (m ⊗ₜ n) :=
  by classical simp [finsuppTensorFinsupp]
#align finsupp_tensor_finsupp_single finsuppTensorFinsupp_single

@[simp]
theorem finsuppTensorFinsupp_apply (f : ι →₀ M) (g : κ →₀ N) (i : ι) (k : κ) :
    finsuppTensorFinsupp R M N ι κ (f ⊗ₜ g) (i, k) = f i ⊗ₜ g k := by
  apply Finsupp.induction_linear f
  · simp
  · intro f₁ f₂ hf₁ hf₂
    simp [add_tmul, hf₁, hf₂]
  · intro i' m
    apply Finsupp.induction_linear g
    · simp
    · intro g₁ g₂ hg₁ hg₂
      simp [tmul_add, hg₁, hg₂]
    · intro k' n
      simp only [finsuppTensorFinsupp_single]
      -- split_ifs; finish can close the goal from here
      by_cases h1 : (i', k') = (i, k)
      · simp only [Prod.mk.inj_iff] at h1
        simp [h1]
      · simp only [Prod.mk.inj_iff, not_and_or] at h1
        cases' h1 with h1 h1 <;> simp [h1]
#align finsupp_tensor_finsupp_apply finsuppTensorFinsupp_apply

@[simp]
theorem finsuppTensorFinsupp_symm_single (i : ι × κ) (m : M) (n : N) :
    (finsuppTensorFinsupp R M N ι κ).symm (Finsupp.single i (m ⊗ₜ n)) =
      Finsupp.single i.1 m ⊗ₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp_single _ _ _ _ _ _ _ _ _).symm
#align finsupp_tensor_finsupp_symm_single finsuppTensorFinsupp_symm_single

/-- A variant of `finsuppTensorFinsupp` where both modules are the ground ring. -/
def finsuppTensorFinsupp' : (ι →₀ R) ⊗[R] (κ →₀ R) ≃ₗ[R] ι × κ →₀ R :=
  finsuppTensorFinsupp R R R ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R R)
#align finsupp_tensor_finsupp' finsuppTensorFinsupp'

@[simp]
theorem finsuppTensorFinsupp'_apply_apply (f : ι →₀ R) (g : κ →₀ R) (a : ι) (b : κ) :
    finsuppTensorFinsupp' R ι κ (f ⊗ₜ[R] g) (a, b) = f a * g b := by
  simp [finsuppTensorFinsupp']
#align finsupp_tensor_finsupp'_apply_apply finsuppTensorFinsupp'_apply_apply

@[simp]
theorem finsuppTensorFinsupp'_single_tmul_single (a : ι) (b : κ) (r₁ r₂ : R) :
    finsuppTensorFinsupp' R ι κ (Finsupp.single a r₁ ⊗ₜ[R] Finsupp.single b r₂) =
      Finsupp.single (a, b) (r₁ * r₂) := by
  ext ⟨a', b'⟩
  classical
  aesop (add norm [Finsupp.single_apply])
#align finsupp_tensor_finsupp'_single_tmul_single finsuppTensorFinsupp'_single_tmul_single

end TensorProduct

/-!
The case of `PiTensorProduct`.
-/

section PiTensorProduct

open PiTensorProduct BigOperators

attribute [local ext] TensorProduct.ext

variable (R : Type*) [CommSemiring R]
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
variable (κ : ι → Type*) [(i : ι) → DecidableEq (κ i)]
variable (M : ι → Type*)
variable [∀ i, AddCommMonoid (M i)]
variable [∀ i, Module R (M i)]
variable [(i : ι) → (x : M i) → Decidable (x ≠ 0)]

/-- If `ι` is a `Fintype`, `κ i` is a family of types indexed by `ι` and `M i` is a family
of modules indexed by `ι`, then the tensor product of the family `κ i →₀ M i` is linearly
equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/
def finsuppPiTensorProduct : (⨂[R] i, κ i →₀ M i) ≃ₗ[R] ((i : ι) → κ i) →₀ ⨂[R] i, M i :=
  PiTensorProduct.congr (fun i ↦ finsuppLEquivDirectSum R (M i) (κ i)) ≪≫ₗ
  (PiTensorProduct.directSum R (fun (i : ι) ↦ fun (_ : κ i) ↦ M i)) ≪≫ₗ
  (finsuppLEquivDirectSum R (⨂[R] i, M i) ((i : ι) → κ i)).symm

@[simp]
theorem finsuppPiTensorProduct_tprod_single (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    finsuppPiTensorProduct R κ M (⨂ₜ[R] i, Finsupp.single (p i) (m i)) =
    Finsupp.single p (⨂ₜ[R] i, m i) := by
  classical
  simp only [finsuppPiTensorProduct, PiTensorProduct.directSum, LinearEquiv.trans_apply,
    congr_tprod, finsuppLEquivDirectSum_single, LinearEquiv.ofLinear_apply, lift.tprod,
    MultilinearMap.fromDirectSumEquiv_apply, compMultilinearMap_apply, map_sum,
    finsuppLEquivDirectSum_symm_lof]
  rw [Finset.sum_subset (piFinset_support_lof_sub R κ p _)]
  · rw [Finset.sum_singleton]
    simp only [lof_apply]
  · intro q _ hq
    simp only [Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq, not_forall, not_not] at hq
    obtain ⟨i, hi⟩ := hq
    simp only [Finsupp.single_eq_zero]
    exact (tprod R).map_coord_zero i hi

@[simp]
theorem finsuppPiTensorProduct_apply (f : (i : ι) → (κ i →₀ M i)) (p : (i : ι) → κ i) :
    finsuppPiTensorProduct R κ M (⨂ₜ[R] i, f i) p = ⨂ₜ[R] i, f i (p i) := by
  rw [congrArg (tprod R) (funext (fun i ↦ (Eq.symm (Finsupp.sum_single (f i)))))]
  erw [MultilinearMap.map_sum_finset (tprod R)]
  simp only [map_sum, finsuppPiTensorProduct_tprod_single]
  rw [Finset.sum_apply']
  rw [← Finset.sum_union_eq_right (s₁ := {p}) (fun _ _ h ↦ by
       simp only [Fintype.mem_piFinset, Finsupp.mem_support_iff, ne_eq, not_forall, not_not] at h
       obtain ⟨i, hi⟩ := h
       rw [(tprod R).map_coord_zero i hi, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]),
   Finset.sum_union_eq_left (fun _ _ h ↦ Finsupp.single_eq_of_ne (Finset.not_mem_singleton.mp h)),
   Finset.sum_singleton, Finsupp.single_eq_same]

@[simp]
theorem finsuppPiTensorProduct_symm_single_tprod (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    (finsuppPiTensorProduct R κ M).symm (Finsupp.single p (⨂ₜ[R] i, m i)) =
    ⨂ₜ[R] i, Finsupp.single (p i) (m i) :=
  (LinearEquiv.symm_apply_eq _).2 (finsuppPiTensorProduct_tprod_single _ _ _ _ _).symm

variable [(x : R) → Decidable (x ≠ 0)]

/-- A variant of `finsuppPiTensorProduct` where all modules `M i` are the ground ring.
-/
def finsuppPiTensorProduct' : (⨂[R] i, (κ i →₀ R)) ≃ₗ[R] ((i : ι) → κ i) →₀ R :=
  finsuppPiTensorProduct R κ (fun _ ↦ R) ≪≫ₗ
  Finsupp.lcongr (Equiv.refl ((i : ι) → κ i)) (constantBaseRingEquiv ι R).toLinearEquiv

@[simp]
theorem finsuppPiTensorProduct'_apply_apply (f : (i : ι) → κ i →₀ R) (p : (i : ι) → κ i) :
    finsuppPiTensorProduct' R κ (⨂ₜ[R] i, f i) p = ∏ i, f i (p i) := by
  simp only [finsuppPiTensorProduct', LinearEquiv.trans_apply, Finsupp.lcongr_apply_apply,
    Equiv.refl_symm, Equiv.refl_apply, finsuppPiTensorProduct_apply, AlgEquiv.toLinearEquiv_apply,
    constantBaseRingEquiv_tprod]

@[simp]
theorem finsuppPiTensorProduct'_tprod_single (p : (i : ι) → κ i) (r : ι → R) :
    finsuppPiTensorProduct' R κ (⨂ₜ[R] i, Finsupp.single (p i) (r i)) =
    Finsupp.single p (∏ i, r i) := by
  ext q
  simp only [finsuppPiTensorProduct'_apply_apply]
  by_cases h : q = p
  · rw [h]; simp only [Finsupp.single_eq_same]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Finsupp.single_eq_of_ne (Ne.symm h), Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [(Finsupp.single_eq_of_ne (Ne.symm hi))])]

end PiTensorProduct

end
