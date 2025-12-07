/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Sophie Morel
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Tensor products of dual spaces

## Main definitions

* `PiTensorProduct.dualDistrib`: The canonical linear map from `⨂[R] i, Dual R (M i)` to
  `Dual R (⨂[R] i, M i)`, sending `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication.

* `PiTensorProduct.dualDistribEquiv`: A linear equivalence between `⨂[R] i, Dual R (M i)`
  and `Dual R (⨂[R] i, M i)` when all `M i` are finite free modules. If
  `f : (i : ι) → Dual R (M i)`, then this equivalence sends `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the natural isomorphism `⨂[R] i, R ≃ R` given by multiplication.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct BigOperators LinearMap Module

open scoped TensorProduct

variable {ι : Type*} [Fintype ι]

section SemiRing

variable (R : Type*) [CommSemiring R]
variable (M : ι → Type*) [Π i, AddCommMonoid (M i)] [Π i, Module R (M i)]

/-- The canonical linear map from `⨂[R] i, Dual R (M i)` to `Dual R (⨂[R] i, M i)`,
sending `⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with
the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication. -/
noncomputable def dualDistrib : (⨂[R] i, Dual R (M i)) →ₗ[R] Dual R (⨂[R] i, M i) :=
  (LinearMap.compRight _ (constantBaseRingEquiv ι R).toLinearMap) ∘ₗ piTensorHomMap

variable {R M}

@[simp]
theorem dualDistrib_apply (f : Π i, Dual R (M i)) (m : Π i, M i) :
    dualDistrib R M (⨂ₜ[R] i, f i) (⨂ₜ[R] i, m i) = ∏ i, (f i) (m i) := by
  simp only [dualDistrib, coe_comp, Function.comp_apply,
    compRight_apply, piTensorHomMap_tprod_tprod, AlgEquiv.toLinearMap_apply,
    constantBaseRingEquiv_tprod]

end SemiRing

section Ring

variable [DecidableEq ι]
variable {R : Type*} [CommRing R]
variable {M : ι → Type*} [Π i, AddCommGroup (M i)] [Π i, Module R (M i)]
variable {κ : ι → Type*} [Π i, Fintype (κ i)] [Π i, DecidableEq (κ i)]
variable [(x : R) → Decidable (x ≠ 0)]

/-- An inverse to `PiTensorProduct.dualDistrib` given bases. -/
noncomputable def dualDistribInvOfBasis (b : Π i, Basis (κ i) R (M i)) :
    Dual R (⨂[R] i, M i) →ₗ[R] ⨂[R] i, Dual R (M i) :=
  ∑ p : (Π i, κ i), (ringLmapEquivSelf R ℕ _).symm (⨂ₜ[R] i, (b i).dualBasis (p i)) ∘ₗ
    (applyₗ (⨂ₜ[R] i, b i (p i)))

omit [(x : R) → Decidable (x ≠ 0)] in
@[simp]
theorem dualDistribInvOfBasis_apply (b : Π i, Basis (κ i) R (M i))
    (f : Dual R (⨂[R] i, M i)) : dualDistribInvOfBasis b f =
    ∑ p : (Π i,  κ i), f (⨂ₜ[R] i, b i (p i)) • (⨂ₜ[R] i, (b i).dualBasis (p i)) := by
  simp [dualDistribInvOfBasis]

theorem dualDistrib_dualDistribInvOfBasis_left_inverse (b : Π i, Basis (κ i) R (M i)) :
    comp (dualDistrib R M) (dualDistribInvOfBasis b) = LinearMap.id := by
  refine (Basis.piTensorProduct b).dualBasis.ext (fun p ↦ ?_)
  refine (Basis.piTensorProduct b).ext (fun q ↦ ?_)
  conv_lhs => rw [Basis.piTensorProduct_apply]
  simp only [Basis.coe_dualBasis, coe_comp, Function.comp_apply, dualDistribInvOfBasis_apply,
    Basis.coord_apply, map_sum, map_smul, coeFn_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
    id_coe, id_eq, Basis.repr_self]
  simp only [Basis.piTensorProduct, LinearEquiv.trans_symm, Finsupp.lcongr_symm, Equiv.refl_symm,
    AlgEquiv.toLinearEquiv_symm, Basis.map_repr, LinearEquiv.symm_symm, AlgEquiv.symm_symm,
    Finsupp.basisSingleOne_repr, LinearEquiv.trans_refl, LinearEquiv.trans_apply, congr_tprod,
    Basis.repr_self, finsuppPiTensorProduct_single, Finsupp.lcongr_single, Equiv.refl_apply,
    AlgEquiv.toLinearEquiv_apply, constantBaseRingEquiv_tprod, Finset.prod_const_one,
    dualDistrib_apply, Basis.coord_apply]
  rw [← Finset.sum_subset (Finset.subset_univ {p}), Finset.sum_singleton]
  · by_cases h : p = q
    · simp only [h, Finsupp.single_eq_same, Finset.prod_const_one, mul_one]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      rw [Finsupp.single_eq_of_ne (Ne.symm h), Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [Finsupp.single_eq_of_ne (Ne.symm hi)]), mul_zero]
  · exact fun _ _ h ↦ by rw [Finsupp.single_eq_of_ne (Finset.not_mem_singleton.mp h), zero_mul]

theorem dualDistrib_dualDistribInvOfBasis_right_inverse (b : Π i, Basis (κ i) R (M i)) :
    comp (dualDistribInvOfBasis b) (dualDistrib R M) = LinearMap.id := by
  refine (Basis.piTensorProduct (fun i ↦ (b i).dualBasis)).ext (fun p ↦ ?_)
  simp only [Basis.piTensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self, id_coe,
    id_eq]
  rw [← Finset.sum_subset (Finset.subset_univ {p})]
  · simp only [Finset.sum_singleton, Finsupp.single_eq_same, Finset.prod_const_one, one_smul]
  · intro _ _ h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (Finset.not_mem_singleton.mp h)
    rw [Finset.prod_eq_zero (Finset.mem_univ i), zero_smul]; rw [Finsupp.single_eq_of_ne hi]

/-- A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)`
given bases for all `M i`. If `f : (i : ι) → Dual R (s i)`, then this equivalence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multipliccation (`constantBaseRingEquiv`). -/
@[simps!]
noncomputable def dualDistribEquivOfBasis (b : Π i, Basis (κ i) R (M i)) :
    (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i) := by
  refine LinearEquiv.ofLinear (dualDistrib R M) (dualDistribInvOfBasis b) ?_ ?_
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _

variable (R M)
variable [Π i, Module.Finite R (M i)] [Π i, Module.Free R (M i)]

/-- A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)` when all
`M i` are finite free modules. If `f : (i : ι) → Dual R (M i)`, then this equivalence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multipliccation (`constantBaseRingEquiv`). -/
@[simp]
noncomputable def dualDistribEquiv : (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i) :=
  dualDistribEquivOfBasis (fun i ↦ Module.Free.chooseBasis R (M i))

end Ring

end PiTensorProduct
