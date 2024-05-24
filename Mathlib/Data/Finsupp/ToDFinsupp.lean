/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.Equiv
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Data.Finsupp.Basic

#align_import data.finsupp.to_dfinsupp from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!
# Conversion between `Finsupp` and homogenous `DFinsupp`

This module provides conversions between `Finsupp` and `DFinsupp`.

## Main definitions

* non-dependent versions of `DFinsupp.sigmaCurryEquiv`:
  * `sigmaFinsuppEquivDFinsupp : ((Σ i, η i) →₀ N) ≃ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppAddEquivDFinsupp : ((Σ i, η i) →₀ N) ≃+ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppLequivDFinsupp : ((Σ i, η i) →₀ N) ≃ₗ[R] (Π₀ i, (η i →₀ N))`
-/


variable {ι : Type*} {R : Type*} {M : Type*}

#align finsupp.to_dfinsupp id
#noalign finsupp.to_dfinsupp_coe
#noalign finsupp.to_dfinsupp_single
#noalign to_dfinsupp_support
#align dfinsupp.to_finsupp id
#noalign dfinsupp.to_finsupp_coe
#noalign dfinsupp.to_finsupp_support
#noalign dfinsupp.to_finsupp_single
#noalign finsupp.to_dfinsupp_to_finsupp
#noalign dfinsupp.to_finsupp_to_dfinsupp
#noalign finsupp.to_dfinsupp_zero
#noalign finsupp.to_dfinsupp_add
#noalign finsupp.to_dfinsupp_neg
#noalign finsupp.to_dfinsupp_sub
#noalign finsupp.to_dfinsupp_smul
#noalign dfinsupp.to_finsupp_zero
#noalign dfinsupp.to_finsupp_add
#noalign dfinsupp.to_finsupp_ne
#noalign dfinsupp.to_finsupp_sub
#noalign dfinsupp.to_finsupp_smul

/-! ### Bundled `Equiv`s -/


section Equivs

#align finsupp_equiv_dfinsupp Equiv.refl
#align finsupp_add_equiv_dfinsupp AddEquiv.refl

variable (R)

#align finsupp_lequiv_dfinsupp LinearEquiv.refl

section Sigma

variable {η : ι → Type*} {N : Type*} [Semiring R] [DecidableEq ι] [(i : ι) → DecidableEq (η i)]

/-! ### Stronger versions of `Finsupp.split` -/

section Zero

variable [Zero N] [(x : N) → Decidable (x ≠ 0)]

open Finsupp

/-- `Finsupp.split` is an equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
def sigmaFinsuppEquivDFinsupp : ((Σ i, η i) →₀ N) ≃ Π₀ i, η i →₀ N :=
  DFinsupp.sigmaCurryEquiv (ι := ι) (α := η) (δ := fun _ _ => N)
#align sigma_finsupp_equiv_dfinsupp sigmaFinsuppEquivDFinsupp

@[simp]
theorem sigmaFinsuppEquivDFinsupp_apply (f : (Σ i, η i) →₀ N) :
    (sigmaFinsuppEquivDFinsupp f : ∀ i, η i →₀ N) = Finsupp.split f :=
  rfl
#align sigma_finsupp_equiv_dfinsupp_apply sigmaFinsuppEquivDFinsupp_apply

@[simp]
theorem sigmaFinsuppEquivDFinsupp_symm_apply (f : Π₀ i, η i →₀ N) (s : Σi, η i) :
    (sigmaFinsuppEquivDFinsupp.symm f : (Σ i, η i) →₀ N) s = f s.1 s.2 :=
  rfl
#align sigma_finsupp_equiv_dfinsupp_symm_apply sigmaFinsuppEquivDFinsupp_symm_apply

@[simp]
theorem sigmaFinsuppEquivDFinsupp_support (f : (Σ i, η i) →₀ N) :
    (sigmaFinsuppEquivDFinsupp f).support = Finsupp.splitSupport f := by
  ext
  rw [DFinsupp.mem_support_toFun]
  exact (Finsupp.mem_splitSupport_iff_nonzero _ _).symm
#align sigma_finsupp_equiv_dfinsupp_support sigmaFinsuppEquivDFinsupp_support

@[simp]
theorem sigmaFinsuppEquivDFinsupp_single  (a : Σ i, η i) (n : N) :
    sigmaFinsuppEquivDFinsupp (Finsupp.single a n) =
      @DFinsupp.single _ (fun i => η i →₀ N) _ _ a.1 (Finsupp.single a.2 n) :=
  DFinsupp.sigmaCurry_single (ι := ι) (α := η) (δ := fun _ _ => N) a n
#align sigma_finsupp_equiv_dfinsupp_single sigmaFinsuppEquivDFinsupp_single

end Zero

@[simp]
theorem sigmaFinsuppEquivDFinsupp_add [AddZeroClass N] [(x : N) → Decidable (x ≠ 0)]
    (f g : (Σ i, η i) →₀ N) :
    sigmaFinsuppEquivDFinsupp (f + g) =
      (sigmaFinsuppEquivDFinsupp f + sigmaFinsuppEquivDFinsupp g : Π₀ i : ι, η i →₀ N) := by
  ext
  rfl
#align sigma_finsupp_equiv_dfinsupp_add sigmaFinsuppEquivDFinsupp_add

/-- `Finsupp.split` is an additive equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
def sigmaFinsuppAddEquivDFinsupp [AddZeroClass N] [(x : N) → Decidable (x ≠ 0)] :
    ((Σ i, η i) →₀ N) ≃+ Π₀ i, η i →₀ N :=
  { sigmaFinsuppEquivDFinsupp with
    map_add' := sigmaFinsuppEquivDFinsupp_add }
#align sigma_finsupp_add_equiv_dfinsupp sigmaFinsuppAddEquivDFinsupp

@[simp]
theorem sigmaFinsuppAddEquivDFinsupp_apply [AddZeroClass N] [(x : N) → Decidable (x ≠ 0)]
    (f : (Σ i, η i) →₀ N) :
    sigmaFinsuppAddEquivDFinsupp (ι := ι) (η := η) (N := N) f = sigmaFinsuppEquivDFinsupp f :=
  rfl

@[simp]
theorem sigmaFinsuppAddEquivDFinsupp_symm_apply [AddZeroClass N] [(x : N) → Decidable (x ≠ 0)]
    (f : Π₀ i, η i →₀ N) :
    (sigmaFinsuppAddEquivDFinsupp (ι := ι) (η := η) (N := N)).symm f =
      sigmaFinsuppEquivDFinsupp.symm f :=
  rfl

@[simp]
theorem sigmaFinsuppEquivDFinsupp_smul {R} [Monoid R] [AddMonoid N] [(x : N) → Decidable (x ≠ 0)]
    [DistribMulAction R N] (r : R) (f : (Σ i, η i) →₀ N) :
    sigmaFinsuppEquivDFinsupp (r • f) = r • sigmaFinsuppEquivDFinsupp f := by
  ext
  rfl
#align sigma_finsupp_equiv_dfinsupp_smul sigmaFinsuppEquivDFinsupp_smul

/-- `Finsupp.split` is a linear equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
def sigmaFinsuppLequivDFinsupp [AddCommMonoid N] [Module R N] [(x : N) → Decidable (x ≠ 0)] :
    ((Σ i, η i) →₀ N) ≃ₗ[R] Π₀ i, η i →₀ N where
  __ := sigmaFinsuppAddEquivDFinsupp (ι := ι) (η := η) (N := N)
  map_smul' := sigmaFinsuppEquivDFinsupp_smul
#align sigma_finsupp_lequiv_dfinsupp sigmaFinsuppLequivDFinsupp

@[simp]
theorem sigmaFinsuppLequivDFinsupp_apply [AddCommMonoid N] [Module R N]
    [(x : N) → Decidable (x ≠ 0)] (f : (Σ i, η i) →₀ N) :
    sigmaFinsuppLequivDFinsupp (ι := ι) R (η := η) (N := N) f = sigmaFinsuppEquivDFinsupp f :=
  rfl

@[simp]
theorem sigmaFinsuppLequivDFinsupp_symm_apply [AddCommMonoid N] [Module R N]
    [(x : N) → Decidable (x ≠ 0)] (f : Π₀ i, η i →₀ N) :
    (sigmaFinsuppLequivDFinsupp (ι := ι) R (η := η) (N := N)).symm f =
      sigmaFinsuppEquivDFinsupp.symm f :=
  rfl

end Sigma

end Equivs
