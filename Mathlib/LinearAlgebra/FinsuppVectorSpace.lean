/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.StdBasis

#align_import linear_algebra.finsupp_vector_space from "leanprover-community/mathlib"@"59628387770d82eb6f6dd7b7107308aa2509ec95"

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

-/


noncomputable section

open Set LinearMap Submodule
open scoped Cardinal

universe u v w

namespace Finsupp

section Ring

variable {R : Type*} {M : Type*} {ι : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]

theorem linearIndependent_single {φ : ι → Type*} {f : ∀ ι, φ ι → M}
    (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σi, φ i => single ix.1 (f ix.1 ix.2) := by
  apply @linearIndependent_iUnion_finite R _ _ _ _ ι φ fun i x => single i (f i x)
  · intro i
    have h_disjoint : Disjoint (span R (range (f i))) (ker (lsingle i)) := by
      rw [ker_lsingle]
      exact disjoint_bot_right
    apply (hf i).map h_disjoint
  · intro i t _ hit
    refine (disjoint_lsingle_lsingle {i} t (disjoint_singleton_left.2 hit)).mono ?_ ?_
    · rw [span_le]
      simp only [iSup_singleton]
      rw [range_coe]
      apply range_comp_subset_range _ (lsingle i)
    · refine iSup₂_mono fun i hi => ?_
      rw [span_le, range_coe]
      apply range_comp_subset_range _ (lsingle i)
#align finsupp.linear_independent_single Finsupp.linearIndependent_single

end Ring

section Semiring

variable {R : Type*} {M : Type*} {ι : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]

open LinearMap Submodule

open scoped Classical in
/-- The basis on `ι →₀ M` with basis vectors `fun ⟨i, x⟩ ↦ single i (b i x)`. -/
protected def basis {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) : Basis (Σi, φ i) R (ι →₀ M) :=
  Basis.ofRepr
    { toFun := fun g =>
        { toFun := fun ix => (b ix.1).repr (g ix.1) ix.2
          support := g.support.sigma fun i => ((b i).repr (g i)).support
          mem_support_toFun := fun ix => by
            simp only [Finset.mem_sigma, mem_support_iff, and_iff_right_iff_imp, Ne]
            intro b hg
            simp [hg] at b }
      invFun := fun g =>
        { toFun := fun i =>
            (b i).repr.symm (g.comapDomain _ (Set.injOn_of_injective sigma_mk_injective _))
          support := g.support.image Sigma.fst
          mem_support_toFun := fun i => by
            rw [Ne, ← (b i).repr.injective.eq_iff, (b i).repr.apply_symm_apply,
                DFunLike.ext_iff]
            simp only [exists_prop, LinearEquiv.map_zero, comapDomain_apply, zero_apply,
              exists_and_right, mem_support_iff, exists_eq_right, Sigma.exists, Finset.mem_image,
              not_forall] }
      left_inv := fun g => by
        ext i
        rw [← (b i).repr.injective.eq_iff]
        ext x
        simp only [coe_mk, LinearEquiv.apply_symm_apply, comapDomain_apply]
      right_inv := fun g => by
        ext ⟨i, x⟩
        simp only [coe_mk, LinearEquiv.apply_symm_apply, comapDomain_apply]
      map_add' := fun g h => by
        ext ⟨i, x⟩
        simp only [coe_mk, add_apply, LinearEquiv.map_add]
      map_smul' := fun c h => by
        ext ⟨i, x⟩
        simp only [coe_mk, smul_apply, LinearEquiv.map_smul, RingHom.id_apply] }
#align finsupp.basis Finsupp.basis

@[simp]
theorem basis_repr {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) (g : ι →₀ M) (ix) :
    (Finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
  rfl
#align finsupp.basis_repr Finsupp.basis_repr

@[simp]
theorem coe_basis {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) :
    ⇑(Finsupp.basis b) = fun ix : Σi, φ i => single ix.1 (b ix.1 ix.2) :=
  funext fun ⟨i, x⟩ =>
    Basis.apply_eq_iff.mpr <| by
      classical
      ext ⟨j, y⟩
      by_cases h : i = j
      · cases h
        simp only [basis_repr, single_eq_same, Basis.repr_self,
          Finsupp.single_apply_left sigma_mk_injective]
      · have : Sigma.mk i x ≠ Sigma.mk j y := fun h' => h <| congrArg (fun s => s.fst) h'
        -- Porting note: previously `this` not needed
        simp only [basis_repr, single_apply, h, this, false_and_iff, if_false, LinearEquiv.map_zero,
        zero_apply]
#align finsupp.coe_basis Finsupp.coe_basis

/-- The basis on `ι →₀ M` with basis vectors `fun i ↦ single i 1`. -/
@[simps]
protected def basisSingleOne : Basis ι R (ι →₀ R) :=
  Basis.ofRepr (LinearEquiv.refl _ _)
#align finsupp.basis_single_one Finsupp.basisSingleOne

@[simp]
theorem coe_basisSingleOne : (Finsupp.basisSingleOne : ι → ι →₀ R) = fun i => Finsupp.single i 1 :=
  funext fun _ => Basis.apply_eq_iff.mpr rfl
#align finsupp.coe_basis_single_one Finsupp.coe_basisSingleOne

end Semiring

end Finsupp

namespace DFinsupp
variable {ι : Type*} {R : Type*} {M : ι → Type*}
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The direct sum of free modules is free.

Note that while this is stated for `DFinsupp` not `DirectSum`, the types are defeq. -/
noncomputable def basis {η : ι → Type*} (b : ∀ i, Basis (η i) R (M i)) :
    Basis (Σi, η i) R (Π₀ i, M i) :=
  .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)
#align dfinsupp.basis DFinsupp.basis

end DFinsupp

/-! TODO: move this section to an earlier file. -/


namespace Basis

variable {R M n : Type*}
variable [DecidableEq n]
variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem _root_.Finset.sum_single_ite [Fintype n] (a : R) (i : n) :
    (∑ x : n, Finsupp.single x (if i = x then a else 0)) = Finsupp.single i a := by
  simp only [apply_ite (Finsupp.single _), Finsupp.single_zero, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]
#align finset.sum_single_ite Finset.sum_single_ite

theorem equivFun_symm_stdBasis [Finite n] (b : Basis n R M) (i : n) :
    b.equivFun.symm (LinearMap.stdBasis R (fun _ => R) i 1) = b i := by
  cases nonempty_fintype n
  simp
#align basis.equiv_fun_symm_std_basis Basis.equivFun_symm_stdBasis

end Basis
