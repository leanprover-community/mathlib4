/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.LinearAlgebra.Pi

/-!
# The standard basis

This file defines the standard basis `Pi.basis (s : ∀ j, Basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of `Π j, M j`. The basis vectors are given by
`Pi.basis s ⟨j, i⟩ j' = Pi.single j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `Pi.basisFun`.

To give a concrete example, `Pi.single (i : Fin 3) (1 : R)`
gives the `i`th unit basis vector in `R³`, and `Pi.basisFun R (Fin 3)` proves
this is a basis over `Fin 3 → R`.

## Main definitions

 - `Pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
 - `Pi.basisFun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
   `Pi.basisFun R η i j = Pi.single i 1 j = if i = j then 1 else 0`.
 - `Matrix.stdBasis R n m`: the standard basis on `Matrix n m R`, given by
   `Matrix.stdBasis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/


open Function Set Submodule

namespace LinearMap

variable (R : Type*) {ι : Type*} [Semiring R] (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)]
  [∀ i, Module R (φ i)] [DecidableEq ι]

/-- The standard basis of the product of `φ`. -/
@[deprecated LinearMap.single (since := "2024-08-09")]
def stdBasis : ∀ i : ι, φ i →ₗ[R] ∀ i, φ i :=
  single R φ

set_option linter.deprecated false in
@[deprecated Pi.single (since := "2024-08-09")]
theorem stdBasis_apply (i : ι) (b : φ i) : stdBasis R φ i b = update (0 : (a : ι) → φ a) i b :=
  rfl

set_option linter.deprecated false in
@[simp, deprecated Pi.single_apply (since := "2024-08-09")]
theorem stdBasis_apply' (i i' : ι) : (stdBasis R (fun _x : ι => R) i) 1 i' = ite (i = i') 1 0 := by
  simp_rw [stdBasis, single_apply, Pi.single_apply, eq_comm]

set_option linter.deprecated false in
@[deprecated LinearMap.coe_single (since := "2024-08-09")]
theorem coe_stdBasis (i : ι) : ⇑(stdBasis R φ i) = Pi.single i :=
  rfl

set_option linter.deprecated false in
@[simp, deprecated Pi.single_eq_same (since := "2024-08-09")]
theorem stdBasis_same (i : ι) (b : φ i) : stdBasis R φ i b i = b :=
  Pi.single_eq_same ..

set_option linter.deprecated false in
@[deprecated Pi.single_eq_of_ne (since := "2024-08-09")]
theorem stdBasis_ne (i j : ι) (h : j ≠ i) (b : φ i) : stdBasis R φ i b j = 0 :=
  Pi.single_eq_of_ne h b

set_option linter.deprecated false in
@[deprecated single_eq_pi_diag (since := "2024-08-09")]
theorem stdBasis_eq_pi_diag (i : ι) : stdBasis R φ i = pi (diag i) :=
  single_eq_pi_diag ..

set_option linter.deprecated false in
@[deprecated ker_single (since := "2024-08-09")]
theorem ker_stdBasis (i : ι) : ker (stdBasis R φ i) = ⊥ :=
  ker_single ..

set_option linter.deprecated false in
@[deprecated proj_comp_single (since := "2024-08-09")]
theorem proj_comp_stdBasis (i j : ι) : (proj i).comp (stdBasis R φ j) = diag j i :=
  proj_comp_single ..

set_option linter.deprecated false in
@[deprecated proj_comp_single_same (since := "2024-08-09")]
theorem proj_stdBasis_same (i : ι) : (proj i).comp (stdBasis R φ i) = id :=
  proj_comp_single_same ..

set_option linter.deprecated false in
@[deprecated proj_comp_single_ne (since := "2024-08-09")]
theorem proj_stdBasis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (stdBasis R φ j) = 0 :=
  proj_comp_single_ne R φ i j h

set_option linter.deprecated false in
@[deprecated iSup_range_single_le_iInf_ker_proj (since := "2024-08-09")]
theorem iSup_range_stdBasis_le_iInf_ker_proj (I J : Set ι) (h : Disjoint I J) :
    ⨆ i ∈ I, range (stdBasis R φ i) ≤ ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) :=
  iSup_range_single_le_iInf_ker_proj R φ I J h

set_option linter.deprecated false in
@[deprecated iInf_ker_proj_le_iSup_range_single (since := "2024-08-09")]
theorem iInf_ker_proj_le_iSup_range_stdBasis {I : Finset ι} {J : Set ι} (hu : Set.univ ⊆ ↑I ∪ J) :
    ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) ≤ ⨆ i ∈ I, range (stdBasis R φ i) :=
  iInf_ker_proj_le_iSup_range_single R φ hu

set_option linter.deprecated false in
@[deprecated iSup_range_single_eq_iInf_ker_proj (since := "2024-08-09")]
theorem iSup_range_stdBasis_eq_iInf_ker_proj {I J : Set ι} (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) (hI : Set.Finite I) :
    ⨆ i ∈ I, range (stdBasis R φ i) = ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) :=
  iSup_range_single_eq_iInf_ker_proj _ _ hd hu hI

set_option linter.deprecated false in
@[deprecated iSup_range_single (since := "2024-08-09")]
theorem iSup_range_stdBasis [Finite ι] : ⨆ i, range (stdBasis R φ i) = ⊤ :=
  iSup_range_single ..

set_option linter.deprecated false in
@[deprecated disjoint_single_single (since := "2024-08-09")]
theorem disjoint_stdBasis_stdBasis (I J : Set ι) (h : Disjoint I J) :
    Disjoint (⨆ i ∈ I, range (stdBasis R φ i)) (⨆ i ∈ J, range (stdBasis R φ i)) :=
  disjoint_single_single R φ I J h

set_option linter.deprecated false in
@[deprecated "You can probably use Finsupp.single_eq_pi_single here" (since := "2024-08-09")]
theorem stdBasis_eq_single {a : R} :
    (fun i : ι => (stdBasis R (fun _ : ι => R) i) a) = fun i : ι => ↑(Finsupp.single i a) :=
  funext fun i => (Finsupp.single_eq_pi_single i a).symm

end LinearMap

namespace Pi

open LinearMap

open Set

variable {R : Type*}

section Module

variable {η : Type*} {ιs : η → Type*} {Ms : η → Type*}

theorem linearIndependent_single [Ring R] [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]
    [DecidableEq η] (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σj, ιs j ↦ Pi.single ji.1 (v ji.1 ji.2) := by
  have hs' : ∀ j : η, LinearIndependent R fun i : ιs j => LinearMap.single R Ms j (v j i) := by
    intro j
    exact (hs j).map' _ (LinearMap.ker_single _ _ _)
  apply linearIndependent_iUnion_finite hs'
  intro j J _ hiJ
  have h₀ :
    ∀ j, span R (range fun i : ιs j => LinearMap.single R Ms j (v j i)) ≤
      LinearMap.range (LinearMap.single R Ms j) := by
    intro j
    rw [span_le, LinearMap.range_coe]
    apply range_comp_subset_range
  have h₁ :
    span R (range fun i : ιs j => LinearMap.single R Ms j (v j i)) ≤
      ⨆ i ∈ ({j} : Set _), LinearMap.range (LinearMap.single R Ms i) := by
    rw [@iSup_singleton _ _ _ fun i => LinearMap.range (LinearMap.single R (Ms) i)]
    apply h₀
  have h₂ :
    ⨆ j ∈ J, span R (range fun i : ιs j => LinearMap.single R Ms j (v j i)) ≤
      ⨆ j ∈ J, LinearMap.range (LinearMap.single R (fun j : η => Ms j) j) :=
    iSup₂_mono fun i _ => h₀ i
  have h₃ : Disjoint (fun i : η => i ∈ ({j} : Set _)) J := by
    convert Set.disjoint_singleton_left.2 hiJ using 0
  exact (disjoint_single_single _ _ _ _ h₃).mono h₁ h₂

set_option linter.deprecated false in
@[deprecated linearIndependent_single (since := "2024-08-09")]
theorem linearIndependent_stdBasis [Ring R] [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]
    [DecidableEq η] (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σj, ιs j => stdBasis R Ms ji.1 (v ji.1 ji.2) :=
  linearIndependent_single _ hs

variable [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]

section Fintype

variable [Fintype η]

open LinearEquiv

/-- `Pi.basis (s : ∀ j, Basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on `Π j, Ms j`
given by `s j` on each component.

For the standard basis over `R` on the finite-dimensional space `η → R` see `Pi.basisFun`.
-/
protected noncomputable def basis (s : ∀ j, Basis (ιs j) R (Ms j)) :
    Basis (Σj, ιs j) R (∀ j, Ms j) :=
  Basis.ofRepr
    ((LinearEquiv.piCongrRight fun j => (s j).repr) ≪≫ₗ
      (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)

@[simp]
theorem basis_repr_single [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (Pi.single j (s j i)) = Finsupp.single ⟨j, i⟩ 1 := by
  classical
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    simp only [Pi.basis, LinearEquiv.trans_apply, Basis.repr_self, Pi.single_eq_same,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
      Basis.repr_symm_apply, LinearEquiv.coe_mk, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    symm
    simp [Finsupp.single_apply]
  simp only [Pi.basis, LinearEquiv.trans_apply, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
    LinearEquiv.piCongrRight, coe_single]
  dsimp
  rw [Pi.single_eq_of_ne (Ne.symm hj), LinearEquiv.map_zero, Finsupp.zero_apply,
    Finsupp.single_eq_of_ne]
  rintro ⟨⟩
  contradiction

set_option linter.deprecated false in
@[simp, deprecated basis_repr_single (since := "2024-08-09")]
theorem basis_repr_stdBasis [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (stdBasis R _ j (s j i)) = Finsupp.single ⟨j, i⟩ 1 :=
  basis_repr_single ..

@[simp]
theorem basis_apply [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (ji) :
    Pi.basis s ji = Pi.single ji.1 (s ji.1 ji.2) :=
  Basis.apply_eq_iff.mpr (by simp)

@[simp]
theorem basis_repr (s : ∀ j, Basis (ιs j) R (Ms j)) (x) (ji) :
    (Pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
  rfl

end Fintype

section

variable [Finite η]
variable (R η)

/-- The basis on `η → R` where the `i`th basis vector is `Function.update 0 i 1`. -/
noncomputable def basisFun : Basis η R (η → R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)

@[simp]
theorem basisFun_apply [DecidableEq η] (i) :
    basisFun R η i = Pi.single i 1 := by
  simp only [basisFun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

@[simp]
theorem basisFun_repr (x : η → R) (i : η) : (Pi.basisFun R η).repr x i = x i := by simp [basisFun]

@[simp]
theorem basisFun_equivFun : (Pi.basisFun R η).equivFun = LinearEquiv.refl _ _ :=
  Basis.equivFun_ofEquivFun _

end

end Module

end Pi

namespace Module

variable (ι R M N : Type*) [Finite ι] [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The natural linear equivalence: `Mⁱ ≃ Hom(Rⁱ, M)` for an `R`-module `M`. -/
noncomputable def piEquiv : (ι → M) ≃ₗ[R] ((ι → R) →ₗ[R] M) := Basis.constr (Pi.basisFun R ι) R

lemma piEquiv_apply_apply (ι R M : Type*) [Fintype ι] [CommSemiring R]
    [AddCommMonoid M] [Module R M] (v : ι → M) (w : ι → R) :
    piEquiv ι R M v w = ∑ i, w i • v i := by
  simp only [piEquiv, Basis.constr_apply_fintype, Basis.equivFun_apply]
  congr

@[simp] lemma range_piEquiv (v : ι → M) :
    LinearMap.range (piEquiv ι R M v) = span R (range v) :=
  Basis.constr_range _ _

@[simp] lemma surjective_piEquiv_apply_iff (v : ι → M) :
    Surjective (piEquiv ι R M v) ↔ span R (range v) = ⊤ := by
  rw [← LinearMap.range_eq_top, range_piEquiv]

end Module
