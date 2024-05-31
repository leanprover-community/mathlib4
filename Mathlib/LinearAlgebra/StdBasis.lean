/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.Pi

#align_import linear_algebra.std_basis from "leanprover-community/mathlib"@"13bce9a6b6c44f6b4c91ac1c1d2a816e2533d395"

/-!
# The standard basis

This file defines the standard basis `Pi.basis (s : ∀ j, Basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of `Π j, M j`. The basis vectors are given by
`Pi.basis s ⟨j, i⟩ j' = LinearMap.stdBasis R M j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `Pi.basisFun`.

To give a concrete example, `LinearMap.stdBasis R (fun (i : Fin 3) ↦ R) i 1`
gives the `i`th unit basis vector in `R³`, and `Pi.basisFun R (Fin 3)` proves
this is a basis over `Fin 3 → R`.

## Main definitions

 - `LinearMap.stdBasis R M`: if `x` is a basis vector of `M i`, then
   `LinearMap.stdBasis R M i x` is the `i`th standard basis vector of `Π i, M i`.
 - `Pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
 - `Pi.basisFun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
   `Pi.basisFun R η i j = if i = j then 1 else 0`.
 - `Matrix.stdBasis R n m`: the standard basis on `Matrix n m R`, given by
   `Matrix.stdBasis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/


open Function Set Submodule

namespace LinearMap

variable (R : Type*) {ι : Type*} [Semiring R] (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)]
  [∀ i, Module R (φ i)] [DecidableEq ι]

/-- The standard basis of the product of `φ`. -/
def stdBasis : ∀ i : ι, φ i →ₗ[R] ∀ i, φ i :=
  single
#align linear_map.std_basis LinearMap.stdBasis

theorem stdBasis_apply (i : ι) (b : φ i) : stdBasis R φ i b = update (0 : (a : ι) → φ a) i b :=
  rfl
#align linear_map.std_basis_apply LinearMap.stdBasis_apply

@[simp]
theorem stdBasis_apply' (i i' : ι) : (stdBasis R (fun _x : ι => R) i) 1 i' = ite (i = i') 1 0 := by
  rw [LinearMap.stdBasis_apply, Function.update_apply, Pi.zero_apply]
  congr 1; rw [eq_iff_iff, eq_comm]
#align linear_map.std_basis_apply' LinearMap.stdBasis_apply'

theorem coe_stdBasis (i : ι) : ⇑(stdBasis R φ i) = Pi.single i :=
  rfl
#align linear_map.coe_std_basis LinearMap.coe_stdBasis

@[simp]
theorem stdBasis_same (i : ι) (b : φ i) : stdBasis R φ i b i = b :=
  Pi.single_eq_same i b
#align linear_map.std_basis_same LinearMap.stdBasis_same

theorem stdBasis_ne (i j : ι) (h : j ≠ i) (b : φ i) : stdBasis R φ i b j = 0 :=
  Pi.single_eq_of_ne h b
#align linear_map.std_basis_ne LinearMap.stdBasis_ne

theorem stdBasis_eq_pi_diag (i : ι) : stdBasis R φ i = pi (diag i) := by
  ext x j
  -- Porting note: made types explicit
  convert (update_apply (R := R) (φ := φ) (ι := ι) 0 x i j _).symm
  rfl
#align linear_map.std_basis_eq_pi_diag LinearMap.stdBasis_eq_pi_diag

theorem ker_stdBasis (i : ι) : ker (stdBasis R φ i) = ⊥ :=
  ker_eq_bot_of_injective <| Pi.single_injective _ _
#align linear_map.ker_std_basis LinearMap.ker_stdBasis

theorem proj_comp_stdBasis (i j : ι) : (proj i).comp (stdBasis R φ j) = diag j i := by
  rw [stdBasis_eq_pi_diag, proj_pi]
#align linear_map.proj_comp_std_basis LinearMap.proj_comp_stdBasis

theorem proj_stdBasis_same (i : ι) : (proj i).comp (stdBasis R φ i) = id :=
  LinearMap.ext <| stdBasis_same R φ i
#align linear_map.proj_std_basis_same LinearMap.proj_stdBasis_same

theorem proj_stdBasis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (stdBasis R φ j) = 0 :=
  LinearMap.ext <| stdBasis_ne R φ _ _ h
#align linear_map.proj_std_basis_ne LinearMap.proj_stdBasis_ne

theorem iSup_range_stdBasis_le_iInf_ker_proj (I J : Set ι) (h : Disjoint I J) :
    ⨆ i ∈ I, range (stdBasis R φ i) ≤ ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) := by
  refine iSup_le fun i => iSup_le fun hi => range_le_iff_comap.2 ?_
  simp only [← ker_comp, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  rintro b - j hj
  rw [proj_stdBasis_ne R φ j i, zero_apply]
  rintro rfl
  exact h.le_bot ⟨hi, hj⟩
#align linear_map.supr_range_std_basis_le_infi_ker_proj LinearMap.iSup_range_stdBasis_le_iInf_ker_proj

theorem iInf_ker_proj_le_iSup_range_stdBasis {I : Finset ι} {J : Set ι} (hu : Set.univ ⊆ ↑I ∪ J) :
    ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) ≤ ⨆ i ∈ I, range (stdBasis R φ i) :=
  SetLike.le_def.2
    (by
      intro b hb
      simp only [mem_iInf, mem_ker, proj_apply] at hb
      rw [←
        show (∑ i ∈ I, stdBasis R φ i (b i)) = b by
          ext i
          rw [Finset.sum_apply, ← stdBasis_same R φ i (b i)]
          refine Finset.sum_eq_single i (fun j _ ne => stdBasis_ne _ _ _ _ ne.symm _) ?_
          intro hiI
          rw [stdBasis_same]
          exact hb _ ((hu trivial).resolve_left hiI)]
      exact sum_mem_biSup fun i _ => mem_range_self (stdBasis R φ i) (b i))
#align linear_map.infi_ker_proj_le_supr_range_std_basis LinearMap.iInf_ker_proj_le_iSup_range_stdBasis

theorem iSup_range_stdBasis_eq_iInf_ker_proj {I J : Set ι} (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) (hI : Set.Finite I) :
    ⨆ i ∈ I, range (stdBasis R φ i) = ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) := by
  refine le_antisymm (iSup_range_stdBasis_le_iInf_ker_proj _ _ _ _ hd) ?_
  have : Set.univ ⊆ ↑hI.toFinset ∪ J := by rwa [hI.coe_toFinset]
  refine le_trans (iInf_ker_proj_le_iSup_range_stdBasis R φ this) (iSup_mono fun i => ?_)
  rw [Set.Finite.mem_toFinset]
#align linear_map.supr_range_std_basis_eq_infi_ker_proj LinearMap.iSup_range_stdBasis_eq_iInf_ker_proj

theorem iSup_range_stdBasis [Finite ι] : ⨆ i, range (stdBasis R φ i) = ⊤ := by
  cases nonempty_fintype ι
  convert top_unique (iInf_emptyset.ge.trans <| iInf_ker_proj_le_iSup_range_stdBasis R φ _)
  · rename_i i
    exact ((@iSup_pos _ _ _ fun _ => range <| stdBasis R φ i) <| Finset.mem_univ i).symm
  · rw [Finset.coe_univ, Set.union_empty]
#align linear_map.supr_range_std_basis LinearMap.iSup_range_stdBasis

theorem disjoint_stdBasis_stdBasis (I J : Set ι) (h : Disjoint I J) :
    Disjoint (⨆ i ∈ I, range (stdBasis R φ i)) (⨆ i ∈ J, range (stdBasis R φ i)) := by
  refine
    Disjoint.mono (iSup_range_stdBasis_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right)
      (iSup_range_stdBasis_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right) ?_
  simp only [disjoint_iff_inf_le, SetLike.le_def, mem_iInf, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff]
  rintro b ⟨hI, hJ⟩ i
  classical
    by_cases hiI : i ∈ I
    · by_cases hiJ : i ∈ J
      · exact (h.le_bot ⟨hiI, hiJ⟩).elim
      · exact hJ i hiJ
    · exact hI i hiI
#align linear_map.disjoint_std_basis_std_basis LinearMap.disjoint_stdBasis_stdBasis

theorem stdBasis_eq_single {a : R} :
    (fun i : ι => (stdBasis R (fun _ : ι => R) i) a) = fun i : ι => ↑(Finsupp.single i a) :=
  funext fun i => (Finsupp.single_eq_pi_single i a).symm
#align linear_map.std_basis_eq_single LinearMap.stdBasis_eq_single

end LinearMap

namespace Pi

open LinearMap

open Set

variable {R : Type*}

section Module

variable {η : Type*} {ιs : η → Type*} {Ms : η → Type*}

theorem linearIndependent_stdBasis [Ring R] [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]
    [DecidableEq η] (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σj, ιs j => stdBasis R Ms ji.1 (v ji.1 ji.2) := by
  have hs' : ∀ j : η, LinearIndependent R fun i : ιs j => stdBasis R Ms j (v j i) := by
    intro j
    exact (hs j).map' _ (ker_stdBasis _ _ _)
  apply linearIndependent_iUnion_finite hs'
  intro j J _ hiJ
  have h₀ :
    ∀ j, span R (range fun i : ιs j => stdBasis R Ms j (v j i)) ≤
      LinearMap.range (stdBasis R Ms j) := by
    intro j
    rw [span_le, LinearMap.range_coe]
    apply range_comp_subset_range
  have h₁ :
    span R (range fun i : ιs j => stdBasis R Ms j (v j i)) ≤
      ⨆ i ∈ ({j} : Set _), LinearMap.range (stdBasis R Ms i) := by
    rw [@iSup_singleton _ _ _ fun i => LinearMap.range (stdBasis R (Ms) i)]
    apply h₀
  have h₂ :
    ⨆ j ∈ J, span R (range fun i : ιs j => stdBasis R Ms j (v j i)) ≤
      ⨆ j ∈ J, LinearMap.range (stdBasis R (fun j : η => Ms j) j) :=
    iSup₂_mono fun i _ => h₀ i
  have h₃ : Disjoint (fun i : η => i ∈ ({j} : Set _)) J := by
    convert Set.disjoint_singleton_left.2 hiJ using 0
  exact (disjoint_stdBasis_stdBasis _ _ _ _ h₃).mono h₁ h₂
#align pi.linear_independent_std_basis Pi.linearIndependent_stdBasis

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
  --  Porting note: was
  -- -- The `AddCommMonoid (Π j, Ms j)` instance was hard to find.
  -- -- Defining this in tactic mode seems to shake up instance search enough
  -- -- that it works by itself.
  -- refine Basis.ofRepr (?_ ≪≫ₗ (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)
  -- exact LinearEquiv.piCongrRight fun j => (s j).repr
#align pi.basis Pi.basis

@[simp]
theorem basis_repr_stdBasis [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (stdBasis R _ j (s j i)) = Finsupp.single ⟨j, i⟩ 1 := by
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    -- Porting note: needed to add more lemmas
    simp only [Pi.basis, LinearEquiv.trans_apply, Basis.repr_self, stdBasis_same,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
      Basis.repr_symm_apply, LinearEquiv.coe_mk, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    symm
    -- Porting note: `Sigma.mk.inj` not found in the following, replaced by `Sigma.mk.inj_iff.mp`
    exact
      Finsupp.single_apply_left
        (fun i i' (h : (⟨j, i⟩ : Σj, ιs j) = ⟨j, i'⟩) => eq_of_heq (Sigma.mk.inj_iff.mp h).2) _ _ _
  simp only [Pi.basis, LinearEquiv.trans_apply, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
    LinearEquiv.piCongrRight]
  dsimp
  rw [stdBasis_ne _ _ _ _ (Ne.symm hj), LinearEquiv.map_zero, Finsupp.zero_apply,
    Finsupp.single_eq_of_ne]
  rintro ⟨⟩
  contradiction
#align pi.basis_repr_std_basis Pi.basis_repr_stdBasis

@[simp]
theorem basis_apply [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (ji) :
    Pi.basis s ji = stdBasis R _ ji.1 (s ji.1 ji.2) :=
  Basis.apply_eq_iff.mpr (by simp)
#align pi.basis_apply Pi.basis_apply

@[simp]
theorem basis_repr (s : ∀ j, Basis (ιs j) R (Ms j)) (x) (ji) :
    (Pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
  rfl
#align pi.basis_repr Pi.basis_repr

end Fintype

section

variable [Finite η]
variable (R η)

/-- The basis on `η → R` where the `i`th basis vector is `Function.update 0 i 1`. -/
noncomputable def basisFun : Basis η R (η → R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)
#align pi.basis_fun Pi.basisFun

@[simp]
theorem basisFun_apply [DecidableEq η] (i) : basisFun R η i = stdBasis R (fun _ : η => R) i 1 := by
  simp only [basisFun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    stdBasis_apply]
#align pi.basis_fun_apply Pi.basisFun_apply

@[simp]
theorem basisFun_repr (x : η → R) (i : η) : (Pi.basisFun R η).repr x i = x i := by simp [basisFun]
#align pi.basis_fun_repr Pi.basisFun_repr

@[simp]
theorem basisFun_equivFun : (Pi.basisFun R η).equivFun = LinearEquiv.refl _ _ :=
  Basis.equivFun_ofEquivFun _
#align pi.basis_fun_equiv_fun Pi.basisFun_equivFun

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

namespace Matrix

variable (R : Type*) (m n : Type*) [Fintype m] [Finite n] [Semiring R]

/-- The standard basis of `Matrix m n R`. -/
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
#align matrix.std_basis Matrix.stdBasis

variable {n m}

theorem stdBasis_eq_stdBasisMatrix (i : m) (j : n) [DecidableEq m] [DecidableEq n] :
    stdBasis R m n (i, j) = stdBasisMatrix i j (1 : R) := by
  -- Porting note: `simp` fails to apply `Pi.basis_apply`
  ext a b
  by_cases hi : i = a <;> by_cases hj : j = b
  · simp [stdBasis, hi, hj, Basis.coe_reindex, comp_apply, Equiv.sigmaEquivProd_symm_apply,
      StdBasisMatrix.apply_same]
    erw [Pi.basis_apply]
    simp
  · simp only [stdBasis, hi, Basis.coe_reindex, comp_apply, Equiv.sigmaEquivProd_symm_apply,
      hj, and_false, not_false_iff, StdBasisMatrix.apply_of_ne]
    erw [Pi.basis_apply]
    simp [hj]
  · simp only [stdBasis, hj, Basis.coe_reindex, comp_apply, Equiv.sigmaEquivProd_symm_apply,
      hi, and_true, not_false_iff, StdBasisMatrix.apply_of_ne]
    erw [Pi.basis_apply]
    simp [hi, hj, Ne.symm hi, LinearMap.stdBasis_ne]
  · simp only [stdBasis, Basis.coe_reindex, comp_apply, Equiv.sigmaEquivProd_symm_apply,
      hi, hj, and_self, not_false_iff, StdBasisMatrix.apply_of_ne]
    erw [Pi.basis_apply]
    simp [hi, hj, Ne.symm hj, Ne.symm hi, LinearMap.stdBasis_ne]
#align matrix.std_basis_eq_std_basis_matrix Matrix.stdBasis_eq_stdBasisMatrix

end Matrix
