/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module linear_algebra.std_basis
! leanprover-community/mathlib commit f2edd790f6c6e1d660515f76768f63cb717434d7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basis
import Mathbin.LinearAlgebra.Basis
import Mathbin.LinearAlgebra.Pi

/-!
# The standard basis

This file defines the standard basis `pi.basis (s : ∀ j, basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of Π j, M j`. The basis vectors are given by
`pi.basis s ⟨j, i⟩ j' = linear_map.std_basis R M j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `pi.basis_fun`.

To give a concrete example, `linear_map.std_basis R (λ (i : fin 3), R) i 1`
gives the `i`th unit basis vector in `R³`, and `pi.basis_fun R (fin 3)` proves
this is a basis over `fin 3 → R`.

## Main definitions

 - `linear_map.std_basis R M`: if `x` is a basis vector of `M i`, then
   `linear_map.std_basis R M i x` is the `i`th standard basis vector of `Π i, M i`.
 - `pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
 - `pi.basis_fun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
   `pi.basis_fun R η i j = if i = j then 1 else 0`.
 - `matrix.std_basis R n m`: the standard basis on `matrix n m R`, given by
   `matrix.std_basis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/


open Function Submodule

open BigOperators

namespace LinearMap

variable (R : Type _) {ι : Type _} [Semiring R] (φ : ι → Type _) [∀ i, AddCommMonoid (φ i)]
  [∀ i, Module R (φ i)] [DecidableEq ι]

/-- The standard basis of the product of `φ`. -/
def stdBasis : ∀ i : ι, φ i →ₗ[R] ∀ i, φ i :=
  single
#align linear_map.std_basis LinearMap.stdBasis

theorem stdBasis_apply (i : ι) (b : φ i) : stdBasis R φ i b = update 0 i b :=
  rfl
#align linear_map.std_basis_apply LinearMap.stdBasis_apply

@[simp]
theorem stdBasis_apply' (i i' : ι) : (stdBasis R (fun _x : ι => R) i) 1 i' = ite (i = i') 1 0 :=
  by
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

theorem stdBasis_eq_pi_diag (i : ι) : stdBasis R φ i = pi (diag i) :=
  by
  ext (x j)
  convert(update_apply 0 x i j _).symm
  rfl
#align linear_map.std_basis_eq_pi_diag LinearMap.stdBasis_eq_pi_diag

theorem ker_stdBasis (i : ι) : ker (stdBasis R φ i) = ⊥ :=
  ker_eq_bot_of_injective <| Pi.single_injective _ _
#align linear_map.ker_std_basis LinearMap.ker_stdBasis

theorem proj_comp_stdBasis (i j : ι) : (proj i).comp (stdBasis R φ j) = diag j i := by
  rw [std_basis_eq_pi_diag, proj_pi]
#align linear_map.proj_comp_std_basis LinearMap.proj_comp_stdBasis

theorem proj_stdBasis_same (i : ι) : (proj i).comp (stdBasis R φ i) = id :=
  LinearMap.ext <| stdBasis_same R φ i
#align linear_map.proj_std_basis_same LinearMap.proj_stdBasis_same

theorem proj_stdBasis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (stdBasis R φ j) = 0 :=
  LinearMap.ext <| stdBasis_ne R φ _ _ h
#align linear_map.proj_std_basis_ne LinearMap.proj_stdBasis_ne

theorem supᵢ_range_stdBasis_le_infᵢ_ker_proj (I J : Set ι) (h : Disjoint I J) :
    (⨆ i ∈ I, range (stdBasis R φ i)) ≤ ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) :=
  by
  refine' supᵢ_le fun i => supᵢ_le fun hi => range_le_iff_comap.2 _
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_infi, mem_infi]
  rintro b - j hj
  rw [proj_std_basis_ne R φ j i, zero_apply]
  rintro rfl
  exact h.le_bot ⟨hi, hj⟩
#align linear_map.supr_range_std_basis_le_infi_ker_proj LinearMap.supᵢ_range_stdBasis_le_infᵢ_ker_proj

theorem infᵢ_ker_proj_le_supᵢ_range_stdBasis {I : Finset ι} {J : Set ι} (hu : Set.univ ⊆ ↑I ∪ J) :
    (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i)) ≤ ⨆ i ∈ I, range (stdBasis R φ i) :=
  SetLike.le_def.2
    (by
      intro b hb
      simp only [mem_infi, mem_ker, proj_apply] at hb
      rw [←
        show (∑ i in I, std_basis R φ i (b i)) = b by
          ext i
          rw [Finset.sum_apply, ← std_basis_same R φ i (b i)]
          refine' Finset.sum_eq_single i (fun j hjI ne => std_basis_ne _ _ _ _ Ne.symm _) _
          intro hiI
          rw [std_basis_same]
          exact hb _ ((hu trivial).resolve_left hiI)]
      exact sum_mem_bsupr fun i hi => mem_range_self (std_basis R φ i) (b i))
#align linear_map.infi_ker_proj_le_supr_range_std_basis LinearMap.infᵢ_ker_proj_le_supᵢ_range_stdBasis

theorem supᵢ_range_stdBasis_eq_infᵢ_ker_proj {I J : Set ι} (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) (hI : Set.Finite I) :
    (⨆ i ∈ I, range (stdBasis R φ i)) = ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) :=
  by
  refine' le_antisymm (supr_range_std_basis_le_infi_ker_proj _ _ _ _ hd) _
  have : Set.univ ⊆ ↑hI.to_finset ∪ J := by rwa [hI.coe_to_finset]
  refine' le_trans (infi_ker_proj_le_supr_range_std_basis R φ this) (supᵢ_mono fun i => _)
  rw [Set.Finite.mem_toFinset]
  exact le_rfl
#align linear_map.supr_range_std_basis_eq_infi_ker_proj LinearMap.supᵢ_range_stdBasis_eq_infᵢ_ker_proj

theorem supᵢ_range_stdBasis [Finite ι] : (⨆ i, range (stdBasis R φ i)) = ⊤ :=
  by
  cases nonempty_fintype ι
  convert top_unique (infi_emptyset.ge.trans <| infi_ker_proj_le_supr_range_std_basis R φ _)
  ·
    exact
      funext fun i =>
        ((@supᵢ_pos _ _ _ fun h => range <| std_basis R φ i) <| Finset.mem_univ i).symm
  · rw [Finset.coe_univ, Set.union_empty]
#align linear_map.supr_range_std_basis LinearMap.supᵢ_range_stdBasis

theorem disjoint_stdBasis_stdBasis (I J : Set ι) (h : Disjoint I J) :
    Disjoint (⨆ i ∈ I, range (stdBasis R φ i)) (⨆ i ∈ J, range (stdBasis R φ i)) :=
  by
  refine'
    Disjoint.mono (supr_range_std_basis_le_infi_ker_proj _ _ _ _ <| disjoint_compl_right)
      (supr_range_std_basis_le_infi_ker_proj _ _ _ _ <| disjoint_compl_right) _
  simp only [disjoint_iff_inf_le, SetLike.le_def, mem_infi, mem_inf, mem_ker, mem_bot, proj_apply,
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
    (fun i : ι => (stdBasis R (fun _ : ι => R) i) a) = fun i : ι => Finsupp.single i a :=
  funext fun i => (Finsupp.single_eq_pi_single i a).symm
#align linear_map.std_basis_eq_single LinearMap.stdBasis_eq_single

end LinearMap

namespace Pi

open LinearMap

open Set

variable {R : Type _}

section Module

variable {η : Type _} {ιs : η → Type _} {Ms : η → Type _}

theorem linearIndependent_stdBasis [Ring R] [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]
    [DecidableEq η] (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σj, ιs j => stdBasis R Ms ji.1 (v ji.1 ji.2) :=
  by
  have hs' : ∀ j : η, LinearIndependent R fun i : ιs j => std_basis R Ms j (v j i) :=
    by
    intro j
    exact (hs j).map' _ (ker_std_basis _ _ _)
  apply linearIndependent_unionᵢ_finite hs'
  · intro j J _ hiJ
    simp [(Set.unionᵢ.equations._eqn_1 _).symm, Submodule.span_image, Submodule.span_unionᵢ]
    have h₀ :
      ∀ j, span R (range fun i : ιs j => std_basis R Ms j (v j i)) ≤ range (std_basis R Ms j) :=
      by
      intro j
      rw [span_le, LinearMap.range_coe]
      apply range_comp_subset_range
    have h₁ :
      span R (range fun i : ιs j => std_basis R Ms j (v j i)) ≤
        ⨆ i ∈ {j}, range (std_basis R Ms i) :=
      by
      rw [@supᵢ_singleton _ _ _ fun i => LinearMap.range (std_basis R (fun j : η => Ms j) i)]
      apply h₀
    have h₂ :
      (⨆ j ∈ J, span R (range fun i : ιs j => std_basis R Ms j (v j i))) ≤
        ⨆ j ∈ J, range (std_basis R (fun j : η => Ms j) j) :=
      supᵢ₂_mono fun i _ => h₀ i
    have h₃ : Disjoint (fun i : η => i ∈ {j}) J := by
      convert Set.disjoint_singleton_left.2 hiJ using 0
    exact (disjoint_std_basis_std_basis _ _ _ _ h₃).mono h₁ h₂
#align pi.linear_independent_std_basis Pi.linearIndependent_stdBasis

variable [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]

variable [Fintype η]

section

open LinearEquiv

/-- `pi.basis (s : ∀ j, basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on `Π j, Ms j`
given by `s j` on each component.

For the standard basis over `R` on the finite-dimensional space `η → R` see `pi.basis_fun`.
-/
protected noncomputable def basis (s : ∀ j, Basis (ιs j) R (Ms j)) :
    Basis (Σj, ιs j) R (∀ j, Ms j) :=
  by
  -- The `add_comm_monoid (Π j, Ms j)` instance was hard to find.
  -- Defining this in tactic mode seems to shake up instance search enough that it works by itself.
  refine' Basis.ofRepr (_ ≪≫ₗ (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)
  exact LinearEquiv.piCongrRight fun j => (s j).repr
#align pi.basis Pi.basis

@[simp]
theorem basis_repr_stdBasis [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (stdBasis R _ j (s j i)) = Finsupp.single ⟨j, i⟩ 1 :=
  by
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    simp only [Pi.basis, LinearEquiv.trans_apply, Basis.repr_self, std_basis_same,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply]
    symm
    exact
      Finsupp.single_apply_left
        (fun i i' (h : (⟨j, i⟩ : Σj, ιs j) = ⟨j, i'⟩) => eq_of_hEq (Sigma.mk.inj h).2) _ _ _
  simp only [Pi.basis, LinearEquiv.trans_apply, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
    LinearEquiv.piCongrRight]
  dsimp
  rw [std_basis_ne _ _ _ _ (Ne.symm hj), LinearEquiv.map_zero, Finsupp.zero_apply,
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

end

section

variable (R η)

/-- The basis on `η → R` where the `i`th basis vector is `function.update 0 i 1`. -/
noncomputable def basisFun : Basis η R (∀ j : η, R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)
#align pi.basis_fun Pi.basisFun

@[simp]
theorem basisFun_apply [DecidableEq η] (i) : basisFun R η i = stdBasis R (fun i : η => R) i 1 := by
  simp only [basis_fun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    std_basis_apply]
#align pi.basis_fun_apply Pi.basisFun_apply

@[simp]
theorem basisFun_repr (x : η → R) (i : η) : (Pi.basisFun R η).repr x i = x i := by simp [basis_fun]
#align pi.basis_fun_repr Pi.basisFun_repr

end

end Module

end Pi

namespace Matrix

variable (R : Type _) (m n : Type _) [Fintype m] [Fintype n] [Semiring R]

/-- The standard basis of `matrix m n R`. -/
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun i : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
#align matrix.std_basis Matrix.stdBasis

variable {n m}

theorem stdBasis_eq_stdBasisMatrix (i : n) (j : m) [DecidableEq n] [DecidableEq m] :
    stdBasis R n m (i, j) = stdBasisMatrix i j (1 : R) :=
  by
  ext (a b)
  by_cases hi : i = a <;> by_cases hj : j = b
  · simp [std_basis, hi, hj]
  · simp [std_basis, hi, hj, Ne.symm hj, LinearMap.stdBasis_ne]
  · simp [std_basis, hi, hj, Ne.symm hi, LinearMap.stdBasis_ne]
  · simp [std_basis, hi, hj, Ne.symm hj, Ne.symm hi, LinearMap.stdBasis_ne]
#align matrix.std_basis_eq_std_basis_matrix Matrix.stdBasis_eq_stdBasisMatrix

end Matrix

