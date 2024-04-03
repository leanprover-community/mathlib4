/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness

/-!

# Some finiteness results of tensor product

This file contains some finiteness results of tensor product.

- `TensorProduct.exists_multiset`, `TensorProduct.exists_finsupp_left`,
  `TensorProduct.exists_finsupp_right`, `TensorProduct.exists_finset`:
  any element of `M ⊗[R] N` can be written as a finite sum of pure tensors.
  See also `TensorProduct.span_tmul_eq_top`.

- `TensorProduct.exists_finite_submodule_left_of_fintype`,
  `TensorProduct.exists_finite_submodule_right_of_fintype`,
  `TensorProduct.exists_finite_submodule_of_fintype` and 21 more:
  any finitely many elements `M ⊗[R] N` is contained in `M' ⊗[R] N'`
  for some finitely generated submodules `M'` and `N'` of `M` and `N`, respectively.
  Each of these 3 functions has 8 variants.

## Tags

tensor product, finitely generated

-/

open scoped TensorProduct

open Submodule

variable {R M N : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

variable {M₁ : Submodule R M} {N₁ : Submodule R N}

namespace TensorProduct

/-- For any element `x` of `M ⊗[R] N`, there exists a (finite) multiset `{ (m_i, n_i) }`
of `M × N`, such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`. -/
theorem exists_multiset (x : M ⊗[R] N) :
    ∃ S : Multiset (M × N), x = (S.map fun i ↦ i.1 ⊗ₜ[R] i.2).sum := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨{(x, y)}, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    exact ⟨Sx + Sy, by rw [Multiset.map_add, Multiset.sum_add, hx, hy]⟩

/-- For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N` such that each `m_i` is distinct (we represent it as an element of `M →₀ N`),
such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`. -/
theorem exists_finsupp_left (x : M ⊗[R] N) :
    ∃ S : M →₀ N, x = S.sum fun m n ↦ m ⊗ₜ[R] n := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨Finsupp.single x y, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    use Sx + Sy
    rw [hx, hy]
    exact (Finsupp.sum_add_index' (by simp) TensorProduct.tmul_add).symm

/-- For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N` such that each `n_i` is distinct (we represent it as an element of `N →₀ M`),
such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`. -/
theorem exists_finsupp_right (x : M ⊗[R] N) :
    ∃ S : N →₀ M, x = S.sum fun n m ↦ m ⊗ₜ[R] n := by
  obtain ⟨S, h⟩ := exists_finsupp_left (TensorProduct.comm R M N x)
  refine ⟨S, (TensorProduct.comm R M N).injective ?_⟩
  simp_rw [h, Finsupp.sum, map_sum]; rfl

/-- For any element `x` of `M ⊗[R] N`, there exists a finite subset `{ (m_i, n_i) }`
of `M × N`, such that `x` is equal to the sum of `m_i ⊗ₜ[R] n_i`. -/
theorem exists_finset (x : M ⊗[R] N) :
    ∃ S : Finset (M × N), x = S.sum fun i ↦ i.1 ⊗ₜ[R] i.2 := by
  obtain ⟨S, h⟩ := exists_finsupp_left x
  use S.graph
  rw [h, Finsupp.sum]
  refine' Finset.sum_nbij' (fun m ↦ ⟨m, S m⟩) Prod.fst .. <;> simp

/-- If `x : ι → M ⊗[R] N` are finitely many elements, then there exists a finitely generated
submodule `M'` of `M` and `x' : ι → M' ⊗[R] N`, whose image in `M ⊗[R] N` is equal to `x`.
There are 8 variants of this function. -/
theorem exists_finite_submodule_left_of_fintype {ι : Type*} [Fintype ι] (x : ι → M ⊗[R] N) :
    ∃ (M' : Submodule R M) (x' : ι → M' ⊗[R] N), Module.Finite R M' ∧
    ∀ (i : ι), M'.subtype.rTensor N (x' i) = x i := by
  classical
  choose S hS using fun i ↦ (x i).exists_multiset
  let T := ((Finset.sum Finset.univ S).map Prod.fst).toFinset
  let M' := span R (T : Set M)
  let f (i : M × N) : M' ⊗[R] N := if h : i.1 ∈ T then ⟨i.1, subset_span h⟩ ⊗ₜ[R] i.2 else 0
  let x' (i : ι) := ((S i).map f).sum
  refine ⟨M', x', inferInstance, fun j ↦ ?_⟩
  simp_rw [x', hS, map_multiset_sum, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun i hi ↦ ?_
  replace hi : i.1 ∈ T := by
    simp only [Multiset.mem_toFinset, Multiset.mem_map, Prod.exists, exists_and_right,
      exists_eq_right, T]
    exact ⟨i.2, Multiset.mem_of_le (Finset.single_le_sum (by simp) (by simp)) hi⟩
  simp_rw [Function.comp_apply, f, dif_pos hi]; rfl

/-- If `x : ι → M ⊗[R] N` are finitely many elements, then there exists a finitely generated
submodule `N'` of `N` and `x' : ι → M ⊗[R] N'`, whose image in `M ⊗[R] N` is equal to `x`.
There are 8 variants of this function. -/
theorem exists_finite_submodule_right_of_fintype {ι : Type*} [Fintype ι] (x : ι → M ⊗[R] N) :
    ∃ (N' : Submodule R N) (x' : ι → M ⊗[R] N'), Module.Finite R N' ∧
    ∀ (i : ι), N'.subtype.lTensor M (x' i) = x i := by
  obtain ⟨N', x', hfin, hx⟩ := exists_finite_submodule_left_of_fintype fun i ↦
    TensorProduct.comm R M N (x i)
  have key : N'.subtype.lTensor M ∘ₗ TensorProduct.comm R N' M =
      (TensorProduct.comm R M N).symm ∘ₗ N'.subtype.rTensor M := ext' fun _ _ ↦ rfl
  refine ⟨N', fun i ↦ TensorProduct.comm R N' M (x' i), hfin, fun i ↦ ?_⟩
  replace hx := congr((TensorProduct.comm R M N).symm $(hx i))
  rw [LinearEquiv.symm_apply_apply] at hx
  simpa only [← hx] using congr($key (x' i))

/-- If `x : ι → M ⊗[R] N` are finitely many elements, then there are finitely generated
submodules `M'` and `N'` of `M` and `N`, respectively, and `x' : ι → M' ⊗[R] N'`,
whose image in `M ⊗[R] N` is equal to `x`. There are 8 variants of this function. -/
theorem exists_finite_submodule_of_fintype {ι : Type*} [Fintype ι] (x : ι → M ⊗[R] N) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (x' : ι → M' ⊗[R] N'),
    Module.Finite R M' ∧ Module.Finite R N' ∧
    ∀ (i : ι), TensorProduct.map M'.subtype N'.subtype (x' i) = x i := by
  obtain ⟨M', x', h1, hx⟩ := exists_finite_submodule_left_of_fintype x
  obtain ⟨N', x'', h2, hx'⟩ := exists_finite_submodule_right_of_fintype x'
  refine ⟨M', N', x'', h1, h2, fun i ↦ ?_⟩
  rw [← hx, ← hx', ← LinearMap.rTensor_comp_lTensor]; rfl

theorem exists_finite_submodule_left_of_fintype' {ι : Type*} [Fintype ι] (x : ι → M₁ ⊗[R] N₁) :
    ∃ (M' : Submodule R M) (x' : ι → M' ⊗[R] N₁) (hM : M' ≤ M₁), Module.Finite R M' ∧
    ∀ (i : ι), (inclusion hM).rTensor N₁ (x' i) = x i := by
  obtain ⟨M', x', hfin, hx⟩ := exists_finite_submodule_left_of_fintype x
  refine ⟨_, (M₁.subtype.submoduleMap M').rTensor N₁ ∘ x', map_subtype_le _ _, .map _ _, fun i ↦ ?_⟩
  have key : M'.subtype.rTensor N₁ =
      (inclusion (map_subtype_le _ _)).rTensor N₁ ∘ₗ (M₁.subtype.submoduleMap M').rTensor N₁ :=
    ext' fun _ _ ↦ rfl
  rw [← hx, key]; rfl

theorem exists_finite_submodule_right_of_fintype' {ι : Type*} [Fintype ι] (x : ι → M₁ ⊗[R] N₁) :
    ∃ (N' : Submodule R N) (x' : ι → M₁ ⊗[R] N') (hN : N' ≤ N₁), Module.Finite R N' ∧
    ∀ (i : ι), (inclusion hN).lTensor M₁ (x' i) = x i := by
  obtain ⟨N', x', hfin, hx⟩ := exists_finite_submodule_right_of_fintype x
  refine ⟨_, (N₁.subtype.submoduleMap N').lTensor M₁ ∘ x', map_subtype_le _ _, .map _ _, fun i ↦ ?_⟩
  have key : N'.subtype.lTensor M₁ =
      (inclusion (map_subtype_le _ _)).lTensor M₁ ∘ₗ (N₁.subtype.submoduleMap N').lTensor M₁ :=
    ext' fun _ _ ↦ rfl
  rw [← hx, key]; rfl

theorem exists_finite_submodule_of_fintype' {ι : Type*} [Fintype ι] (x : ι → M₁ ⊗[R] N₁) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (x' : ι → M' ⊗[R] N') (hM : M' ≤ M₁) (hN : N' ≤ N₁),
    Module.Finite R M' ∧ Module.Finite R N' ∧
    ∀ (i : ι), TensorProduct.map (inclusion hM) (inclusion hN) (x' i) = x i := by
  obtain ⟨M', x', hM, h1, hx⟩ := exists_finite_submodule_left_of_fintype' x
  obtain ⟨N', x'', hN, h2, hx'⟩ := exists_finite_submodule_right_of_fintype' x'
  refine ⟨M', N', x'', hM, hN, h1, h2, fun i ↦ ?_⟩
  rw [← hx, ← hx', ← LinearMap.rTensor_comp_lTensor]; rfl

theorem exists_finite_submodule_left_of_finsupp {ι : Type*} (x : ι →₀ M ⊗[R] N) :
    ∃ (M' : Submodule R M) (x' : ι →₀ M' ⊗[R] N), Module.Finite R M' ∧
    ∀ (i : ι), M'.subtype.rTensor N (x' i) = x i := by
  classical
  obtain ⟨M', x', hfin, hx⟩ := exists_finite_submodule_left_of_fintype fun i : x.support ↦ x i
  refine ⟨M', (Finsupp.equivFunOnFinite.symm x').extendDomain, hfin, fun i ↦ ?_⟩
  by_cases h : i ∈ x.support
  · simp [h, hx]
  simp [h, Finsupp.not_mem_support_iff.1 h]

theorem exists_finite_submodule_right_of_finsupp {ι : Type*} (x : ι →₀ M ⊗[R] N) :
    ∃ (N' : Submodule R N) (x' : ι →₀ M ⊗[R] N'), Module.Finite R N' ∧
    ∀ (i : ι), N'.subtype.lTensor M (x' i) = x i := by
  classical
  obtain ⟨N', x', hfin, hx⟩ := exists_finite_submodule_right_of_fintype fun i : x.support ↦ x i
  refine ⟨N', (Finsupp.equivFunOnFinite.symm x').extendDomain, hfin, fun i ↦ ?_⟩
  by_cases h : i ∈ x.support
  · simp [h, hx]
  simp [h, Finsupp.not_mem_support_iff.1 h]

theorem exists_finite_submodule_of_finsupp {ι : Type*} (x : ι →₀ M ⊗[R] N) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (x' : ι →₀ M' ⊗[R] N'),
    Module.Finite R M' ∧ Module.Finite R N' ∧
    ∀ (i : ι), TensorProduct.map M'.subtype N'.subtype (x' i) = x i := by
  obtain ⟨M', x', h1, hx⟩ := exists_finite_submodule_left_of_finsupp x
  obtain ⟨N', x'', h2, hx'⟩ := exists_finite_submodule_right_of_finsupp x'
  refine ⟨M', N', x'', h1, h2, fun i ↦ ?_⟩
  rw [← hx, ← hx', ← LinearMap.rTensor_comp_lTensor]; rfl

theorem exists_finite_submodule_left_of_finsupp' {ι : Type*} (x : ι →₀ M₁ ⊗[R] N₁) :
    ∃ (M' : Submodule R M) (x' : ι →₀ M' ⊗[R] N₁) (hM : M' ≤ M₁), Module.Finite R M' ∧
    ∀ (i : ι), (inclusion hM).rTensor N₁ (x' i) = x i := by
  classical
  obtain ⟨M', x', hM, hfin, hx⟩ := exists_finite_submodule_left_of_fintype' fun i : x.support ↦ x i
  refine ⟨M', (Finsupp.equivFunOnFinite.symm x').extendDomain, hM, hfin, fun i ↦ ?_⟩
  by_cases h : i ∈ x.support
  · simp [h, hx]
  simp [h, Finsupp.not_mem_support_iff.1 h]

theorem exists_finite_submodule_right_of_finsupp' {ι : Type*} (x : ι →₀ M₁ ⊗[R] N₁) :
    ∃ (N' : Submodule R N) (x' : ι →₀ M₁ ⊗[R] N') (hN : N' ≤ N₁), Module.Finite R N' ∧
    ∀ (i : ι), (inclusion hN).lTensor M₁ (x' i) = x i := by
  classical
  obtain ⟨N', x', hN, hfin, hx⟩ := exists_finite_submodule_right_of_fintype' fun i : x.support ↦ x i
  refine ⟨N', (Finsupp.equivFunOnFinite.symm x').extendDomain, hN, hfin, fun i ↦ ?_⟩
  by_cases h : i ∈ x.support
  · simp [h, hx]
  simp [h, Finsupp.not_mem_support_iff.1 h]

theorem exists_finite_submodule_of_finsupp' {ι : Type*} (x : ι →₀ M₁ ⊗[R] N₁) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (x' : ι →₀ M' ⊗[R] N')
    (hM : M' ≤ M₁) (hN : N' ≤ N₁), Module.Finite R M' ∧ Module.Finite R N' ∧
    ∀ (i : ι), TensorProduct.map (inclusion hM) (inclusion hN) (x' i) = x i := by
  obtain ⟨M', x', hM, h1, hx⟩ := exists_finite_submodule_left_of_finsupp' x
  obtain ⟨N', x'', hN, h2, hx'⟩ := exists_finite_submodule_right_of_finsupp' x'
  refine ⟨M', N', x'', hM, hN, h1, h2, fun i ↦ ?_⟩
  rw [← hx, ← hx', ← LinearMap.rTensor_comp_lTensor]; rfl

theorem exists_finite_submodule_left_of_pair (x y : M ⊗[R] N) :
    ∃ (M' : Submodule R M) (x' y' : M' ⊗[R] N), Module.Finite R M' ∧
    M'.subtype.rTensor N x' = x ∧ M'.subtype.rTensor N y' = y := by
  obtain ⟨M', x', hfin, hx⟩ := exists_finite_submodule_left_of_fintype ![x, y]
  exact ⟨M', x' 0, x' 1, hfin, hx 0, hx 1⟩

theorem exists_finite_submodule_right_of_pair (x y : M ⊗[R] N) :
    ∃ (N' : Submodule R N) (x' y' : M ⊗[R] N'), Module.Finite R N' ∧
    N'.subtype.lTensor M x' = x ∧ N'.subtype.lTensor M y' = y := by
  obtain ⟨N', x', hfin, hx⟩ := exists_finite_submodule_right_of_fintype ![x, y]
  exact ⟨N', x' 0, x' 1, hfin, hx 0, hx 1⟩

theorem exists_finite_submodule_of_pair (x y : M ⊗[R] N) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (x' y' : M' ⊗[R] N'),
    Module.Finite R M' ∧ Module.Finite R N' ∧
    TensorProduct.map M'.subtype N'.subtype x' = x ∧
    TensorProduct.map M'.subtype N'.subtype y' = y := by
  obtain ⟨M', N', x', h1, h2, hx⟩ := exists_finite_submodule_of_fintype ![x, y]
  exact ⟨M', N', x' 0, x' 1, h1, h2, hx 0, hx 1⟩

theorem exists_finite_submodule_left_of_pair' (x y : M₁ ⊗[R] N₁) :
    ∃ (M' : Submodule R M) (x' y' : M' ⊗[R] N₁) (hM : M' ≤ M₁), Module.Finite R M' ∧
    (inclusion hM).rTensor N₁ x' = x ∧ (inclusion hM).rTensor N₁ y' = y := by
  obtain ⟨M', x', hM, hfin, hx⟩ := exists_finite_submodule_left_of_fintype' ![x, y]
  exact ⟨M', x' 0, x' 1, hM, hfin, hx 0, hx 1⟩

theorem exists_finite_submodule_right_of_pair' (x y : M₁ ⊗[R] N₁) :
    ∃ (N' : Submodule R N) (x' y' : M₁ ⊗[R] N') (hN : N' ≤ N₁), Module.Finite R N' ∧
    (inclusion hN).lTensor M₁ x' = x ∧ (inclusion hN).lTensor M₁ y' = y := by
  obtain ⟨N', x', hN, hfin, hx⟩ := exists_finite_submodule_right_of_fintype' ![x, y]
  exact ⟨N', x' 0, x' 1, hN, hfin, hx 0, hx 1⟩

theorem exists_finite_submodule_of_pair' (x y : M₁ ⊗[R] N₁) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (x' y' : M' ⊗[R] N') (hM : M' ≤ M₁) (hN : N' ≤ N₁),
    Module.Finite R M' ∧ Module.Finite R N' ∧
    TensorProduct.map (inclusion hM) (inclusion hN) x' = x ∧
    TensorProduct.map (inclusion hM) (inclusion hN) y' = y := by
  obtain ⟨M', N', x', hM, hN, h1, h2, hx⟩ := exists_finite_submodule_of_fintype' ![x, y]
  exact ⟨M', N', x' 0, x' 1, hM, hN, h1, h2, hx 0, hx 1⟩

theorem exists_finite_submodule_left (x : M ⊗[R] N) :
    ∃ (M' : Submodule R M) (x' : M' ⊗[R] N), Module.Finite R M' ∧
    M'.subtype.rTensor N x' = x := by
  obtain ⟨M', x', hfin, hx⟩ := exists_finite_submodule_left_of_fintype ![x]
  exact ⟨M', x' 0, hfin, hx 0⟩

theorem exists_finite_submodule_right (x : M ⊗[R] N) :
    ∃ (N' : Submodule R N) (x' : M ⊗[R] N'), Module.Finite R N' ∧
    N'.subtype.lTensor M x' = x := by
  obtain ⟨N', x', hfin, hx⟩ := exists_finite_submodule_right_of_fintype ![x]
  exact ⟨N', x' 0, hfin, hx 0⟩

theorem exists_finite_submodule (x : M ⊗[R] N) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (x' : M' ⊗[R] N'),
    Module.Finite R M' ∧ Module.Finite R N' ∧
    TensorProduct.map M'.subtype N'.subtype x' = x := by
  obtain ⟨M', N', x', h1, h2, hx⟩ := exists_finite_submodule_of_fintype ![x]
  exact ⟨M', N', x' 0, h1, h2, hx 0⟩

theorem exists_finite_submodule_left' (x : M₁ ⊗[R] N₁) :
    ∃ (M' : Submodule R M) (x' : M' ⊗[R] N₁) (hM : M' ≤ M₁), Module.Finite R M' ∧
    (inclusion hM).rTensor N₁ x' = x := by
  obtain ⟨M', x', hM, hfin, hx⟩ := exists_finite_submodule_left_of_fintype' ![x]
  exact ⟨M', x' 0, hM, hfin, hx 0⟩

theorem exists_finite_submodule_right' (x : M₁ ⊗[R] N₁) :
    ∃ (N' : Submodule R N) (x' : M₁ ⊗[R] N') (hN : N' ≤ N₁), Module.Finite R N' ∧
    (inclusion hN).lTensor M₁ x' = x := by
  obtain ⟨N', x', hN, hfin, hx⟩ := exists_finite_submodule_right_of_fintype' ![x]
  exact ⟨N', x' 0, hN, hfin, hx 0⟩

theorem exists_finite_submodule' (x : M₁ ⊗[R] N₁) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (x' : M' ⊗[R] N') (hM : M' ≤ M₁) (hN : N' ≤ N₁),
    Module.Finite R M' ∧ Module.Finite R N' ∧
    TensorProduct.map (inclusion hM) (inclusion hN) x' = x := by
  obtain ⟨M', N', x', hM, hN, h1, h2, hx⟩ := exists_finite_submodule_of_fintype' ![x]
  exact ⟨M', N', x' 0, hM, hN, h1, h2, hx 0⟩

end TensorProduct
