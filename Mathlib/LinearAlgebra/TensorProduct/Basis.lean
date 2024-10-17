/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FinsuppVectorSpace
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases and dimensionality of tensor products of modules

These can not go into `LinearAlgebra.TensorProduct` since they depend on
`LinearAlgebra.FinsuppVectorSpace` which in turn imports `LinearAlgebra.TensorProduct`.
-/


noncomputable section

open Set LinearMap Submodule

open scoped TensorProduct

section CommSemiring

variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

/-- If `b : ι → M` and `c : κ → N` are bases then so is `fun i ↦ b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`. -/
def Basis.tensorProduct (b : Basis ι S M) (c : Basis κ R N) :
    Basis (ι × κ) S (M ⊗[R] N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.AlgebraTensorModule.congr b.repr c.repr).trans <|
        (finsuppTensorFinsupp R S _ _ _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.AlgebraTensorModule.rid R S S)).symm

@[simp]
theorem Basis.tensorProduct_apply (b : Basis ι S M) (c : Basis κ R N) (i : ι) (j : κ) :
    Basis.tensorProduct b c (i, j) = b i ⊗ₜ c j := by
  simp [Basis.tensorProduct]

theorem Basis.tensorProduct_apply' (b : Basis ι S M) (c : Basis κ R N) (i : ι × κ) :
    Basis.tensorProduct b c i = b i.1 ⊗ₜ c i.2 := by
  simp [Basis.tensorProduct]

@[simp]
theorem Basis.tensorProduct_repr_tmul_apply (b : Basis ι S M) (c : Basis κ R N) (m : M) (n : N)
    (i : ι) (j : κ) :
    (Basis.tensorProduct b c).repr (m ⊗ₜ n) (i, j) = c.repr n j • b.repr m i := by
  simp [Basis.tensorProduct, mul_comm]

variable (S : Type*) [Semiring S] [Algebra R S]

/-- The lift of an `R`-basis of `M` to an `S`-basis of the base change `S ⊗[R] M`. -/
noncomputable
def Basis.baseChange (b : Basis ι R M) : Basis ι S (S ⊗[R] M) :=
  ((Basis.singleton Unit S).tensorProduct b).reindex (Equiv.punitProd ι)

@[simp]
lemma Basis.baseChange_repr_tmul (b : Basis ι R M) (x y i) :
    (b.baseChange S).repr (x ⊗ₜ y) i = b.repr y i • x := by
  simp [Basis.baseChange, Basis.tensorProduct]

@[simp]
lemma Basis.baseChange_apply (b : Basis ι R M) (i) :
    b.baseChange S i = 1 ⊗ₜ b i := by
  simp [Basis.baseChange, Basis.tensorProduct]

variable {ιN ιM : Type*} (𝒞 : Basis ιN R N) (ℬ : Basis ιM R M) (x : M ⊗[R] N)

/-- Elements in M ⊗ N can be represented by sum of elements in M tensor elements of basis of N.-/
lemma TensorProduct.eq_repr_basis_right :
    ∃ (b : ιN →₀ M), (b.sum fun i m => m ⊗ₜ 𝒞 i) = x := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul m n =>
    use 𝒞.repr n |>.mapRange (fun (r : R) => r • m) (by simp)
    simp only [Finsupp.mapRange, zero_tmul, implies_true, Finsupp.onFinset_sum, Function.comp_apply,
      smul_tmul]
    rw [← tmul_sum]
    congr
    conv_rhs => rw [← Basis.linearCombination_repr 𝒞 n]
    rfl
  | add x y hx hy =>
    rcases hx with ⟨x, rfl⟩
    rcases hy with ⟨y, rfl⟩
    use x + y
    rw [Finsupp.sum_add_index]
    · simp
    · intro i _; simp [add_tmul]

/-- Elements in M ⊗ N can be represented by sum of elements of basis of M tensor elements of N.-/
lemma TensorProduct.eq_repr_basis_left :
    ∃ (c : ιM →₀ N), (c.sum fun i n => ℬ i ⊗ₜ c i) = x := by
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right ℬ (TensorProduct.comm R M N x)
  refine ⟨c, ?_⟩
  apply_fun TensorProduct.comm R M N using (TensorProduct.comm R M N).injective
  simp only [Finsupp.sum, map_sum, comm_tmul, ← hc]

include ℬ in
lemma TensorProduct.sum_tmul_basis_right_eq_zero
    (s : Finset ιN) (b : ιN → M) (h : ∑ i ∈ s, b i ⊗ₜ[R] 𝒞 i = 0) :
    ∀ i ∈ s, b i = 0 := by
  classical
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  let I := s.biUnion fun i => (ℬ.repr (b i)).support
  have eq1 := calc (0 : M ⊗[R] N)
      _ = ∑ i ∈ s, b i ⊗ₜ[R] 𝒞 i := h.symm
      _ = ∑ i ∈ s, (∑ k ∈ (ℬ.repr (b i)).support, (ℬ.repr (b i)) k • ℬ k) ⊗ₜ[R] 𝒞 i := by
          refine Finset.sum_congr rfl fun z _ => ?_
          congr
          exact ℬ.linearCombination_repr (b z) |>.symm
      _ = ∑ i ∈ s, ∑ k ∈ (ℬ.repr (b i)).support, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[R] 𝒞 i) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [TensorProduct.sum_tmul]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.smul_tmul']
      _ = ∑ i ∈ s, ∑ k ∈ I, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[R] 𝒞 i) := by
          refine Finset.sum_congr rfl fun j h => ?_
          apply Finset.sum_subset
          · intro i hi
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_biUnion, I] at hi ⊢
            exact ⟨_, h, hi⟩
          · intro i hi1 hi2
            simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not, smul_eq_zero]
              at hi1 hi2 ⊢
            simp only [hi2, zero_smul]
      _ = ∑ k ∈ I, ∑ i ∈ s, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[R] 𝒞 i) := Finset.sum_comm
      _ = ∑ ij ∈ I ×ˢ s, (ℬ.repr (b ij.2)) ij.1 • (ℬ ij.1 ⊗ₜ[R] 𝒞 ij.2) := by
          rw [Finset.sum_product]
      _ = ∑ ij ∈ I ×ˢ s, (ℬ.repr (b ij.2)) ij.1 • 𝒯 ij := by
          refine Finset.sum_congr rfl fun ij _ => ?_
          rw [Basis.tensorProduct_apply]
  have LI := 𝒯.linearIndependent
  rw [linearIndependent_iff'] at LI
  specialize LI (I ×ˢ s) _ eq1.symm
  intro i hi
  rw [← ℬ.linearCombination_repr (b i)]
  change ∑ _ ∈ _, _ = 0
  simp only [LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  refine Finset.sum_eq_zero fun j hj => ?_
  specialize LI ⟨j, i⟩ (by
    simp only [Finset.mem_product, Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, I] at hj ⊢
    refine ⟨⟨_, hi, hj⟩, hi⟩)
  simp [LI]

include 𝒞 in
lemma TensorProduct.sum_tmul_basis_left_eq_zero
    (s : Finset ιM) (c : ιM → N) (h : ∑ i ∈ s, ℬ i ⊗ₜ[R] c i = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  let I := s.biUnion fun i => (𝒞.repr (c i)).support
  have eq1 := calc (0 : M ⊗[R] N)
      _ = ∑ i ∈ s, ℬ i ⊗ₜ[R] c i := h.symm
      _ = ∑ i ∈ s, (ℬ i ⊗ₜ[R] (∑ k ∈ (𝒞.repr (c i)).support, (𝒞.repr (c i)) k • 𝒞 k)) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          congr
          exact 𝒞.linearCombination_repr (c z) |>.symm
      _ = ∑ i ∈ s, ∑ k ∈ (𝒞.repr (c i)).support, (𝒞.repr (c i)) k • (ℬ i ⊗ₜ[R] 𝒞 k) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [TensorProduct.tmul_sum]
          simp_rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      _ = ∑ i ∈ s, ∑ k ∈ I, (𝒞.repr (c i)) k • (ℬ i ⊗ₜ[R] 𝒞 k) := by
          refine Finset.sum_congr rfl fun j h => ?_
          apply Finset.sum_subset
          · intro i hi
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_biUnion, I] at hi ⊢
            exact ⟨_, h, hi⟩
          · intro i hi1 hi2
            simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not, smul_eq_zero]
              at hi1 hi2 ⊢
            simp only [hi2, zero_smul]
      _ = ∑ ij ∈ s ×ˢ I, (𝒞.repr (c ij.1)) ij.2 • (ℬ ij.1 ⊗ₜ[R] 𝒞 ij.2) := by
          rw [Finset.sum_product]
      _ = ∑ ij ∈ s ×ˢ I, (𝒞.repr (c ij.1)) ij.2 • 𝒯 ij := by
          refine Finset.sum_congr rfl fun ij _ => ?_
          rw [Basis.tensorProduct_apply]
  have LI := 𝒯.linearIndependent
  rw [linearIndependent_iff'] at LI
  specialize LI (s ×ˢ I) _ eq1.symm
  intro i hi
  rw [← 𝒞.linearCombination_repr (c i)]
  change ∑ _ ∈ _, _ = 0
  simp only [LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  refine Finset.sum_eq_zero fun j hj => ?_
  specialize LI ⟨i, j⟩ (by
    simp only [Finset.mem_product, Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, I] at hj ⊢
    exact ⟨hi, ⟨_, hi, hj⟩⟩)
  simp [LI]

end CommSemiring

end
