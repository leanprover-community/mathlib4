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

variable (K : Type*) [CommSemiring K] (B C: Type*) [AddCommMonoid B] [Module K B]
    [AddCommMonoid C] [Module K C]

/-- Elements in B ⊗ C can be represented by sum of elements in B tensor elements of basis of C.-/
lemma TensorProduct.eq_repr_basis_right
    {ιC ιB : Type*} (𝒞 : Basis ιC K C) (ℬ : Basis ιB K B) (x : B ⊗[K] C) :
    ∃ (s : Finset ιC) (b : ιC → B), ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = x := by
  classical
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  have eq1 := calc x
      _ = ∑ ij ∈ (𝒯.repr x).support, (𝒯.repr x) ij • 𝒯 ij := 𝒯.linearCombination_repr x |>.symm
      _ = ∑ ij ∈ (𝒯.repr x).support, (𝒯.repr x) (ij.1, ij.2) • 𝒯 (ij.1, ij.2) :=
          Finset.sum_congr rfl <| by simp
      _ = ∑ i ∈ (𝒯.repr x).support.image Prod.fst, ∑ j ∈ (𝒯.repr x).support.image Prod.snd,
            𝒯.repr x (i, j) • 𝒯 (i, j) := by
          rw [← Finset.sum_product']
          apply Finset.sum_subset
          · rintro ⟨i, j⟩ hij
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_product, Finset.mem_image,
              Prod.exists, exists_and_right, exists_eq_right, Subtype.exists, 𝒯] at hij ⊢
            exact ⟨⟨j, hij⟩, ⟨i, hij⟩⟩
          · rintro ⟨i, j⟩ hij1 hij2
            simp only [Finset.mem_product, Finset.mem_image, Finsupp.mem_support_iff, ne_eq,
              Prod.exists, exists_and_right, exists_eq_right, Subtype.exists, Decidable.not_not,
              Basis.tensorProduct_apply, smul_eq_zero, 𝒯] at hij1 hij2 ⊢
            rw [hij2]
            simp only [zero_smul]
      _ = ∑ j ∈ (𝒯.repr x).support.image Prod.snd, ∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            𝒯.repr x (i, j) • 𝒯 (i, j) := Finset.sum_comm
      _ = ∑ j ∈ (𝒯.repr x).support.image Prod.snd, ∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            𝒯.repr x (i, j) • (ℬ i ⊗ₜ[K] 𝒞 j) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          simp only [𝒯, Basis.tensorProduct_apply]
      _ =  ∑ j ∈ (𝒯.repr x).support.image Prod.snd, ∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            (𝒯.repr x (i, j) • ℬ i) ⊗ₜ[K] 𝒞 j := by
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.smul_tmul']
      _ =  ∑ j ∈ (𝒯.repr x).support.image Prod.snd, (∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            (𝒯.repr x (i, j) • ℬ i)) ⊗ₜ[K] 𝒞 j := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.sum_tmul]
  exact ⟨_, _, eq1.symm⟩

/-- Elements in B ⊗ C can be represented by sum of elements of basis of B tensor elements of C.-/
lemma TensorProduct.eq_repr_basis_left
    {ιB ιC: Type*} (ℬ : Basis ιB K B) (𝒞 : Basis ιC K C) (x : B ⊗[K] C) :
    ∃ (s : Finset ιB) (c : ιB → C), ∑ i ∈ s, ℬ i ⊗ₜ[K] c i = x := by
  classical
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  have eq1 := calc x
      _ = ∑ ij ∈ (𝒯.repr x).support, (𝒯.repr x) ij • 𝒯 ij := 𝒯.linearCombination_repr x |>.symm
      _ = ∑ ij ∈ (𝒯.repr x).support, (𝒯.repr x) (ij.1, ij.2) • 𝒯 (ij.1, ij.2) :=
          Finset.sum_congr rfl <| by simp
      _ = ∑ i ∈ (𝒯.repr x).support.image Prod.fst, ∑ j ∈ (𝒯.repr x).support.image Prod.snd,
            𝒯.repr x (i, j) • 𝒯 (i, j) := by
          rw [← Finset.sum_product']
          apply Finset.sum_subset
          · rintro ⟨i, j⟩ hij
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_product, Finset.mem_image,
              Prod.exists, exists_and_right, exists_eq_right, Subtype.exists, 𝒯] at hij ⊢
            exact ⟨⟨j, hij⟩, ⟨i, hij⟩⟩
          · rintro ⟨i, j⟩ hij1 hij2
            simp only [Finset.mem_product, Finset.mem_image, Finsupp.mem_support_iff, ne_eq,
              Prod.exists, exists_and_right, exists_eq_right, Subtype.exists, Decidable.not_not,
              Basis.tensorProduct_apply, smul_eq_zero, 𝒯] at hij1 hij2 ⊢
            rw [hij2]
            simp only [zero_smul]
      _ = ∑ i ∈ (𝒯.repr x).support.image Prod.fst, ∑ j ∈ (𝒯.repr x).support.image Prod.snd,
            𝒯.repr x (i, j) • (ℬ i ⊗ₜ[K] 𝒞 j) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          simp only [𝒯, Basis.tensorProduct_apply]
      _ =  ∑ i ∈ (𝒯.repr x).support.image Prod.fst, ∑ j ∈ (𝒯.repr x).support.image Prod.snd,
            ℬ i ⊗ₜ[K] (𝒯.repr x (i, j) • 𝒞 j : C) := by
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      _ =  ∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            ℬ i ⊗ₜ[K] (∑ j ∈ (𝒯.repr x).support.image Prod.snd, (𝒯.repr x (i, j) • 𝒞 j)) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.tmul_sum]
  exact ⟨_, _, eq1.symm⟩

lemma TensorProduct.sum_tmul_basis_right_eq_zero
    {ιC ιB: Type*} (𝒞 : Basis ιC K C) (ℬ : Basis ιB K B)
    (s : Finset ιC) (b : ιC → B)
    (h : ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = 0) :
    ∀ i ∈ s, b i = 0 := by
  classical
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  let I := s.biUnion fun i => (ℬ.repr (b i)).support
  have eq1 := calc (0 : B ⊗[K] C)
      _ = ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i := h.symm
      _ = ∑ i ∈ s, (∑ k ∈ (ℬ.repr (b i)).support, (ℬ.repr (b i)) k • ℬ k) ⊗ₜ[K] 𝒞 i := by
          refine Finset.sum_congr rfl fun z _ => ?_
          congr
          exact ℬ.linearCombination_repr (b z) |>.symm
      _ = ∑ i ∈ s, ∑ k ∈ (ℬ.repr (b i)).support, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[K] 𝒞 i) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [TensorProduct.sum_tmul]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.smul_tmul']
      _ = ∑ i ∈ s, ∑ k ∈ I, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[K] 𝒞 i) := by
          refine Finset.sum_congr rfl fun j h => ?_
          apply Finset.sum_subset
          · intro i hi
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_biUnion, I] at hi ⊢
            exact ⟨_, h, hi⟩
          · intro i hi1 hi2
            simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not, smul_eq_zero]
              at hi1 hi2 ⊢
            simp only [hi2, zero_smul]
      _ = ∑ k ∈ I, ∑ i ∈ s, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[K] 𝒞 i) := Finset.sum_comm
      _ = ∑ ij ∈ I ×ˢ s, (ℬ.repr (b ij.2)) ij.1 • (ℬ ij.1 ⊗ₜ[K] 𝒞 ij.2) := by
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

lemma TensorProduct.sum_tmul_basis_left_eq_zero
    {ιB ιC: Type*} (ℬ : Basis ιB K B) (𝒞 : Basis ιC K C)
    (s : Finset ιB) (c : ιB → C)
    (h : ∑ i ∈ s, ℬ i ⊗ₜ[K] c i = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  let I := s.biUnion fun i => (𝒞.repr (c i)).support
  have eq1 := calc (0 : B ⊗[K] C)
      _ = ∑ i ∈ s, ℬ i ⊗ₜ[K] c i := h.symm
      _ = ∑ i ∈ s, (ℬ i ⊗ₜ[K] (∑ k ∈ (𝒞.repr (c i)).support, (𝒞.repr (c i)) k • 𝒞 k)) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          congr
          exact 𝒞.linearCombination_repr (c z) |>.symm
      _ = ∑ i ∈ s, ∑ k ∈ (𝒞.repr (c i)).support, (𝒞.repr (c i)) k • (ℬ i ⊗ₜ[K] 𝒞 k) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [TensorProduct.tmul_sum]
          simp_rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      _ = ∑ i ∈ s, ∑ k ∈ I, (𝒞.repr (c i)) k • (ℬ i ⊗ₜ[K] 𝒞 k) := by
          refine Finset.sum_congr rfl fun j h => ?_
          apply Finset.sum_subset
          · intro i hi
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_biUnion, I] at hi ⊢
            exact ⟨_, h, hi⟩
          · intro i hi1 hi2
            simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not, smul_eq_zero]
              at hi1 hi2 ⊢
            simp only [hi2, zero_smul]
      _ = ∑ ij ∈ s ×ˢ I, (𝒞.repr (c ij.1)) ij.2 • (ℬ ij.1 ⊗ₜ[K] 𝒞 ij.2) := by
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
