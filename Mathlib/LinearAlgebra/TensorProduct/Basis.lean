/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FinsuppVectorSpace

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

section

variable (ℬ : Basis ι R M) (𝒞 : Basis κ R N) (x : M ⊗[R] N)

/-- Elements in `M ⊗ N` can be represented by sum of elements in `M` tensor elements of basis of
`N`. -/
lemma TensorProduct.eq_repr_basis_right :
    ∃ b : κ →₀ M, b.sum (fun i m ↦ m ⊗ₜ 𝒞 i) = x := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul m n =>
    use (𝒞.repr n).mapRange (· • m) (by simp)
    simp only [Finsupp.mapRange, zero_tmul, implies_true, Finsupp.onFinset_sum, Function.comp_apply,
      smul_tmul]
    rw [← tmul_sum]
    congr
    conv_rhs => rw [← Basis.linearCombination_repr 𝒞 n]
    rfl
  | add x y hx hy =>
    rcases hx with ⟨x, rfl⟩
    rcases hy with ⟨y, rfl⟩
    exact ⟨x + y, Finsupp.sum_add_index (by simp) fun _ _ => by simp [add_tmul]⟩

/-- Elements in `M ⊗ N` can be represented by sum of elements of basis of `M` tensor elements of
  `N`.-/
lemma TensorProduct.eq_repr_basis_left :
    ∃ (c : ι →₀ N), (c.sum fun i n ↦ ℬ i ⊗ₜ n) = x := by
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right ℬ (TensorProduct.comm R M N x)
  exact ⟨c, (TensorProduct.comm R M N).injective <| by simp [Finsupp.sum, ← hc]⟩

lemma TensorProduct.sum_tmul_basis_left_injective :
    Function.Injective <| Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N) (ℬ i) := by
  classical
  intro b b' h
  refine (TensorProduct.congr ℬ.repr (LinearEquiv.refl R N) ≪≫ₗ
    (finsuppScalarLeft R N ι)).symm.injective ?_
  rw [← b.sum_single, ← b'.sum_single, Finsupp.sum, map_sum, Finsupp.sum, map_sum]
  simpa

lemma TensorProduct.sum_tmul_basis_left_eq_zero
    (b : ι →₀ N) (h : (b.sum fun i n ↦ ℬ i ⊗ₜ[R] n) = 0) : b = 0 :=
  TensorProduct.sum_tmul_basis_left_injective ℬ (a₁ := b) (a₂ := 0) (h.trans (by simp))

lemma TensorProduct.sum_tmul_basis_right_injective :
    Function.Injective <| Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N).flip (𝒞 i):= by
  classical
  intro b b' h
  refine (TensorProduct.congr (LinearEquiv.refl R M) 𝒞.repr ≪≫ₗ
    (finsuppScalarRight R M κ)).symm.injective ?_
  rw [← b.sum_single, ← b'.sum_single, Finsupp.sum, map_sum, Finsupp.sum, map_sum]
  simpa

lemma TensorProduct.sum_tmul_basis_right_eq_zero
    (b : κ →₀ M) (h : (b.sum fun i m ↦ m ⊗ₜ[R] 𝒞 i) = 0) : b = 0 :=
  TensorProduct.sum_tmul_basis_right_injective 𝒞 (a₁ := b) (a₂ := 0) (h.trans (by simp))


end

end CommSemiring

end
