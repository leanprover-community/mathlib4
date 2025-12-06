/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Bases and dimensionality of tensor products of modules

This file defines various bases on the tensor product of modules,
and shows that the tensor product of free modules is again free.
-/

@[expose] public section


noncomputable section

open LinearMap Module Set Submodule

open scoped TensorProduct

section CommSemiring

variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

namespace Module.Basis

/-- If `b : ι → M` and `c : κ → N` are bases then so is `fun i ↦ b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`. -/
def tensorProduct (b : Basis ι S M) (c : Basis κ R N) :
    Basis (ι × κ) S (M ⊗[R] N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.AlgebraTensorModule.congr b.repr c.repr).trans <|
        (finsuppTensorFinsupp R S _ _ _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.AlgebraTensorModule.rid R S S)).symm

@[simp]
theorem tensorProduct_apply (b : Basis ι S M) (c : Basis κ R N) (i : ι) (j : κ) :
    tensorProduct b c (i, j) = b i ⊗ₜ c j := by
  simp [tensorProduct]

theorem tensorProduct_apply' (b : Basis ι S M) (c : Basis κ R N) (i : ι × κ) :
    tensorProduct b c i = b i.1 ⊗ₜ c i.2 := by
  simp [tensorProduct]

@[simp]
theorem tensorProduct_repr_tmul_apply (b : Basis ι S M) (c : Basis κ R N) (m : M) (n : N)
    (i : ι) (j : κ) :
    (tensorProduct b c).repr (m ⊗ₜ n) (i, j) = c.repr n j • b.repr m i := by
  simp [tensorProduct]

variable (S : Type*) [Semiring S] [Algebra R S]

/-- The lift of an `R`-basis of `M` to an `S`-basis of the base change `S ⊗[R] M`. -/
noncomputable
def baseChange (b : Basis ι R M) : Basis ι S (S ⊗[R] M) :=
  (tensorProduct (.singleton Unit S) b).reindex (Equiv.punitProd ι)

@[simp]
lemma baseChange_repr_tmul (b : Basis ι R M) (x y i) :
    (b.baseChange S).repr (x ⊗ₜ y) i = b.repr y i • x := by
  simp [baseChange, tensorProduct]

@[simp]
lemma baseChange_apply (b : Basis ι R M) (i) :
    b.baseChange S i = 1 ⊗ₜ b i := by
  simp [baseChange, tensorProduct]

end Module.Basis

section

variable [DecidableEq ι] [DecidableEq κ]
variable (ℬ : Basis ι R M) (𝒞 : Basis κ R N) (x : M ⊗[R] N)

/--
If `{𝒞ᵢ}` is a basis for the module `N`, then every elements of `x ∈ M ⊗ N` can be uniquely written
as `∑ᵢ mᵢ ⊗ 𝒞ᵢ` for some `mᵢ ∈ M`.
-/
def TensorProduct.equivFinsuppOfBasisRight : M ⊗[R] N ≃ₗ[R] κ →₀ M :=
  LinearEquiv.lTensor M 𝒞.repr ≪≫ₗ TensorProduct.finsuppScalarRight R M κ

@[simp]
lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul (m : M) (n : N) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m ⊗ₜ n) =
    (𝒞.repr n).mapRange (· • m) (zero_smul _ _) := by
  ext; simp [equivFinsuppOfBasisRight]

lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply
    (m : M) (n : N) (i : κ) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m ⊗ₜ n) i =
    𝒞.repr n i • m := by
  simp only [equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply]

lemma TensorProduct.equivFinsuppOfBasisRight_symm :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.toLinearMap =
    Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N).flip (𝒞 i) := by
  ext; simp [equivFinsuppOfBasisRight]

@[simp]
lemma TensorProduct.equivFinsuppOfBasisRight_symm_apply (b : κ →₀ M) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm b = b.sum fun i m ↦ m ⊗ₜ 𝒞 i :=
  congr($(TensorProduct.equivFinsuppOfBasisRight_symm 𝒞) b)

omit [DecidableEq κ] in
lemma TensorProduct.sum_tmul_basis_right_injective :
    Function.Injective (Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N).flip (𝒞 i)) :=
  have := Classical.decEq κ
  (equivFinsuppOfBasisRight_symm (M := M) 𝒞).symm ▸
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective

omit [DecidableEq κ] in
lemma TensorProduct.sum_tmul_basis_right_eq_zero
    (b : κ →₀ M) (h : (b.sum fun i m ↦ m ⊗ₜ[R] 𝒞 i) = 0) : b = 0 :=
  have := Classical.decEq κ
  (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective (a₂ := 0) <| by simpa

/--
If `{ℬᵢ}` is a basis for the module `M`, then every elements of `x ∈ M ⊗ N` can be uniquely written
as `∑ᵢ ℬᵢ ⊗ nᵢ` for some `nᵢ ∈ N`.
-/
def TensorProduct.equivFinsuppOfBasisLeft : M ⊗[R] N ≃ₗ[R] ι →₀ N :=
  TensorProduct.comm R M N ≪≫ₗ TensorProduct.equivFinsuppOfBasisRight ℬ

@[simp]
lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul (m : M) (n : N) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m ⊗ₜ n) =
    (ℬ.repr m).mapRange (· • n) (zero_smul _ _) := by
  simp [equivFinsuppOfBasisLeft]

lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply
    (m : M) (n : N) (i : ι) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m ⊗ₜ n) i =
    ℬ.repr m i • n := by
  simp only [equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]

lemma TensorProduct.equivFinsuppOfBasisLeft_symm :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.toLinearMap =
    Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N) (ℬ i) := by
  ext; simp [equivFinsuppOfBasisLeft]

@[simp]
lemma TensorProduct.equivFinsuppOfBasisLeft_symm_apply (b : ι →₀ N) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm b = b.sum fun i n ↦ ℬ i ⊗ₜ n :=
  congr($(TensorProduct.equivFinsuppOfBasisLeft_symm ℬ) b)

omit [DecidableEq κ] in
/-- Elements in `M ⊗ N` can be represented by sum of elements in `M` tensor elements of basis of
`N`. -/
lemma TensorProduct.eq_repr_basis_right :
    ∃ b : κ →₀ M, b.sum (fun i m ↦ m ⊗ₜ 𝒞 i) = x := by
  classical simpa using (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.surjective x

omit [DecidableEq ι] in
/-- Elements in `M ⊗ N` can be represented by sum of elements of basis of `M` tensor elements of
  `N`. -/
lemma TensorProduct.eq_repr_basis_left :
    ∃ (c : ι →₀ N), (c.sum fun i n ↦ ℬ i ⊗ₜ n) = x := by
  classical obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.surjective x
  exact ⟨c, (TensorProduct.comm R M N).injective <| by simp [Finsupp.sum]⟩

omit [DecidableEq ι] in
/-- Given a finite basis `ℬ` for `M`, any tensor `x ∈ M ⊗ N` decomposes as `∑ᵢ ℬᵢ ⊗ₜ nᵢ`
where the `N`-component `nᵢ` is obtained by applying `ℬ.dualBasis i ⊗ id` to `x` and then
identifying `R ⊗ N ≃ N` via `lid`. -/
lemma TensorProduct.eq_sum_basis_tmul_dualBasis_apply [Fintype ι] :
    x = ∑ i, ℬ i ⊗ₜ[R] (TensorProduct.lid R N)
      ((TensorProduct.map (ℬ.coord i) LinearMap.id) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    conv_lhs => rw [← ℬ.sum_repr u, TensorProduct.sum_tmul]
    apply Finset.sum_congr rfl
    intro i _
    simp [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, TensorProduct.lid_tmul,
      Basis.coord_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  | add w1 w2 hw1 hw2 =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hw1, ← hw2]

omit [DecidableEq κ] in
/-- Given a finite basis `𝒞` for `N`, any tensor `x ∈ M ⊗ N` decomposes as `∑ⱼ mⱼ ⊗ₜ 𝒞ⱼ`
where the `M`-component `mⱼ` is obtained by applying `id ⊗ 𝒞.dualBasis j` to `x` and then
identifying `M ⊗ R ≃ M` via `rid`. -/
lemma TensorProduct.eq_sum_dualBasis_apply_tmul_basis [Fintype κ] :
    x = ∑ j, (TensorProduct.rid R M)
          ((TensorProduct.map LinearMap.id (𝒞.coord j)) x) ⊗ₜ[R] 𝒞 j := by
  apply (TensorProduct.comm R M N).injective
  rw [eq_sum_basis_tmul_dualBasis_apply 𝒞 (TensorProduct.comm R M N x)]
  simp only [map_sum, comm_tmul, map_comm, ← comm_trans_lid, LinearEquiv.trans_apply]

omit [DecidableEq ι] in
lemma TensorProduct.sum_tmul_basis_left_injective :
    Function.Injective (Finsupp.lsum R fun i ↦ (TensorProduct.mk R M N) (ℬ i)) :=
  have := Classical.decEq ι
  (equivFinsuppOfBasisLeft_symm (N := N) ℬ).symm ▸
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective

omit [DecidableEq ι] in
lemma TensorProduct.sum_tmul_basis_left_eq_zero
    (b : ι →₀ N) (h : (b.sum fun i n ↦ ℬ i ⊗ₜ[R] n) = 0) : b = 0 :=
  have := Classical.decEq ι
  (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective (a₂ := 0) <| by simpa

end

variable [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M] [Module.Free S M]
  [AddCommMonoid N] [Module R N] [Module.Free R N]
instance Module.Free.tensor : Module.Free S (M ⊗[R] N) :=
  let ⟨bM⟩ := exists_basis (R := S) (M := M)
  let ⟨bN⟩ := exists_basis (R := R) (M := N)
  of_basis (bM.2.tensorProduct bN.2)

end CommSemiring

end
