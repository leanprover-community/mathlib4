/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.IsTensorProduct

/-!

# Tensor Product of (multivariate) polynomial rings

Let `Semiring R`, `Algebra R S` and `Module R N`.

* `MvPolynomial.rTensor` gives the linear equivalence
  `MvPolynomial σ S ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ (S ⊗[R] N)` characterized,
  for `p : MvPolynomial σ S`, `n : N` and `d : σ →₀ ℕ`, by
  `rTensor (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n`
* `MvPolynomial.scalarRTensor` gives the linear equivalence
  `MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N`
  such that `MvPolynomial.scalarRTensor (p ⊗ₜ[R] n) d = coeff d p • n`
  for `p : MvPolynomial σ R`, `n : N` and `d : σ →₀ ℕ`, by

* `MvPolynomial.rTensorAlgHom`, the algebra morphism from the tensor product
  of a polynomial algebra by an algebra to a polynomial algebra
* `MvPolynomial.rTensorAlgEquiv`, `MvPolynomial.scalarRTensorAlgEquiv`,
  the tensor product of a polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra

## TODO :
* `MvPolynomial.rTensor` could be phrased in terms of `AddMonoidAlgebra`, and
  `MvPolynomial.rTensor` then has `smul` by the polynomial algebra.
* `MvPolynomial.rTensorAlgHom` and `MvPolynomial.scalarRTensorAlgEquiv`
  are morphisms for the algebra structure by `MvPolynomial σ R`.
-/

@[expose] public section


universe u v

noncomputable section

namespace MvPolynomial

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {N : Type v} [CommSemiring R]

variable {σ ι : Type*}

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Algebra

variable [CommSemiring N] [Algebra R N]

/-- The algebra morphism from a tensor product of a polynomial algebra
  by an algebra to a polynomial algebra -/
noncomputable def rTensorAlgEquiv : S ⊗[R] MvPolynomial σ N ≃ₐ[S] MvPolynomial σ (S ⊗[R] N) :=
  AddMonoidAlgebra.tensorEquiv R _ _

@[simp]
lemma coeff_rTensorAlgEquiv_tmul (s : S) (p : MvPolynomial σ N) (d : σ →₀ ℕ) :
    coeff d (rTensorAlgEquiv (s ⊗ₜ[R] p)) = s ⊗ₜ[R] coeff d p := by
  simp [rTensorAlgEquiv, coeff, MvPolynomial, ← tmul_eq_smul_one_tmul]

lemma coeff_rTensorAlgEquiv_monomial_tmul [DecidableEq σ] (e : σ →₀ ℕ) (s : S) (n : N)
    (d : σ →₀ ℕ) :
    coeff d (rTensorAlgEquiv (s ⊗ₜ[R] monomial e n)) = if e = d then s ⊗ₜ[R] n else 0 := by
  simp [tmul_ite]

/-- The tensor product of the polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra with
  coefficients in that algebra -/
noncomputable def scalarRTensorAlgEquiv : N ⊗[R] MvPolynomial σ R ≃ₐ[N] MvPolynomial σ N :=
  AddMonoidAlgebra.scalarTensorEquiv R N

variable (R)
variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- Tensoring `MvPolynomial σ R` on the left by an `R`-algebra `A` is algebraically
equivalent to `MvPolynomial σ A`. -/
noncomputable def algebraTensorAlgEquiv :
    A ⊗[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A := AlgEquiv.ofAlgHom
  (Algebra.TensorProduct.lift
    (Algebra.ofId A (MvPolynomial σ A))
    (MvPolynomial.mapAlgHom <| Algebra.ofId R A) (fun _ _ ↦ Commute.all _ _))
  (aeval (fun s ↦ 1 ⊗ₜ X s))
  (by ext s; simp)
  (by ext s; simp)

@[simp]
lemma algebraTensorAlgEquiv_tmul (a : A) (p : MvPolynomial σ R) :
    algebraTensorAlgEquiv R A (a ⊗ₜ p) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [algebraTensorAlgEquiv, Algebra.smul_def]
  rfl

@[simp]
lemma algebraTensorAlgEquiv_symm_X (s : σ) :
    (algebraTensorAlgEquiv R A).symm (X s) = 1 ⊗ₜ X s := by
  simp [algebraTensorAlgEquiv]

@[simp]
lemma algebraTensorAlgEquiv_symm_monomial (m : σ →₀ ℕ) (a : A) :
    (algebraTensorAlgEquiv R A).symm (monomial m a) = a ⊗ₜ monomial m 1 := by
  apply @Finsupp.induction σ ℕ _ _ m
  · simp [algebraTensorAlgEquiv]
  · intro i n f _ _ hfa
    simp only [algebraTensorAlgEquiv, AlgEquiv.ofAlgHom_symm_apply] at hfa ⊢
    simp only [add_comm, monomial_add_single, map_mul, map_pow, aeval_X,
      Algebra.TensorProduct.tmul_pow, one_pow, hfa]
    nth_rw 2 [← mul_one a]
    rw [Algebra.TensorProduct.tmul_mul_tmul]

@[simp]
lemma algebraTensorAlgEquiv_symm_comp_aeval :
    (((algebraTensorAlgEquiv (σ := σ) R A).symm.restrictScalars R) :
        MvPolynomial σ A →ₐ[R] A ⊗[R] MvPolynomial σ R).comp
      (MvPolynomial.mapAlgHom (R := R) (S₁ := R) (S₂ := A) (Algebra.ofId R A)) =
      Algebra.TensorProduct.includeRight := by
  ext
  simp

@[simp]
lemma algebraTensorAlgEquiv_symm_map (x : MvPolynomial σ R) :
    (algebraTensorAlgEquiv R A).symm (map (algebraMap R A) x) = 1 ⊗ₜ x :=
  DFunLike.congr_fun (algebraTensorAlgEquiv_symm_comp_aeval R A) x

lemma aeval_one_tmul (f : σ → S) (p : MvPolynomial σ R) :
    (aeval fun x ↦ (1 ⊗ₜ[R] f x : N ⊗[R] S)) p = 1 ⊗ₜ[R] (aeval f) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, Algebra.TensorProduct.algebraMap_apply]
    rw [← mul_one ((algebraMap R N) a), ← Algebra.smul_def, smul_tmul, Algebra.smul_def, mul_one]
  | add p q hp hq => simp [hp, hq, tmul_add]
  | mul_X p i h => simp [h]

variable (S σ ι) in
/-- `S[X] ⊗[R] R[Y] ≃ S[X, Y]` -/
def tensorEquivSum :
    MvPolynomial σ S ⊗[R] MvPolynomial ι R ≃ₐ[S] MvPolynomial (σ ⊕ ι) S :=
  ((algebraTensorAlgEquiv _ _).restrictScalars _).trans
    ((sumAlgEquiv _ _ _).symm.trans (renameEquiv _ (.sumComm ι σ)))

variable {R}

attribute [local simp] Algebra.smul_def

@[simp] lemma tensorEquivSum_X_tmul_one (i) :
    tensorEquivSum R σ ι S (.X i ⊗ₜ 1) = .X (.inl i) := by simp [tensorEquivSum]

@[simp] lemma tensorEquivSum_C_tmul_one (r) :
    tensorEquivSum R σ ι S (.C r ⊗ₜ 1) = .C r := by simp [tensorEquivSum]

@[simp] lemma tensorEquivSum_one_tmul_X (i) :
    tensorEquivSum R σ ι S (1 ⊗ₜ .X i) = .X (.inr i) := by simp [tensorEquivSum]

@[simp] lemma tensorEquivSum_one_tmul_C (r) :
    tensorEquivSum R σ ι S (1 ⊗ₜ .C r) = .C (algebraMap R S r) := by simp [tensorEquivSum]

@[simp] lemma tensorEquivSum_C_tmul_C (r : R) (s : S) :
    tensorEquivSum R σ ι S (.C s ⊗ₜ .C r) = .C (r • s) := by simp [tensorEquivSum, mul_comm (C s)]

@[simp] lemma tensorEquivSum_X_tmul_X (i j) :
    tensorEquivSum R σ ι S (.X i ⊗ₜ .X j) = .X (.inl i) * .X (.inr j) := by simp [tensorEquivSum]

section Pushout

attribute [local instance] algebraMvPolynomial

instance : Algebra.IsPushout R S (MvPolynomial σ R) (MvPolynomial σ S) :=
  AddMonoidAlgebra.instIsPushout

instance : Algebra.IsPushout R (MvPolynomial σ R) S (MvPolynomial σ S) := .symm inferInstance

end Pushout

end Algebra

end MvPolynomial

end
