/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ

/-!
# Characteristic polynomials of linear families of endomorphisms

The coefficients of the characteristic polynomials of a a linear family of endomorphisms
are homogeneous polynomials in the parameters.
This result is used in Lie theory
to establish the existence of regular elements and Cartan subalgebras,
and ultimately a well-defined notion of rank for Lie algebras.

In this file we prove this result about characteristic polynomials.
Let `L` and `M` be modules over a nontrivial commutative ring `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L`, indexed by `ι`.
Then we define a multivariate polynomial with variables indexed by `ι`
that evaluates on elements `x` of `L` to the characteristic polynomial of `φ x`.

## Main declarations

* `Matrix.toMvPolynomial M i`: the family of multivariate polynomials that evaluates on `c : n → R`
  to the dot product of the `i`-th row of `M` with `c`.
* `LinearMap.toMvPolynomial b₁ b₂ f`: a version of `Matrix.toMvPolynomial` for linear maps `f`
  with respect to bases `b₁` and `b₂` of the domain and codomain.
`Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`.
* `LinearMap.polyCharpoly`: the multivariate polynomial that evaluates on elements `x` of `L`
  to the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_map`: the evaluation of `polyCharpoly` on elements `x` of `L`
  is the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_coeff_isHomogeneous`: the coefficients of `polyCharpoly`
  are homogeneous polynomials in the parameters.

-/

open scoped BigOperators Matrix

section Basis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

-- move to Mathlib.RingTheory.TensorProduct.Basic
open Algebra.TensorProduct LinearMap in
lemma Basis.baseChange_end (A : Type*) [CommRing A] [Algebra R A] (b : Basis ι R M) (ij : ι × ι) :
    baseChange A (b.end ij) = (basis A b).end ij := by
  apply (basis A b).ext
  intro k
  conv_lhs => simp only [basis_apply, baseChange_tmul]
  simp_rw [end_apply_apply, basis_apply]
  split <;> simp only [TensorProduct.tmul_zero]

end Basis

namespace Matrix

variable {m n o R S : Type*}
variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

open MvPolynomial

/-- Let `M` be an `(m × n)`-matrix over `R`.
Then `Matrix.toMvPolynomial M` is the family (indexed by `i : m`)
of multivariate polynomials in `n` variables over `R` that evaluates on `c : n → R`
to the dot product of the `i`-th row of `M` with `c`:
`Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`. -/
noncomputable
def toMvPolynomial (M : Matrix m n R) (i : m) : MvPolynomial n R :=
  ∑ j, monomial (.single j 1) (M i j)

lemma toMvPolynomial_eval_eq_apply (M : Matrix m n R) (i : m) (c : n → R) :
    eval c (M.toMvPolynomial i) = (M *ᵥ c) i := by
  simp only [toMvPolynomial, map_sum, eval_monomial, pow_zero, Finsupp.prod_single_index, pow_one,
    mulVec, dotProduct]

lemma toMvPolynomial_map (f : R →+* S) (M : Matrix m n R) (i : m) :
    (M.map f).toMvPolynomial i = MvPolynomial.map f (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, map_apply, map_sum, map_monomial]

lemma toMvPolynomial_isHomogeneous (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  rintro j -
  apply MvPolynomial.isHomogeneous_monomial _ _ _
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same]

lemma toMvPolynomial_totalDegree_le (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).totalDegree ≤ 1 := by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le

@[simp]
lemma toMvPolynomial_constantCoeff (M : Matrix m n R) (i : m) :
    constantCoeff (M.toMvPolynomial i) = 0 := by
  simp only [toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, _root_.map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

@[simp]
lemma toMvPolynomial_zero (i : m) : (0 : Matrix m n R).toMvPolynomial i = 0 := by
  simp only [toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero]

lemma toMvPolynomial_add (M N : Matrix m n R) (i : m) :
    (M + N).toMvPolynomial i = M.toMvPolynomial i + N.toMvPolynomial i := by
  simp only [toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib]

lemma toMvPolynomial_mul (M : Matrix m n R) (N : Matrix n o R) (i : m) :
    (M * N).toMvPolynomial i = bind₁ N.toMvPolynomial (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, mul_apply, map_sum, Finset.sum_comm (γ := o), bind₁, aeval,
    AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, algebraMap_apply, Algebra.id.map_eq_id,
    RingHom.id_apply, C_apply, pow_zero, Finsupp.prod_single_index, pow_one, Finset.mul_sum,
    monomial_mul, zero_add]

end Matrix

namespace LinearMap

variable {R M₁ M₂ M₃ ι₁ ι₂ ι₃ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]
variable [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) (b₃ : Basis ι₃ R M₃)

open MvPolynomial

/-- Let `f : M₁ →ₗ[R] M₂` be an `R`-linear map
between modules `M₁` and `M₂` with bases `b₁` and `b₂` respectively.
Then `LinearMap.toMvPolynomial b₁ b₂ f` is the family of multivariate polynomials over `R`
that evaluates on an element `x` of `M₁` (represented on the basis `b₁`)
to the element `f x` of `M₂` (represented on the basis `b₂`). -/
noncomputable
def toMvPolynomial (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    MvPolynomial ι₁ R :=
  (toMatrix b₁ b₂ f).toMvPolynomial i

lemma toMvPolynomial_eval_eq_apply (f : M₁ →ₗ[R] M₂) (i : ι₂) (c : ι₁ →₀ R) :
    eval c (f.toMvPolynomial b₁ b₂ i) = b₂.repr (f (b₁.repr.symm c)) i := by
  rw [toMvPolynomial, Matrix.toMvPolynomial_eval_eq_apply,
    ← LinearMap.toMatrix_mulVec_repr b₁ b₂, LinearEquiv.apply_symm_apply]

open Algebra.TensorProduct in
lemma toMvPolynomial_baseChange (f : M₁ →ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRing A] [Algebra R A] :
    (f.baseChange A).toMvPolynomial (basis A b₁) (basis A b₂) i =
      MvPolynomial.map (algebraMap R A) (f.toMvPolynomial b₁ b₂ i) := by
  simp only [toMvPolynomial, toMatrix_baseChange, Matrix.toMvPolynomial_map]

lemma toMvPolynomial_isHomogeneous (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).IsHomogeneous 1 :=
  Matrix.toMvPolynomial_isHomogeneous _ _

lemma toMvPolynomial_totalDegree_le (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).totalDegree ≤ 1 :=
  Matrix.toMvPolynomial_totalDegree_le _ _

@[simp]
lemma toMvPolynomial_constantCoeff (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    constantCoeff (f.toMvPolynomial b₁ b₂ i) = 0 :=
  Matrix.toMvPolynomial_constantCoeff _ _

@[simp]
lemma toMvPolynomial_zero (i : ι₂) : (0 : M₁ →ₗ[R] M₂).toMvPolynomial b₁ b₂ i = 0 := by
  simp only [toMvPolynomial, map_zero, Matrix.toMvPolynomial_zero]

lemma toMvPolynomial_add (f g : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f + g).toMvPolynomial b₁ b₂ i = f.toMvPolynomial b₁ b₂ i + g.toMvPolynomial b₁ b₂ i := by
  simp only [toMvPolynomial, map_add, Matrix.toMvPolynomial_add]

lemma toMvPolynomial_comp (g : M₂ →ₗ[R] M₃) (f : M₁ →ₗ[R] M₂) (i : ι₃) :
    (g ∘ₗ f).toMvPolynomial b₁ b₃ i =
      bind₁ (f.toMvPolynomial b₁ b₂) (g.toMvPolynomial b₂ b₃ i) := by
  simp only [toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

end LinearMap

variable {R L M n ι ιM : Type*}

section LinearAlgebra

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable (φ : L →ₗ[R] Module.End R M)
variable [Fintype ι] [Fintype ιM] [DecidableEq ι]

namespace LinearMap

section basic

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

open Matrix

/-- Let `L` and `M` be modules over `R`, and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpoly φ b bₘ` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`.

This definition does not depend on the choice of `bₘ`
(see `LinearMap.polyCharpoly_basisIndep`). -/
noncomputable
def polyCharpoly : Polynomial (MvPolynomial ι R) :=
  (charpoly.univ R ιM).map <| MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)

lemma polyCharpoly_monic : (polyCharpoly φ b bₘ).Monic :=
  (charpoly.univ_monic R ιM).map _

lemma polyCharpoly_ne_zero [Nontrivial R] : (polyCharpoly φ b bₘ) ≠ 0 :=
  (polyCharpoly_monic _ _ _).ne_zero

@[simp]
lemma polyCharpoly_natDegree [Nontrivial R] : (polyCharpoly φ b bₘ).natDegree = Fintype.card ιM := by
  rw [polyCharpoly, (charpoly.univ_monic _ _).natDegree_map, charpoly.univ_natDegree]

lemma polyCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = Fintype.card ιM) :
    ((polyCharpoly φ b bₘ).coeff i).IsHomogeneous j := by
  rw [polyCharpoly, Polynomial.coeff_map, ← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r ↦ MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous _ _ _

open Algebra.TensorProduct MvPolynomial in
lemma polyCharpoly_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpoly (TensorProductEndₗ _ _ _ ∘ₗ φ.baseChange A) (basis A b) (basis A bₘ) =
      (polyCharpoly φ b bₘ).map (MvPolynomial.map (algebraMap R A)) := by
  simp only [polyCharpoly]
  rw [← charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_X, bind₁_X_right]
    classical
    rw [toMvPolynomial_comp _ (basis A (Basis.end bₘ)), ← toMvPolynomial_baseChange]
    suffices toMvPolynomial (basis A bₘ.end) (basis A bₘ).end (TensorProductEndₗ R A M) ij = X ij by
      rw [this, bind₁_X_right]
    simp only [toMvPolynomial, Matrix.toMvPolynomial]
    suffices ∀ kl,
      (toMatrix (basis A (Basis.end bₘ)) (Basis.end (basis A bₘ))) (TensorProductEndₗ R A M) ij kl =
      if kl = ij then 1 else 0 by
      rw [Finset.sum_eq_single ij]
      · rw [this, if_pos rfl, X]
      · rintro kl - H
        rw [this, if_neg H, map_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    intro kl
    rw [toMatrix_apply, TensorProductEndₗ, TensorProduct.AlgebraTensorModule.lift_apply,
      basis_apply, TensorProduct.lift.tmul, coe_restrictScalars]
    dsimp only [coe_mk, AddHom.coe_mk, smul_apply, baseChangeHom_apply]
    rw [one_smul, Basis.baseChange_end, Basis.repr_self_apply]

open LinearMap in
lemma polyCharpoly_map_eq_toMatrix_charpoly (x : L) :
    (polyCharpoly φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (toMatrix bₘ bₘ (φ x)).charpoly := by
  erw [polyCharpoly, Polynomial.map_map, MvPolynomial.comp_eval₂Hom, charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply, Function.curry_apply, toMvPolynomial_eval_eq_apply, LinearEquiv.symm_apply_apply]
  rfl

lemma polyCharpoly_map_eq_charpoly [Module.Finite R M] [Module.Free R M]
    (x : L) :
    (polyCharpoly φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  nontriviality R
  rw [polyCharpoly_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

lemma polyCharpoly_map_eval [Module.Finite R M] [Module.Free R M]
    (x : ι → R) :
    (polyCharpoly φ b bₘ).map (MvPolynomial.eval x) =
      (φ (b.repr.symm (Finsupp.equivFunOnFinite.symm x))).charpoly := by
  simp only [← polyCharpoly_map_eq_charpoly φ b bₘ, LinearEquiv.apply_symm_apply,
    Finsupp.equivFunOnFinite, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]

open Algebra.TensorProduct TensorProduct in
lemma polyCharpoly_map_aeval
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite A (A ⊗[R] M)] [Module.Free A (A ⊗[R] M)]
    (x : ι → A) :
    (polyCharpoly φ b bₘ).map (MvPolynomial.aeval x).toRingHom =
      LinearMap.charpoly ((TensorProductEndₗ R A M).comp (baseChange A φ)
        ((basis A b).repr.symm (Finsupp.equivFunOnFinite.symm x))) := by
  rw [← polyCharpoly_map_eval (TensorProductEndₗ R A M ∘ₗ baseChange A φ) _ (basis A bₘ),
    polyCharpoly_baseChange, Polynomial.map_map]
  congr
  exact DFunLike.ext _ _ fun f ↦ (MvPolynomial.eval_map (algebraMap R A) x f).symm

open Algebra.TensorProduct MvPolynomial in
lemma polyCharpoly_basisIndep (bₘ' : Basis ιM R M) :
    polyCharpoly φ b bₘ = polyCharpoly φ b bₘ' := by
  let f : Polynomial (MvPolynomial ι R) → Polynomial (MvPolynomial ι R) :=
    Polynomial.map (MvPolynomial.aeval X).toRingHom
  have hf : Function.Injective f := by
    simp only [f, aeval_X_left, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, Polynomial.map_id]
    exact Polynomial.map_injective (RingHom.id _) Function.injective_id
  apply hf
  dsimp only
  let _h1 : Module.Finite (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Finite.of_basis (basis (MvPolynomial ι R) bₘ)
  let _h2 : Module.Free (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Free.of_basis (basis (MvPolynomial ι R) bₘ)
  simp only [f, polyCharpoly_map_aeval, polyCharpoly_map_aeval]

open LinearMap in
lemma polyCharpoly_eval_eq_toMatrix_charpoly_coeff (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpoly φ b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← polyCharpoly_map_eq_toMatrix_charpoly φ b bₘ x]

end basic

section module

variable [DecidableEq ιM] [Nontrivial R] [Module.Finite R M] [Module.Free R M]
variable (b : Basis ι R L) (bₘ : Basis ιM R M) (x : L)

@[simp]
lemma polyCharpoly_map :
    (polyCharpoly φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  rw [polyCharpoly_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

@[simp]
lemma polyCharpoly_eval (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpoly φ b bₘ).coeff i) = (φ x).charpoly.coeff i := by
  rw [polyCharpoly_eval_eq_toMatrix_charpoly_coeff, LinearMap.charpoly_toMatrix]

end module

end LinearMap

end LinearAlgebra
